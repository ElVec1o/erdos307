#!/bin/bash
# check_consistency.sh -- guard against the drift class that three external audits kept finding.
#
# Every claim below is a NUMBER stated in one file and derivable from another. Each has drifted at
# least once: the page count, the coverage count, the native_decide site count, the orphan census.
# This script recomputes each from the artifact and compares. Run it before any release.
#
#   bash code/check_consistency.sh    # exits nonzero on any mismatch
set -u
cd "$(dirname "$0")/.."
fail=0
chk() { # name  expected  actual
  if [ "$2" = "$3" ]; then printf "  ok    %-28s %s\n" "$1" "$3"
  else printf "  FAIL  %-28s computed %s, but the file says %s\n" "$1" "$2" "$3"; fail=1; fi
}

core_pdf=$(pdfinfo paper/erdos307-core.pdf 2>/dev/null | awk '/Pages/{print $2}')
comp_pdf=$(pdfinfo paper/erdos307-companion.pdf 2>/dev/null | awk '/Pages/{print $2}')
readme_core=$(grep -o 'the paper ([0-9]* pp' README.md | grep -o '[0-9]*')
readme_comp=$(grep -o 'the companion ([0-9]* pp' README.md | grep -o '[0-9]*')
chk "core page count" "$readme_core" "$core_pdf"
chk "companion page count" "$readme_comp" "$comp_pdf"

# The derived documents are generated from erdos307.tex by code/split_paper.py. A result added to
# the source and not re-split is invisible to the page counts above, so the label sets are compared
# directly: every numbered result in the monolith must appear in exactly one derived document.
read split_drift < <(python3 -c "
import re
def labs(f):
    return set(re.findall(r'\\\\label\{((?:thm|prop|lem|cor|rem):[^}]+)\}', open(f).read()))
m = labs('paper/erdos307.tex')
d = labs('paper/erdos307-core.tex') | labs('paper/erdos307-companion.tex')
bad = sorted(m ^ d)
print(','.join(bad) if bad else 'none')
")
chk "split label parity" "none" "$split_drift"

read cov tot < <(python3 -c "
import re, glob
tex = open('paper/erdos307.tex').read()
pat = re.compile(r'\\\\begin\{(theorem|proposition|lemma|corollary)\}(?:\[((?:[^\[\]]|\[[^\]]*\])*)\])?\s*\\\\label\{([a-z:0-9]+)\}')
labels = {m[2] for m in pat.findall(tex)}
lean = set()
for f in glob.glob('lean/Erdos307/*.lean'):
    lean |= set(re.findall(r'\`([a-z]+:[a-z0-9]+)\`', open(f).read()))
print(len(labels & lean), len(labels))")
stated=$(grep -o '\*\*[0-9]* of [0-9]*\*\*' lean/COVERAGE.md | head -1 | grep -o '[0-9]*' | head -1)
stated_tot=$(grep -o '\*\*[0-9]* of [0-9]*\*\*' lean/COVERAGE.md | head -1 | grep -o '[0-9]*' | tail -1)
chk "coverage covered" "$cov" "$stated"
chk "coverage total" "$tot" "$stated_tot"

# README and COVERAGE.md each carry their own copy of the declaration/module counts. Both drifted
# once (README sat at 159/30 while the build was at 304/36), so both are recomputed here.
mods=$(ls lean/Erdos307/*.lean | wc -l | tr -d ' ')
decls=$(grep -c '^#print axioms' lean/Check.lean | tr -d ' ')
chk "Check.lean declarations" "$decls" "$(grep -oE '[0-9]+ declarations' README.md | grep -oE '[0-9]+' | sort -u | paste -sd, -)"
chk "README module count"     "$mods"  "$(grep -oE 'across all [0-9]+ modules' README.md | grep -oE '[0-9]+' | sort -u | paste -sd, -)"
chk "COVERAGE declarations"   "$decls" "$(grep -oE '\*\*[0-9]+ declarations' lean/COVERAGE.md | grep -oE '[0-9]+')"
chk "COVERAGE module count"   "$mods"  "$(grep -oE 'across all [0-9]+ modules' lean/COVERAGE.md | grep -oE '[0-9]+')"
chk "COVERAGE file count"     "$mods"  "$(grep -oE '\([0-9]+ files' lean/COVERAGE.md | grep -oE '[0-9]+')"

# paper/erdos307.pdf is tracked and shipped; it went stale once while the split PDFs were current.
stale=$([ paper/erdos307.tex -nt paper/erdos307.pdf ] && echo 1 || echo 0)
chk "full pdf freshness" "0" "$stale"

codeN=$(git ls-files code | wc -l | tr -d ' ')
chk "code/README file count" "$codeN" "$(grep -oE 'holds [0-9]+ tracked files' code/README.md | grep -oE '[0-9]+')"

err=$(grep -c '^! ' paper/erdos307-core.log paper/erdos307-companion.log 2>/dev/null | awk -F: '{s+=$2} END{print s+0}')
chk "latex errors" "0" "$err"

dup=$(grep -o '\\label{[^}]*}' paper/erdos307.tex | sort | uniq -d | wc -l | tr -d ' ')
chk "duplicate labels" "0" "$dup"

nd=$(grep -rn 'native_decide' lean/Erdos307/*.lean | grep -c ':= by')
chk "native_decide sites" "0" "$nd"

sry=$(grep -rn 'sorry' lean/Erdos307/*.lean | grep -v 'sorry`-free\|sorryAx' | wc -l | tr -d ' ')
chk "sorry count" "0" "$sry"

orph=$(git ls-files | grep -v '^\(paper\|lean\|code\|data\)/' \
       | grep -v '^\(README.md\|LICENSE\|.gitignore\|CLAUDE.md\|RULES.md\|CITATION.cff\)$' | wc -l | tr -d ' ')
chk "orphan files" "0" "$orph"

unanch=$(for f in lean/Erdos307/*.lean; do grep -q 'Paper:' "$f" || basename "$f"; done | wc -l | tr -d ' ')
chk "unanchored Lean files" "0" "$unanch"

leaked=$(git ls-files | grep -c '^private/')
chk "private/ files tracked" "0" "$leaked"

# Non-vacuity. `#print axioms` cannot see unsatisfiable hypotheses: a theorem with contradictory
# hypotheses proves everything and reports the three standard axioms. One did (see Vacuity.lean).
# lean/Vacuity.lean instantiates the exposed theorems at concrete models and discharges every
# hypothesis; if it compiles, those hypotheses are satisfiable.
if (cd lean && lake env lean Vacuity.lean) >/dev/null 2>&1; then
  printf "  ok    %-28s %s\n" "non-vacuity witnesses" "compile"
else
  printf "  FAIL  %-28s %s\n" "non-vacuity witnesses" "lean/Vacuity.lean does not compile"; fail=1
fi

# --- V4 Rule 11: README contract checks -------------------------------------------------
# The README is a derived document; a stale one blocks the push exactly like a wrong theorem number.
pver=$(grep -oE 'Version [0-9]+\.[0-9]+\.[0-9]+' paper/erdos307.tex | head -1 | grep -oE '[0-9.]+')
rver=$(grep -oE 'Version [0-9]+\.[0-9]+\.[0-9]+' README.md | head -1 | grep -oE '[0-9.]+')
cver=$(grep -oE '^version: [0-9.]+' CITATION.cff | grep -oE '[0-9.]+')
chk "README version = paper"   "$pver" "$rver"
chk "CITATION version = paper" "$pver" "$cver"
missing=0
for f in $(grep -oE '\((code|lean|paper|data|certs|hunt)/[A-Za-z0-9_./-]+\)' README.md | tr -d '()' | sort -u); do
  [ -e "$f" ] || { echo "  MISSING path in README: $f"; missing=$((missing+1)); }
done
chk "README paths exist"  "0" "$missing"
chk "reproduce.sh present" "1" "$([ -x code/reproduce.sh ] && echo 1 || echo 0)"

echo
[ "$fail" -eq 0 ] && echo "CONSISTENT" || echo "DRIFT DETECTED -- fix before releasing"
exit $fail
