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
  else printf "  FAIL  %-28s stated %s, actual %s\n" "$1" "$2" "$3"; fail=1; fi
}

pdf=$(pdfinfo paper/erdos307.pdf 2>/dev/null | awk '/Pages/{print $2}')
readme_pp=$(grep -o 'the note ([0-9]* pp' README.md | grep -o '[0-9]*')
chk "paper page count" "$readme_pp" "$pdf"

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
chk "coverage covered" "$stated" "$cov"
chk "coverage total" "$stated_tot" "$tot"

nd=$(grep -rn 'native_decide' lean/Erdos307/*.lean | grep -c ':= by')
chk "native_decide sites" "1" "$nd"

sry=$(grep -rn 'sorry' lean/Erdos307/*.lean | grep -v 'sorry`-free\|sorryAx' | wc -l | tr -d ' ')
chk "sorry count" "0" "$sry"

orph=$(git ls-files | grep -v '^\(paper\|lean\|code\|data\|certs\|hunt\)/' \
       | grep -v '^\(README.md\|LICENSE\|.gitignore\|CLAUDE.md\|RULES.md\)$' | wc -l | tr -d ' ')
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

echo
[ "$fail" -eq 0 ] && echo "CONSISTENT" || echo "DRIFT DETECTED -- fix before releasing"
exit $fail
