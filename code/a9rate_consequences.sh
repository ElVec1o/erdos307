#!/usr/bin/env bash
# Every place that would need revisiting if cor:a9rate stopped being conjectural.
#
# Hand-maintaining this list failed four consecutive review rounds.  The first mechanisation then
# failed too, LINE-oriented grep missing the abstract because the phrase "is stated as a
# \textsc{conjecture}" spans a line break -- reproducing by machine the exact omission it was written
# to prevent.  This version works on PARAGRAPHS with newlines flattened, so line breaks cannot hide a
# phrase, and it scans every file that carries the claim.
set -u
cd "$(dirname "$0")/.."

scan () {  # $1 = file, $2 = label for output
  awk -v RS='' -v FILE="$2" '
    { para = $0; gsub(/\n/, " ", para)
      if (para ~ /cor:a9rate/ ||
          para ~ /still conjectural/ || para ~ /remains conjectural/ ||
          para ~ /stated as a .textsc\{conjecture\}/ || para ~ /not proved/ ||
          para ~ /never supplied/ || para ~ /does not close/ ||
          para ~ /not available/ || para ~ /is open here/ ||
          para ~ /sketch of what a uniform version/ ||
          para ~ /would give, not a proof/ || para ~ /blocking .cor:a9rate/ ||
          para ~ /\(log N\)\^\{1\/4\}/ || para ~ /log N.\^.1\/4/) {
        n++
        why = ""
        if (para ~ /cor:a9rate/)                          why = why "names-label "
        if (para ~ /still conjectural|remains conjectural/) why = why "conjectural "
        if (para ~ /stated as a .textsc\{conjecture\}/)    why = why "STATED-AS-CONJECTURE "
        if (para ~ /not proved/)                          why = why "not-proved "
        if (para ~ /never supplied|does not close|not available/) why = why "input-unavailable "
        if (para ~ /is open here/)                        why = why "OPEN-QUESTION "
        if (para ~ /sketch of what a uniform version|would give, not a proof/) why = why "sketch-not-proof "
        printf "\n  [%s #%d]  (%s)\n  %.600s\n", FILE, n, why, para
      } }
  ' "$1"
}

echo "############ paper/erdos307.tex (source of truth) ############"
scan paper/erdos307.tex "tex"
echo
echo "############ README.md ############"
scan README.md "README"
echo
echo "############ code/README.md ############"
scan code/README.md "codeREADME"
echo
echo "############ derived builds ############"
echo "  paper/erdos307-core.tex and paper/erdos307-companion.tex are generated:"
echo "      cd paper && python3 ../code/split_paper.py     # must be run FROM paper/"
for f in paper/erdos307-core.tex paper/erdos307-companion.tex; do
  echo "      $(basename "$f"): $(grep -c 'cor:a9rate' "$f" | tr -d ' ') mentions"
done
echo
echo "  Deliberately over-inclusive: it prints paragraphs and lets a human judge."
