#!/usr/bin/env bash
# Every place that would need revisiting if cor:a9rate stopped being conjectural.
# Hand-maintaining this list failed four consecutive review rounds (wrong file for ssec:sieve, wrong
# lemma for the retraction paragraph, the abstract omitted, a "FIVE places" heading over a nine-item
# list).  It is a mechanical question, so it is mechanised.  Deliberately over-inclusive: it prints
# every mention with context and lets a human judge, rather than trying to be clever about phrasing.
set -u
cd "$(dirname "$0")/.."

echo "### 1. Every mention of cor:a9rate in the source, with context"
grep -n -B2 -A2 'cor:a9rate' paper/erdos307.tex | sed 's/^/  /'
echo
echo "### 2. Assertions of conjecturality NOT on a line naming cor:a9rate"
echo "    (the label may be several sentences away -- these need reading)"
grep -n -i -E 'still conjectural|remains conjectural|stated as a .textsc.conjecture|never supplied|not a proof|would give, not a proof|analytic input' paper/erdos307.tex \
  | grep -v 'cor:a9rate' | sed 's/^/  /'
echo
echo "### 3. README.md"
grep -n -i -E 'a9rate|conjectural|log N.\^.1/4|\(log N\)\^\{1/4\}' README.md | sed 's/^/  /'
echo
echo "### 4. Derived builds -- regenerate with code/split_paper.py, do not edit"
for f in paper/erdos307-core.tex paper/erdos307-companion.tex; do
  n=$(grep -c 'cor:a9rate' "$f" 2>/dev/null | tr -d ' ')
  echo "  $(basename "$f"): $n mentions of cor:a9rate"
done
