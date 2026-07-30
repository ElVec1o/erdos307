#!/usr/bin/env bash
# run_tier2_par.sh -- tier 2, parallel. Pairs are independent, so the sweep strides perfectly:
# worker j of K takes every pair with (pair % K) == j and keeps its OWN checkpoint and hit file.
# Verified as an exact partition: 3 striped workers reproduce the single-worker totals
# (57,237 m tested / 2,536,973 valid m' / 0 hits) on box 4 5 3 150 8 9.
#
#   run_tier2_par.sh start [K]   default K=5
#   run_tier2_par.sh status | stop
set -uo pipefail
D="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
BIN="$D/descended_hunt2"; SRC="$D/descended_hunt2.rs"
BOX="4 6 3 600 10 11"; RESUME=110      # pairs 0..110 already swept by the serial run
K_FILE="$D/tier2_par.k"

case "${1:-status}" in
  status)
    n=$(pgrep -f "descended_hunt2 4 6 3 600 10 11" | wc -l | tr -d ' ')
    echo "workers running: $n"
    tt=0; tv=0; th=0
    for f in "$D"/descended_hunt2.progress.*; do
      [ -f "$f" ] || continue
      echo "  $(basename "$f"): $(cat "$f")"
      tt=$((tt + $(sed -n 's/.*tested \([0-9]*\).*/\1/p' "$f")))
      tv=$((tv + $(sed -n "s/.*valid-m' \([0-9]*\).*/\1/p" "$f")))
      th=$((th + $(sed -n 's/.*hits \([0-9]*\).*/\1/p' "$f")))
    done
    echo "TOTAL since restart: tested $tt  closure-tests $tv  hits $th"
    for f in "$D"/descended_hunt2.out.*; do [ -s "$f" ] && { echo "HIT RECORDED in $f"; cat "$f"; }; done
    exit 0;;
  stop)
    pkill -f "descended_hunt2 4 6 3 600 10 11" && echo "stopped" || echo "not running"; exit 0;;
  start) ;;
  *) echo "usage: $0 start [K] | status | stop"; exit 1;;
esac

K="${2:-5}"
pgrep -f "descended_hunt2 4 6 3 600 10 11" >/dev/null && { echo "already running; refusing to double-start"; exit 1; }
[ -x "$BIN" ] && [ "$BIN" -nt "$SRC" ] || { echo "building..."; rustc -O -o "$BIN" "$SRC" || exit 1; }
echo "$K" > "$K_FILE"
for j in $(seq 0 $((K-1))); do
  ( cd "$D" && nohup "$BIN" $BOX $RESUME "$K" "$j" >> "$D/descended_hunt2.log.$j" 2>&1 & )
done
sleep 2
echo "started $K workers, box [$BOX], resuming from pair $RESUME"
pgrep -f "descended_hunt2 4 6 3 600 10 11" | wc -l | awk '{print "  confirmed running:",$1}'
