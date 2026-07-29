#!/usr/bin/env bash
# run_tier2.sh — tier 2 of the descended-operator hunt: products in [1e10, 1e11].
#
# Tier 1 (run_descended.sh, box 4 6 3 600 9 10) is still sweeping and the machine is already
# oversubscribed, so this does NOT co-run: `chain` blocks until tier 1's pid exits, then starts.
# Everything else matches tier 1: detach, rebuild only on source change, refuse to double-start,
# refuse to resume a checkpoint written on a different box, auto-resume otherwise.
#
#   run_tier2.sh chain    wait for tier 1 to finish, then start tier 2   (the normal call)
#   run_tier2.sh start    start now regardless of tier 1
#   run_tier2.sh status | stop | fresh
set -uo pipefail
D="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
BIN="$D/descended_hunt2"; SRC="$D/descended_hunt2.rs"
PROG="$D/descended_hunt2.progress"; BOXF="$D/descended_hunt2.box"; LOG="$D/descended_hunt2.log"
PIDF="$D/descended_hunt2.pid"
BOX="4 6 3 600 10 11"

build(){ [ -x "$BIN" ] && [ "$BIN" -nt "$SRC" ] || { echo "building..."; rustc -O -o "$BIN" "$SRC" || exit 1; }; }
alive(){ [ -f "$PIDF" ] && kill -0 "$(cat "$PIDF")" 2>/dev/null; }

case "${1:-chain}" in
  status)
    if alive; then echo "RUNNING (pid $(cat "$PIDF"))"; else echo "not running"; fi
    [ -f "$PROG" ] && echo "checkpoint: $(cat "$PROG")"
    [ -f "$BOXF" ] && echo "checkpoint box: [$(cat "$BOXF")]"
    [ -f "$D/descended_hunt2.out" ] && echo "HITS RECORDED:" && cat "$D/descended_hunt2.out"
    exit 0;;
  stop)  alive && { kill "$(cat "$PIDF")"; echo "stopped"; } || echo "not running"; exit 0;;
  fresh) rm -f "$PROG" "$BOXF"; echo "checkpoint cleared";;
  chain|start) ;;
  *) echo "usage: $0 chain|start|status|stop|fresh"; exit 1;;
esac

alive && { echo "already running (pid $(cat "$PIDF")); refusing to double-start"; exit 1; }
build

# a checkpoint from a different box would resume into the wrong sweep
RESUME=0
if [ -f "$PROG" ]; then
  if [ -f "$BOXF" ] && [ "$(cat "$BOXF")" = "$BOX" ]; then
    RESUME=$(sed -n 's/.*resume_from \([0-9]*\).*/\1/p' "$PROG")
    echo "resuming from pair $RESUME"
  else
    echo "checkpoint box [$(cat "$BOXF" 2>/dev/null)] != [$BOX]; refusing to resume. Use 'fresh'."
    exit 1
  fi
fi
echo "$BOX" > "$BOXF"

nohup bash -c '
  if [ "'"${1:-chain}"'" = "chain" ]; then
    while pgrep -f "[d]escended_hunt " >/dev/null 2>&1 || pgrep -x "[d]escended_hunt" >/dev/null 2>&1; do sleep 60; done
    echo "tier 1 finished; starting tier 2 at $(date)"
  fi
  exec "'"$BIN"'" '"$BOX $RESUME"'
' >> "$LOG" 2>&1 &
echo $! > "$PIDF"
echo "tier 2 armed (pid $(cat "$PIDF")), box [$BOX], log $LOG"
[ "${1:-chain}" = "chain" ] && echo "  waiting for tier 1 to finish before it starts."
