#!/usr/bin/env bash
# run_descended.sh — launch the deep descended-operator hunt from ANYWHERE.
#
#   bash /Users/vico/Documents/elvec1o/ERDOS/307/erdos307-1.0/hunt/run_descended.sh
#
# Detaches (survives closing the terminal), rebuilds only if the source changed,
# and AUTO-RESUMES from the last checkpoint. Safe to run twice: it refuses to start
# a second copy while one is live.
#
#   status : bash run_descended.sh status
#   stop   : bash run_descended.sh stop
#   fresh  : bash run_descended.sh fresh    (ignore checkpoint, restart from 0)
#
# Override the box by appending args, e.g.:  bash run_descended.sh 4 6 3 1000 9 13
set -uo pipefail

HUNT="/Users/vico/Documents/elvec1o/ERDOS/307/erdos307-1.0/hunt"
BIN="$HUNT/descended_hunt"
SRC="$HUNT/descended_hunt.rs"
PROG="$HUNT/descended_hunt.progress"
OUT="$HUNT/descended_hunt.out"
LOG="$HUNT/descended_deep.log"
BOXF="$HUNT/descended_hunt.box"
DEFAULT_BOX=(4 6 3 600 9 12)   # omega 4..6, odd primes<=600, product 1e9..1e12

cd "$HUNT" || { echo "cannot cd to $HUNT"; exit 1; }

status() {
  if pgrep -f "descended_hunt " >/dev/null 2>&1 || pgrep -x descended_hunt >/dev/null 2>&1; then
    echo "RUNNING (pid $(pgrep -f descended_hunt | head -1))"
  else
    echo "not running"
  fi
  if [ -f "$PROG" ]; then
    line=$(cat "$PROG")
    echo "checkpoint: $line"
    [ -f "$HUNT/descended_hunt.box" ] && echo "checkpoint box: [$(cat "$HUNT/descended_hunt.box")]"
    ts=$(echo "$line" | awk '{for(i=1;i<=NF;i++) if($i=="unix") print $(i+1)}')
    if [ -n "${ts:-}" ]; then
      age=$(( $(date +%s) - ts ))
      echo "checkpoint age: ${age}s $([ "$age" -gt 120 ] && echo '(STALE — process likely dead)')"
    fi
  else
    echo "checkpoint: none yet"
  fi
  if [ -s "$OUT" ]; then
    echo "!!! HITS FOUND — see $OUT"; tail -20 "$OUT"
  else
    echo "hits: none so far"
  fi
}

case "${1:-run}" in
  status) status; exit 0 ;;
  stop)   pkill -f descended_hunt && echo "stopped (checkpoint kept; rerun to resume)" || echo "nothing running"; exit 0 ;;
  fresh)  rm -f "$PROG" "$HUNT/descended_hunt.box"; shift; echo "checkpoint cleared" ;;
esac

# refuse to double-start
if pgrep -x descended_hunt >/dev/null 2>&1; then
  echo "already running — showing status instead:"; status; exit 0
fi

# build only if the source is newer than the binary
if [ ! -x "$BIN" ] || [ "$SRC" -nt "$BIN" ]; then
  echo "building..."
  rustc -O -o "$BIN" "$SRC" || { echo "BUILD FAILED"; exit 1; }
fi

# box: user args override the default
if [ "$#" -ge 6 ]; then BOX=("$@"); else BOX=("${DEFAULT_BOX[@]}"); fi

# auto-resume, but ONLY if the checkpoint belongs to the same box.
# (A checkpoint index is meaningless against a different prime pool: resuming across
#  boxes would silently skip supports. Guard on an exact box match.)
RESUME=0
PREV_BOX=""
[ -f "$BOXF" ] && PREV_BOX=$(cat "$BOXF")
if [ -f "$PROG" ]; then
  if [ "$PREV_BOX" != "${BOX[*]}" ]; then
    echo "checkpoint is for box [${PREV_BOX:-unknown}], you asked for [${BOX[*]}] — starting from 0 (not resuming across boxes)"
  elif grep -q "STATUS COMPLETE" "$PROG"; then
    echo "this exact box already COMPLETED; starting from 0 (widen the box to make new progress)"
  else
    RESUME=$(awk '{for(i=1;i<=NF;i++) if($i=="resume_from") print $(i+1)}' "$PROG")
    RESUME=${RESUME:-0}
    [ "$RESUME" -gt 0 ] && echo "auto-resuming box [${BOX[*]}] from outer index $RESUME"
  fi
fi
printf '%s' "${BOX[*]}" > "$BOXF"

echo "launching: descended_hunt ${BOX[*]} $RESUME"
nohup "$BIN" "${BOX[@]}" "$RESUME" >>"$LOG" 2>&1 </dev/null &
disown
sleep 2
echo "detached (pid $!). safe to close this terminal."
echo "  status : bash $HUNT/run_descended.sh status"
echo "  live   : tail -f $LOG"
echo "  hits   : $OUT   (appended the moment one is found)"
