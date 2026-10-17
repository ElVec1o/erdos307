#!/bin/bash
# Stage A, second implementation, over the 3,698 survivor bases. Low profile (nice 19, memory-guarded).
#   start / resume : ./run_stageA2.sh                (resumes from run/done.txt)
#   more cores     : echo 8 > run/threads            (re-read before every base; up to 10)
#   fewer / pause  : echo 0 > run/threads            (workers finish their base, then idle; or kill -STOP <pid>)
#   stop           : pkill -f stageA2                (loses at most the bases in progress)
cd "$(dirname "$0")"
[ -f run/threads ] || echo 2 > run/threads
exec ~/erdos307-runs/guard.sh 2500 nice -n 19 ./stageA2 survivors_bases.txt run 10 40
