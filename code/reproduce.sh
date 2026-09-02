#!/usr/bin/env bash
# reproduce.sh -- single entry point regenerating everything the paper cites.
# Usage: bash code/reproduce.sh [quick|full]
#   quick (default): every check whose runtime is under about two minutes.
#   full:            adds the multi-hour enumerations, named at the end.
# Expected runtime: quick about 12 minutes; full is dominated by the sector and pair-sector runs.
set -uo pipefail
cd "$(dirname "$0")/.." || exit 1
MODE="${1:-quick}"
fail=0
run() { printf '\n=== %s\n' "$1"; shift; if ! "$@"; then echo "FAILED: $*"; fail=1; fi; }
# The sector enumerator checkpoints by item index into its working directory.  A checkpoint left by
# an earlier run makes a later run skip every item and report success having done nothing, so each
# run gets a clean scratch directory of its own.
SCRATCH="$(mktemp -d)"; trap 'rm -rf "$SCRATCH"' EXIT
runsector() { local msg="$1"; shift; rm -f "$SCRATCH"/k64_phase*; printf '\n=== %s\n' "$msg"
  if ! ( cd "$SCRATCH" && "$@" ); then echo "FAILED: $*"; fail=1; fi; }

echo "reproduce.sh mode=$MODE   toolchain:"
echo "  $(gp --version 2>&1 | head -1)"
echo "  $(rustc --version 2>/dev/null || echo 'rustc: not found')"
echo "  $(python3 --version)"
echo "  lean/mathlib v4.30.0 (see lean/lake-manifest.json)"

# 1. the cross-file consistency gate: page counts, coverage totals, sorry count, census
run "consistency gate" bash code/check_consistency.sh

# 2. symbolic and exact-rational identities behind the sector results
run "sector identities (general d)"            gp -q -f code/sector_general.gp
run "generalised terminal formula"             gp -q -f code/sector_kexclude.gp
run "alpha = d identity"                       gp -q -f code/alpha_is_d.gp
run "sector-42 exact case split"               gp -q -f code/sector42_k64.gp
run "Znam conditions on Bado's maximiser"      gp -q -f code/sector42_znam_violations.gp
run "T(R) != 2 parity"                         gp -q -f code/pairsector_parity.gp

# 3. the sector enumerations that are fast
if command -v rustc >/dev/null; then
  rustc -O -o /tmp/_skx code/sector_kexclude.rs 2>/dev/null
  runsector "d=42, omega(e)=64, phase 2 (regression: 166213 / 2495 / 0)" /tmp/_skx 42 41 64 2 4 197
  runsector "d=47058, omega(e)=54 excluded (2,850,564 sets)"        /tmp/_skx 47058 47057 54 1 4 300
  runsector "d=2214502422, omega(e)=70 excluded (11,646 sets)"      /tmp/_skx 2214502422 2214502421 70 1 4 112
fi

if [ "$MODE" = full ]; then
  runsector "d=42, omega(e)=64, phase 1 (3.7e10 sets, ~22 min on 9 threads)" /tmp/_skx 42 41 64 1 9 197
  echo "Not run even in full mode, and stated as such in the paper:"
  echo "  - the pair-sector rho stage (code/pairsector_factor.rs, hours)"
  echo "  - omega(e)=56 at d=47058 (4.4e11 sets)"
fi

printf '\n=== reproduce.sh finished with fail=%d\n' "$fail"
exit "$fail"
