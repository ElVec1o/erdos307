#!/usr/bin/env bash
# Cut a release ONLY if the consistency gate passes.  Twice in one day a release went out on a
# failing gate because `check_consistency.sh | grep` swallowed the exit status.  This script does not.
set -euo pipefail
cd "$(dirname "$0")/.."
ver="${1:?usage: release.sh X.Y.Z <notes-file>}"; notes="${2:?usage: release.sh X.Y.Z <notes-file>}"
out=$(bash code/check_consistency.sh 2>&1)
if ! grep -q '^CONSISTENT$' <<<"$out"; then echo "$out" | grep -E 'FAIL|DRIFT'; echo "REFUSED: gate not consistent"; exit 1; fi
[ -z "$(git status --porcelain)" ] || { echo "REFUSED: working tree not clean"; exit 1; }
grep -q "^version: $ver$" CITATION.cff || { echo "REFUSED: CITATION.cff is not at $ver"; exit 1; }
git tag -a "v$ver" -F "$notes" && git push -q origin "v$ver"
gh release create "v$ver" --title "v$ver" --notes-file "$notes" | tail -1
