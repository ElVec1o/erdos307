#!/usr/bin/env bash
# install_hooks.sh -- install the tracked git hooks.  Hooks live outside the repository's object
# store, so they cannot be shipped directly; this copies them into .git/hooks.
set -euo pipefail
root="$(git rev-parse --show-toplevel)"
for h in "$root"/code/hooks/*; do
  n="$(basename "$h")"
  install -m 755 "$h" "$root/.git/hooks/$n"
  echo "installed .git/hooks/$n"
done
