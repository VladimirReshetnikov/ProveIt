#!/bin/sh
# Lean 4.32.0. LEAN=/path/to/lean sh build.sh is also supported.
set -eu
cd "$(dirname "$0")"
export LEAN_PATH="$PWD${LEAN_PATH:+:$LEAN_PATH}"
compiler="${LEAN:-lean}"
"$compiler" -o ReplayCore.olean ReplayCore.lean
"$compiler" -o ReplayBalls.olean ReplayBalls.lean
for source in ReplayPair*.lean; do
  "$compiler" -o "${source%.lean}.olean" "$source"
done
"$compiler" -o AllReplay.olean AllReplay.lean
