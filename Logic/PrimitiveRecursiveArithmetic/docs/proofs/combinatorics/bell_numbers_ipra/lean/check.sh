#!/usr/bin/env bash
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
out="${BELL_BUILD_DIR:-$here/build}"
lean_bin="${LEAN_BIN:-lean}"
mkdir -p "$out"
export LEAN_PATH="$out${LEAN_PATH:+:$LEAN_PATH}"
"$lean_bin" --version > "$out/lean-version.txt"
"$lean_bin" -o "$out/BellCore.olean" "$here/BellCore.lean" > "$out/BellCore.log" 2>&1
"$lean_bin" -o "$out/BellTargets.olean" "$here/BellTargets.lean" > "$out/BellTargets.log" 2>&1
"$lean_bin" -o "$out/Audit.olean" "$here/Audit.lean" > "$out/axioms.txt" 2>&1
if rg -n "sorryAx|declaration uses 'sorry'|error:" "$out"/*.log "$out/axioms.txt"; then
  exit 1
fi
cat "$out/lean-version.txt" "$out/axioms.txt"
