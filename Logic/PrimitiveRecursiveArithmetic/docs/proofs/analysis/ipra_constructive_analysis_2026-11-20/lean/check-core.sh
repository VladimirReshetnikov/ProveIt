#!/usr/bin/env bash
# Uses only the Lean standard library. Set LEAN to the desired compiler.
set -eu
cd "$(dirname "$0")"
cache_dir=$(mktemp -d)
trap 'rm -rf "$cache_dir"' EXIT
export LEAN_PATH="$cache_dir"
for module in Dialogue BitIntegral FiniteCube DepthMean Prefix Carry LeastPrefix Oscillation Entropy; do
  "${LEAN:-lean}" -o "$cache_dir/$module.olean" "$module.lean"
  echo "Checked $module"
done
