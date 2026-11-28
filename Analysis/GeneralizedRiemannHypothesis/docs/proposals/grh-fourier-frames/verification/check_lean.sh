#!/usr/bin/env bash
# Argument is a prepared checkout of the pinned Mathlib, or the GRH Lake project.
set -euo pipefail
project=$(cd "${1:?pass the path to the prepared Lake project}" && pwd)
src=$(cd "$(dirname "$0")" && pwd)
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
cd "$project"
lake env lean --version
modules=(QuadraticCoefficients FourierFrame CyclotomicSlope MixedSlope FrameWitness)
for mod in "${modules[@]}"; do
    lake env lean -R "$src" -o "$out/$mod.olean" "$src/$mod.lean"
done
lake env bash -c 'export LEAN_PATH="$1:$LEAN_PATH"; shift; leanchecker --verbose "$@"' _ "$out" "${modules[@]}"
