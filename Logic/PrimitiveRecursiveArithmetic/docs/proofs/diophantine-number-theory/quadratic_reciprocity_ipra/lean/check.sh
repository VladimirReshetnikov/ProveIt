#!/bin/sh
# Build each module from source without using any existing .olean files.
set -eu
src=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
cd "$src"
build_dir=$(mktemp -d)
trap 'rm -rf -- "$build_dir"' EXIT
export LEAN_PATH="$build_dir"
lean --version
for module in QRConstructiveList QRPermutation QuadraticReciprocity Involution QREuler QRGauss Supplements QRMain QRWitnesses
do
    echo "Checking $module"
    lean -o "$build_dir/$module.olean" "$module.lean"
done
lean Audit.lean
