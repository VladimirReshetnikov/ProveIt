#!/bin/sh
# Rebuild in a fresh directory and print the trusted-axiom audit.
set -eu
cd "$(dirname "$0")"
compiler=${LEAN:-lean}
build_dir=$(mktemp -d)
trap 'rm -rf "$build_dir"' EXIT
export LEAN_PATH="$build_dir"

"$compiler" --version
for module in \
    BertrandSearch Binomial BertrandBounds BertrandValuation BertrandProducts \
    BertrandPrimeFactor Primorial BertrandFactorCount BertrandAssembly \
    BertrandLegendre BertrandReconstruction Bertrand
do
    echo "Checking $module.lean"
    "$compiler" -o "$build_dir/$module.olean" "$module.lean"
done
echo "Checking Audit.lean"
"$compiler" Audit.lean
