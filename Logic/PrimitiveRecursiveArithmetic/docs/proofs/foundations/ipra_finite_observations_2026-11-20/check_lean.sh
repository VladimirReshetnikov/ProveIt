#!/usr/bin/env bash
# Run inside the pinned ProveIt Lake environment (see README.md).
set -euo pipefail
packet="$(cd "$(dirname "$0")" && pwd)"
objects="$(mktemp -d)"
trap 'rm -rf "$objects"' EXIT
export LEAN_PATH="$objects${LEAN_PATH:+:$LEAN_PATH}"
lean --version
for file in lean/Completion.lean lean/Closure.lean lean/Quotient.lean categorica/StableQuotient.lean; do
  lean "$packet/$file"
  echo "checked $file"
done
lean -o "$objects/Merge.olean" --root="$packet/categorica" "$packet/categorica/Merge.lean"
echo 'checked categorica/Merge.lean'
for file in categorica/Finality.lean categorica/PathDerivation.lean topologica/NervePolarity.lean topologica/ElementaryCollapse.lean topologica/NerveTransfer.lean analytica/ContourRibbon.lean analytica/Secant.lean; do
  lean "$packet/$file"
  echo "checked $file"
done
