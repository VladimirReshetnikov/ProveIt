#!/usr/bin/env bash
set -euo pipefail
if [[ $# != 3 ]]; then echo 'usage: checker REPO SOURCE_DIR NEW_OUTPUT_DIR' >&2; exit 2; fi
repo=$1
src=$2
out=$3
[[ ! -e "$out" ]] || { echo 'output already exists' >&2; exit 1; }
for key in GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE GIT_OBJECT_DIRECTORY GIT_ALTERNATE_OBJECT_DIRECTORIES; do
  [[ ! -v $key ]] || { echo "refusing inherited $key" >&2; exit 1; }
done
mkdir -p "$out"
cp "$src/PA194Site49SmallGapArithmetic.lean" "$out/"
cd "$repo"
lake env lean -R "$out" -o "$out/PA194Site49SmallGapArithmetic.olean" "$out/PA194Site49SmallGapArithmetic.lean" > "$out/build.log" 2>&1
cat "$out/build.log"
! rg -q 'sorryAx' "$out/build.log"
for thm in gapTwo gapThree gapFour; do
  rg -q "'PA194Site49SmallGapArithmetic.$thm' depends on axioms:" "$out/build.log"
done
cmp "$src/PA194Site49SmallGapArithmetic.lean" "$out/PA194Site49SmallGapArithmetic.lean"
sha256sum "$out/PA194Site49SmallGapArithmetic.lean" > "$out/source.sha256"
echo 'PASS: natural-number small-gap word arithmetic; machine correspondence remains separate.'
