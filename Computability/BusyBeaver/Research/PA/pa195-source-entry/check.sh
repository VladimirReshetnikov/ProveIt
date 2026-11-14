#!/usr/bin/env bash
set -euo pipefail
# Run from repository root; rebuild pinned dependencies and the generated tree.
task_dir=$(mktemp -d /dev/shm/pa195-source-entry-check.XXXXXXXX)
trap 'rm -rf "$task_dir"' EXIT
mkdir -p "$task_dir/M6/Source"
upstream=Computability/BusyBeaver/Research/PA/jamesyc-upstream/pa196/M6
printf '%s  %s\n' \
  152d1d552b27baca8db0ac05b16092d9083c2ab979bb0b4e7f96a95803d9a9b0 "$upstream/Zip.lean" \
  e66961d7acb60e0c84e9674ee2d91ca2049ac6d704ad0edf7d971ef933f3ce2e "$upstream/Runtime.lean" \
  062a7aa69779a8cf94544953ae46b944dbad2746ea7dde3dfac8d170e3a8bcd7 "$upstream/Reference230.lean" \
  7a469f4b72365cac658d441277f9d829940df3c7052b280805a1ec8c3c42c69f "$upstream/Native.lean" \
  4edcf4eb98b24999f610f06a22d943db68c7c2cae8d96160bbf614c75821738a "$upstream/Source/Syntax.lean" \
  98bdd0185ee5db469d400e32d349d20368ac117742386b6e253d3636c677cdd8 "$upstream/Source/PathTrie.lean" \
  09896e31c4d5d3fd5cf636d3cfea0dddfb4396fe48781aaf5ab90f151878b8fb "$upstream/FastResolve.lean" \
  8f4b3d4ce58cff2f9787300c206092fcf1e62410b5bad9a5fe54216da39209f0 "$upstream/TreeSite.lean" | sha256sum -c
export LEAN_PATH="$task_dir:$(lake env printenv LEAN_PATH)"
for task_module in Zip Runtime Reference230 Native Source/Syntax Source/PathTrie FastResolve TreeSite; do
  lean -M6000 -j1 -o "$task_dir/M6/$task_module.olean" "$upstream/$task_module.lean"
done
base=Computability/BusyBeaver/Research/PA
lean -M6000 -j1 -o "$task_dir/PA195LocalQuotient.olean" "$base/pa195-quotient/PA195LocalQuotient.lean"
lean -M6000 -j1 -o "$task_dir/PA195RuntimeEngine.olean" "$base/pa195-runtime/PA195RuntimeEngine.lean"
lean -M6000 -j1 -o "$task_dir/PA195Site25.olean" "$base/pa195-site25/PA195Site25.lean"
python3 "$base/pa195-source-entry/generate.py" "$task_dir/PA195SourceTree.lean"
lean -M6000 -j1 --root="$task_dir" -o "$task_dir/PA195SourceTree.olean" "$task_dir/PA195SourceTree.lean"
lean -M6000 -j1 "$base/pa195-source-entry/PA195SourceEntry.lean"
