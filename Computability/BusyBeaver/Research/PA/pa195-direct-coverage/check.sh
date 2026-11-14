#!/usr/bin/env bash
set -euo pipefail
# Run from repo root. Optional --start-site/--stop-site check a subrange.
task_dir=$(mktemp -d /dev/shm/pa195-direct-coverage.XXXXXXXX)
trap 'rm -rf "$task_dir"' EXIT
mkdir -p "$task_dir/M6/Source" "$task_dir/batches"
base=Computability/BusyBeaver/Research/PA
upstream=$base/jamesyc-upstream/pa196/M6
printf '%s  %s\n' \
  152d1d552b27baca8db0ac05b16092d9083c2ab979bb0b4e7f96a95803d9a9b0 "$upstream/Zip.lean" \
  e66961d7acb60e0c84e9674ee2d91ca2049ac6d704ad0edf7d971ef933f3ce2e "$upstream/Runtime.lean" \
  062a7aa69779a8cf94544953ae46b944dbad2746ea7dde3dfac8d170e3a8bcd7 "$upstream/Reference230.lean" \
  7a469f4b72365cac658d441277f9d829940df3c7052b280805a1ec8c3c42c69f "$upstream/Native.lean" \
  4edcf4eb98b24999f610f06a22d943db68c7c2cae8d96160bbf614c75821738a "$upstream/Source/Syntax.lean" \
  98bdd0185ee5db469d400e32d349d20368ac117742386b6e253d3636c677cdd8 "$upstream/Source/PathTrie.lean" \
  09896e31c4d5d3fd5cf636d3cfea0dddfb4396fe48781aaf5ab90f151878b8fb "$upstream/FastResolve.lean" \
  8f4b3d4ce58cff2f9787300c206092fcf1e62410b5bad9a5fe54216da39209f0 "$upstream/TreeSite.lean" \
  8689481036b4c29d1a8ce7fec25e6ae12e8ac54fd4a86f23fb9cb5ee01b39f38 "$upstream/Source/Semantics.lean" \
  102490b3a2ca6b3b57f4e5b52b0409a66f8067b3231e9f48751a4162ecc7627f "$upstream/Source/PhysicalRegisters.lean" | sha256sum -c
export LEAN_PATH="$task_dir:$(lake env printenv LEAN_PATH)"
for task_module in Zip Runtime Reference230 Native Source/Syntax Source/PathTrie FastResolve TreeSite Source/Semantics Source/PhysicalRegisters; do
  lean -M6000 -j1 -o "$task_dir/M6/$task_module.olean" "$upstream/$task_module.lean"
done
lean -M6000 -j1 -o "$task_dir/PA195LocalQuotient.olean" "$base/pa195-quotient/PA195LocalQuotient.lean"
lean -M6000 -j1 -o "$task_dir/PA195RuntimeEngine.olean" "$base/pa195-runtime/PA195RuntimeEngine.lean"
lean -M6000 -j1 -o "$task_dir/PA195Symbolic.olean" "$base/pa195-symbolic/PA195Symbolic.lean"
python3 "$base/pa195-source-entry/generate.py" "$task_dir/PA195SourceTree.lean"
lean -M6000 -j1 --root="$task_dir" -o "$task_dir/PA195SourceTree.olean" "$task_dir/PA195SourceTree.lean"
lean -M6000 -j1 -o "$task_dir/PA195SourcePhysical.olean" "$base/pa195-direct-coverage/PA195SourcePhysical.lean"
python3 "$base/pa195-direct-coverage/generate.py" --out "$task_dir/batches" "$@"
for task_batch in "$task_dir"/batches/*.lean; do
  test -f "$task_batch" || continue
  lean -M6000 -j1 "$task_batch"
done
