#!/usr/bin/env bash
set -euo pipefail
# Run from repo root. Optional --start-site/--stop-site check a subrange.
task_dir=$(mktemp -d /dev/shm/pa195-source-iteration.XXXXXXXX)
trap 'rm -rf "$task_dir"' EXIT
mkdir -p "$task_dir/M6/Source" "$task_dir/PA196"
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
printf '%s  %s\n' \
  b6ef7ec9fdcd5e876314a37696c3ce2dd66a86db16d5efc2c34e963f3f8a047e "$upstream/Source/Determinism.lean" \
  02e13fa9c01a3de73afd0f3cbebd68b7ce2b86cdecbebfc05e5f1b0f7b09a45b "$upstream/Source/CyclicDriver.lean" \
  576b6bda8d521c852cfd8c71b257e3d11fddc452969e56d1b996c06f9564968f "$upstream/Source/CyclicDeterminism.lean" \
  af81fe00cc0b1420f5b4e547f7adff77279f4211d7f7aa401395fa15ee6f1360 "$upstream/Source/RootFrame.lean" \
  4a4f5a95b397beee45bf20d853f66be27fde7955bb621f52a8c6d48de5d351f6 "$upstream/Source/FileInvariant.lean" \
  3eda577b4f6d1934af3e719dcb99a259b2f0d2ce9b9b9847401aa4318aba12d0 "$upstream/PositiveInvariant.lean" \
  bdd8711116e5a99811ba77d20cb0cd35d9963d51ced9f1fa5c429556370c1bba "$base/jamesyc-upstream/pa196/PA196/Frame.lean" | sha256sum -c
for task_module in Source/Determinism Source/CyclicDriver Source/CyclicDeterminism Source/RootFrame Source/FileInvariant PositiveInvariant; do
  lean -M6000 -j1 -o "$task_dir/M6/$task_module.olean" "$upstream/$task_module.lean"
done
lean -M6000 -j1 -o "$task_dir/PA196/Frame.olean" "$base/jamesyc-upstream/pa196/PA196/Frame.lean"
for task_module in PA195RuntimeContracts PA195PrimitiveSimulation; do
  lean -M6000 -j1 -o "$task_dir/$task_module.olean" "$base/pa195-source-iteration/$task_module.lean"
done
lean -M6000 -j1 "$base/pa195-source-iteration/PA195CompilerCorrectness.lean"
