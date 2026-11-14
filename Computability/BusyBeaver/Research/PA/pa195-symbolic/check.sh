#!/usr/bin/env bash
set -euo pipefail
# Run from repository root. Optional arguments are passed to generate.py;
# e.g. --start-site 25 --stop-site 50 checks just that range.
task_dir=$(mktemp -d /dev/shm/pa195-symbolic-check.XXXXXXXX)
trap 'rm -rf "$task_dir"' EXIT
mkdir -p "$task_dir/M6" "$task_dir/batches"
upstream=Computability/BusyBeaver/Research/PA/jamesyc-upstream/pa196/M6
printf '%s  %s\n' \
  152d1d552b27baca8db0ac05b16092d9083c2ab979bb0b4e7f96a95803d9a9b0 "$upstream/Zip.lean" \
  e66961d7acb60e0c84e9674ee2d91ca2049ac6d704ad0edf7d971ef933f3ce2e "$upstream/Runtime.lean" \
  062a7aa69779a8cf94544953ae46b944dbad2746ea7dde3dfac8d170e3a8bcd7 "$upstream/Reference230.lean" \
  7a469f4b72365cac658d441277f9d829940df3c7052b280805a1ec8c3c42c69f "$upstream/Native.lean" | sha256sum -c
export LEAN_PATH="$task_dir:$(lake env printenv LEAN_PATH)"
for task_module in Zip Runtime Reference230 Native; do
  lean -M6000 -j1 -o "$task_dir/M6/$task_module.olean" "$upstream/$task_module.lean"
done
base=Computability/BusyBeaver/Research/PA
lean -M6000 -j1 -o "$task_dir/PA195LocalQuotient.olean" "$base/pa195-quotient/PA195LocalQuotient.lean"
lean -M6000 -j1 -o "$task_dir/PA195RuntimeEngine.olean" "$base/pa195-runtime/PA195RuntimeEngine.lean"
lean -M6000 -j1 -o "$task_dir/PA195Symbolic.olean" "$base/pa195-symbolic/PA195Symbolic.lean"
python3 "$base/pa195-symbolic/generate.py" --out "$task_dir/batches" "$@"
for task_batch in "$task_dir"/batches/*.lean; do
  test -f "$task_batch" || continue
  lean -M6000 -j1 "$task_batch"
done
