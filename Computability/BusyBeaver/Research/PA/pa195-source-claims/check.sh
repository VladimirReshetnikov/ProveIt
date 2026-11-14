#!/usr/bin/env bash
set -euo pipefail
# Run from repository root. Pass --start-site/--stop-site to check a range.
task_dir=$(mktemp -d /dev/shm/pa195-source-claims.XXXXXXXX)
trap 'rm -rf "$task_dir"' EXIT
mkdir -p "$task_dir/M6/Source" "$task_dir/batches"
base=Computability/BusyBeaver/Research/PA
upstream=$base/jamesyc-upstream/pa196/M6
printf '%s  %s\n' \
  4edcf4eb98b24999f610f06a22d943db68c7c2cae8d96160bbf614c75821738a "$upstream/Source/Syntax.lean" \
  98bdd0185ee5db469d400e32d349d20368ac117742386b6e253d3636c677cdd8 "$upstream/Source/PathTrie.lean" \
  09896e31c4d5d3fd5cf636d3cfea0dddfb4396fe48781aaf5ab90f151878b8fb "$upstream/FastResolve.lean" \
  8f4b3d4ce58cff2f9787300c206092fcf1e62410b5bad9a5fe54216da39209f0 "$upstream/TreeSite.lean" | sha256sum -c
export LEAN_PATH="$task_dir:$(lake env printenv LEAN_PATH)"
for task_module in Source/Syntax Source/PathTrie FastResolve TreeSite; do
  lean -M6000 -j1 -o "$task_dir/M6/$task_module.olean" "$upstream/$task_module.lean"
done
python3 "$base/pa195-source-entry/generate.py" "$task_dir/PA195SourceTree.lean"
lean -M6000 -j1 --root="$task_dir" -o "$task_dir/PA195SourceTree.olean" "$task_dir/PA195SourceTree.lean"
lean -M6000 -j1 -o "$task_dir/PA195SourceClaims.olean" "$base/pa195-source-claims/PA195SourceClaims.lean"
python3 "$base/pa195-source-claims/generate.py" --out "$task_dir/batches" "$@"
for task_batch in "$task_dir"/batches/*.lean; do
  test -f "$task_batch" || continue
  lean -M6000 -j1 "$task_batch"
done
