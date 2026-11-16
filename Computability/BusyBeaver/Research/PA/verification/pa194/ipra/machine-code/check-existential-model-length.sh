#!/usr/bin/env bash
set -euo pipefail
src=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
cd "${1:?repository root required}"
out=$(realpath -m "${2:?fresh output directory required}")
mkdir "$out"
export LEAN_PATH="$out:/dev/shm/pa194-compressed-executor-repo:/dev/shm/pa194-bidirectional-run-scan-repo:/dev/shm/pa194-bidirectional-generic-repo:/dev/shm/pa194-symbolic-zipper-repo:/dev/shm/pa194-site31-matched-repo:/dev/shm/pa194-one-spare-file-roundtrip-repo:/dev/shm/pa194-site28-work/build-one-spare-file-roundtrip:/dev/shm/pa194-site28-work/build-carry-roundtrip:/dev/shm/pa194-site27-coherent/build:/dev/shm/pa194-site27-foundation-view:/dev/shm/pa194-fetch-coherent-full-v2/foundation-view:/tmp/current14-standard-fresh-build-20261104/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib:/dev/shm/pa194-model-length:/dev/shm/pa194-unified-coherent/build:$(lake env printenv LEAN_PATH)"
for mod in PA194ExistentialModelLength; do
 lean -j1 -M6000 -R "$src" -o "$out/$mod.olean" "$src/$mod.lean" > "$out/$mod.log" 2>&1
done
log="$out/PA194ExistentialModelLength.log"
if rg -q 'sorryAx|declaration uses .sorry.' "$log"; then cat "$log"; exit 1; fi
[[ $(rg -c 'depends on axioms:' "$log") == 3 ]]
cat "$log"
