#!/usr/bin/env bash
set -euo pipefail
if (($# != 2)); then echo 'usage: REPO NEW_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); out=$(realpath -m "$2"); src=$(cd "$(dirname "$0")" && pwd)
[[ ! -e "$out" ]] || { echo 'Output exists' >&2; exit 2; }
check_inputs() {
 printf '%s  %s\n' \
 94bc1e21d74e6ef0ae3e6ecef90e2a841b4fe435406ed76ac670862e6e0abf01 "$src/PA194ContextBaseApplicationCode.lean" \
 3f40b867cbe3d7df0b7c9aa7e9da2eeec834c7e76b54ebcdbcae6ca701442005 "$src/PA194OrdinalBaseApplicationCode.lean" \
 63583ead8c3f90bb2621596aef31bd21ca32bc83eb225f32796d63b5cfa90c99 /dev/shm/pa194-context-specialize-code-repo/PA194ContextSpecializeCode.olean \
 03568d79012b3f6c35c94e502980352bc4b67da244de8c8c7b001e777f695f4b /dev/shm/pa194-internal-induction-at-context-repo/PA194InternalBaseAtContext.olean \
 ca883fcc331af8acc2e3f00071f78cabc8d761c2213c6b69a3ba8b15839be16c /dev/shm/pa194-ordinal-uniform-repo/PA194FixedSyntaxQuote.olean | sha256sum -c -
}
check_inputs
mkdir -p "$out"
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$out:/dev/shm/pa194-internal-induction-at-context-repo:/dev/shm/pa194-context-specialize-code-repo:/dev/shm/pa194-context-mp-code-repo:/dev/shm/pa194-context-conjunction-code-repo:/dev/shm/pa194-context-shift-code-repo:/dev/shm/pa194-internal-separation-shift-repo:/dev/shm/pa194-internal-induction-base-at-repo:/dev/shm/pa194-induction-base-shift-repo:/dev/shm/pa194-ordinal-uniform-repo:/dev/shm/pa194-ordinal-fixed-repo:/dev/shm/pa194-ordinal-induction-code-repo:/dev/shm/pa194-ordinal-statement-repo:/dev/shm/pa194-typed-schema-repo:/dev/shm/pa194-fully-closed-repo:/dev/shm/pa194-fully-closed-replay:/dev/shm/pa194-model-separation-full-replay:/dev/shm/pa194-model-separation-seeded-replay:/dev/shm/pa194-model-closure-definability-replay:/dev/shm/pa194-model-closure-replay:/dev/shm/pa194-general-separation-repo:/dev/shm/pa194-ranked-open-separation-repo:/dev/shm/pa194-general-separation-replay:/dev/shm/pa194-ranked-open-separation-replay-v3:/dev/shm/pa194-unrestricted-all-replay:/dev/shm/pa194-adjunctive-admission-audit:/dev/shm/pa194-full-one-level-audit:/tmp/current14-standard-fresh-build-20261104/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib:$lake_path"
for name in PA194ContextBaseApplicationCode PA194OrdinalBaseApplicationCode; do
 lean -j1 -M 4000 -R "$src" -o "$out/$name.olean" "$src/$name.lean" > "$out/$name.log" 2>&1
 if rg -q "sorryAx|declaration uses 'sorry'" "$out/$name.log"; then cat "$out/$name.log"; exit 1; fi
 cat "$out/$name.log"
done
[[ $(rg -c 'depends on axioms:' "$out/PA194ContextBaseApplicationCode.log") == 3 ]]
[[ $(rg -c 'depends on axioms:' "$out/PA194OrdinalBaseApplicationCode.log") == 3 ]]
check_inputs
echo 'PASS: explicit uniform ordinal-base application proof code under arbitrary contexts; dependencies prebuilt.'
