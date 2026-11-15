#!/usr/bin/env bash
set -euo pipefail
if (($# != 2)); then echo 'usage: REPO NEW_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); out=$(realpath -m "$2")
src=$(cd "$(dirname "$0")" && pwd)
[[ ! -e "$out" ]] || { echo 'Output exists' >&2; exit 2; }
check_inputs() {
 printf '%s  %s\n' \
 c0bc3aef3b131361990dc76ffd7c9534de375973f4dd9f15a282a10e71fa04e0 "$src/PA194OrdinalClosed.lean" \
 16913ac4afbad6a6d2a5e801a0289424888ed1d60d0880a6a072e1e325c7be5d /dev/shm/pa194-ordinal-uniform-replay/PA194OrdinalUniform.olean \
 6009b96d84d3686b3e80393158587bef16be7c12892ee7054a1e04fc093d064b /dev/shm/pa194-uniform-fully-closed-replay/PA194UniformFreeBoundModel.olean \
 336f4e3d9dccadb16c1b98d2c0361c44f1f2d99de863f139e4c83014075a3352 /dev/shm/pa194-uniform-closure-replay/PA194UniformCloseModel.olean | sha256sum -c -
}
check_inputs
mkdir -p "$out"
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$out:/dev/shm/pa194-ordinal-uniform-replay:/dev/shm/pa194-uniform-fully-closed-replay:/dev/shm/pa194-uniform-sep-combined-replay:/dev/shm/pa194-uniform-closure-replay:/dev/shm/pa194-full-sep-theory-replay:/dev/shm/pa194-ordinal-fixed-replay:/dev/shm/pa194-ordinal-induction-code-replay:/dev/shm/pa194-ordinal-statement-replay:/dev/shm/pa194-typed-schema-replay:/dev/shm/pa194-fully-closed-replay:/dev/shm/pa194-model-separation-full-replay:/dev/shm/pa194-model-separation-seeded-replay:/dev/shm/pa194-model-closure-definability-replay:/dev/shm/pa194-model-closure-replay:/dev/shm/pa194-general-separation-replay:/dev/shm/pa194-ranked-open-separation-replay-v3:/dev/shm/pa194-unrestricted-all-replay:/dev/shm/pa194-adjunctive-admission-audit:/dev/shm/pa194-full-one-level-audit:/tmp/current14-standard-fresh-build-20261104/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib:$lake_path"
lean -j1 -M 4000 -R "$src" -o "$out/PA194OrdinalClosed.olean" "$src/PA194OrdinalClosed.lean" > "$out/check.log" 2>&1
if rg -q "sorryAx|declaration uses 'sorry'" "$out/check.log"; then cat "$out/check.log"; exit 1; fi
[[ $(rg -c 'depends on axioms:' "$out/check.log") == 3 ]]
cat "$out/check.log"
check_inputs
echo 'PASS: uniform parameter-closed ordinal-induction syntax; dependencies prebuilt.'
