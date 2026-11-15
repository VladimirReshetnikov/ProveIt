#!/usr/bin/env bash
set -euo pipefail
if (($# != 2)); then echo 'usage: REPO NEW_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); out=$(realpath -m "$2"); src=$(cd "$(dirname "$0")" && pwd)
[[ ! -e "$out" ]] || { echo 'Output exists' >&2; exit 2; }
check_inputs() {
 printf '%s  %s\n' \
 a716d74b3001b0921f19f2634930df07544e2a0007a9e76b7916a78649b3f051 "$src/PA194ReopenProof.lean" \
 723a9891766395a547317de32f5801c7972dd1dfdcbf5520b6d469f261face5c /dev/shm/pa194-general-separation-replay/PA194BindFormulaInverse.olean \
 d4bd149ccfb0ea0b53b0c32fed5b1750f91a090823aff4a4beedb6440354a61a /dev/shm/pa194-model-closure-replay/PA194CloseHistory.olean \
 1915479ceecf82defc487dc001d9c3de9e1ecfb6ad17c257f5ec3db01221327b /dev/shm/pa194-fully-closed-replay/PA194FullyClosedSeparation.olean | sha256sum -c -
}
check_inputs
mkdir -p "$out"
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$out:/dev/shm/pa194-fully-closed-replay:/dev/shm/pa194-model-separation-full-replay:/dev/shm/pa194-model-separation-seeded-replay:/dev/shm/pa194-model-closure-definability-replay:/dev/shm/pa194-model-closure-replay:/dev/shm/pa194-general-separation-replay:/dev/shm/pa194-ranked-open-separation-replay-v3:/dev/shm/pa194-unrestricted-all-replay:/dev/shm/pa194-adjunctive-admission-audit:/dev/shm/pa194-full-one-level-audit:/tmp/current14-standard-fresh-build-20261104/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib:$lake_path"
lean -j1 -M 4000 -R "$src" -o "$out/PA194ReopenProof.olean" "$src/PA194ReopenProof.lean" > "$out/check.log" 2>&1
if rg -q "sorryAx|declaration uses 'sorry'" "$out/check.log"; then cat "$out/check.log"; exit 1; fi
[[ $(rg -c 'depends on axioms:' "$out/check.log") == 4 ]]
cat "$out/check.log"
check_inputs
echo 'PASS: internal proof reopening for model-valued closure lengths; dependencies prebuilt.'
