#!/usr/bin/env bash
set -euo pipefail
if (($# != 2)); then echo 'usage: REPO NEW_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); out=$(realpath -m "$2"); src=$(cd "$(dirname "$0")" && pwd)
[[ ! -e "$out" ]] || { echo 'Output exists' >&2; exit 2; }
check_inputs() {
 printf '%s  %s\n' \
 10bac54517209a8a888f2a6d37e17b1f90e76ad9ff9c1032bef24dad865e4e5c "$src/PA194ContextDoubleSpecializeCode.lean" \
 f5dad78a55d1156f9fc296e793d25a410da95f0e14ad2fe5fb9b336fab13f274 "$src/PA194ContextStepApplicationCode.lean" \
 7f8cfcc202a4fdaf929f7d00c455352586327817139a623b5490f7a3e3bb3cdb "$src/PA194OrdinalStepApplicationCode.lean" \
 63583ead8c3f90bb2621596aef31bd21ca32bc83eb225f32796d63b5cfa90c99 /dev/shm/pa194-context-specialize-code-repo/PA194ContextSpecializeCode.olean \
 1df71c4caed5133016b5af8afea38cebeece2c70139e8903d28abb090f20da2e /dev/shm/pa194-induction-step-shift-repo/PA194InductionStepShiftCode.olean \
 ca883fcc331af8acc2e3f00071f78cabc8d761c2213c6b69a3ba8b15839be16c /dev/shm/pa194-ordinal-uniform-repo/PA194FixedSyntaxQuote.olean | sha256sum -c -
}
check_inputs
mkdir -p "$out"
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$out:/dev/shm/pa194-induction-step-shift-repo:/dev/shm/pa194-internal-induction-at-context-repo:/dev/shm/pa194-context-specialize-code-repo:/dev/shm/pa194-context-mp-code-repo:/dev/shm/pa194-context-conjunction-code-repo:/dev/shm/pa194-context-shift-code-repo:/dev/shm/pa194-internal-separation-shift-repo:/dev/shm/pa194-internal-induction-base-at-repo:/dev/shm/pa194-induction-base-shift-repo:/dev/shm/pa194-ordinal-uniform-repo:/dev/shm/pa194-ordinal-fixed-repo:/dev/shm/pa194-ordinal-induction-code-repo:/dev/shm/pa194-ordinal-statement-repo:/dev/shm/pa194-typed-schema-repo:/dev/shm/pa194-fully-closed-repo:/dev/shm/pa194-fully-closed-replay:/dev/shm/pa194-model-separation-full-replay:/dev/shm/pa194-model-separation-seeded-replay:/dev/shm/pa194-model-closure-definability-replay:/dev/shm/pa194-model-closure-replay:/dev/shm/pa194-general-separation-repo:/dev/shm/pa194-ranked-open-separation-repo:/dev/shm/pa194-general-separation-replay:/dev/shm/pa194-ranked-open-separation-replay-v3:/dev/shm/pa194-unrestricted-all-replay:/dev/shm/pa194-adjunctive-admission-audit:/dev/shm/pa194-full-one-level-audit:/tmp/current14-standard-fresh-build-20261104/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib:$lake_path"
for name in PA194ContextDoubleSpecializeCode PA194ContextStepApplicationCode PA194OrdinalStepApplicationCode; do
 lean -j1 -M 4000 -R "$src" -o "$out/$name.olean" "$src/$name.lean" > "$out/$name.log" 2>&1
 if rg -q "sorryAx|declaration uses 'sorry'" "$out/$name.log"; then cat "$out/$name.log"; exit 1; fi
 cat "$out/$name.log"
done
for name in PA194ContextDoubleSpecializeCode PA194ContextStepApplicationCode PA194OrdinalStepApplicationCode; do
 [[ $(rg -c 'depends on axioms:' "$out/$name.log") == 3 ]]
done
check_inputs
echo 'PASS: explicit uniform ordinal-step application proof code under arbitrary contexts; dependencies prebuilt.'
