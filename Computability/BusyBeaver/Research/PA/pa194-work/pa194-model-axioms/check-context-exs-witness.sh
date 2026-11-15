#!/usr/bin/env bash
set -euo pipefail
if (($# != 2)); then echo 'usage: REPO NEW_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); out=$(realpath -m "$2"); src=$(cd "$(dirname "$0")" && pwd)
[[ ! -e "$out" ]] || { echo 'Output exists' >&2; exit 2; }
check_inputs() {
 printf '%s  %s\n' \
 6e133992c761a312f0e69740ac0fae2b7bea2b309b810e4286f98da29f0fd110 "$src/PA194ContextExsWitnessCode.lean" \
 116e34e55d6833a865b98a20954009b8d57038ecf7c3bd4caf2f91f4ebb1de42 /dev/shm/pa194-context-quantifier-code-repo/PA194ContextExsElimCode.olean | sha256sum -c -
}
check_inputs
mkdir -p "$out"
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$out:/dev/shm/pa194-context-quantifier-code-repo:/dev/shm/pa194-internal-induction-at-context-repo:/dev/shm/pa194-context-specialize-code-repo:/dev/shm/pa194-context-mp-code-repo:/dev/shm/pa194-context-conjunction-code-repo:/dev/shm/pa194-context-shift-code-repo:/dev/shm/pa194-internal-separation-shift-repo:/dev/shm/pa194-internal-induction-base-at-repo:/dev/shm/pa194-induction-base-shift-repo:/dev/shm/pa194-ordinal-uniform-repo:/dev/shm/pa194-ordinal-fixed-repo:/dev/shm/pa194-ordinal-induction-code-repo:/dev/shm/pa194-ordinal-statement-repo:/dev/shm/pa194-typed-schema-repo:/dev/shm/pa194-fully-closed-repo:/dev/shm/pa194-fully-closed-replay:/dev/shm/pa194-model-separation-full-replay:/dev/shm/pa194-model-separation-seeded-replay:/dev/shm/pa194-model-closure-definability-replay:/dev/shm/pa194-model-closure-replay:/dev/shm/pa194-general-separation-repo:/dev/shm/pa194-ranked-open-separation-repo:/dev/shm/pa194-general-separation-replay:/dev/shm/pa194-ranked-open-separation-replay-v3:/dev/shm/pa194-unrestricted-all-replay:/dev/shm/pa194-adjunctive-admission-audit:/dev/shm/pa194-full-one-level-audit:/tmp/current14-standard-fresh-build-20261104/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib:$lake_path"
for name in PA194ContextExsWitnessCode; do
 lean -j1 -M 4000 -R "$src" -o "$out/$name.olean" "$src/$name.lean" > "$out/$name.log" 2>&1
 if rg -q "sorryAx|declaration uses 'sorry'" "$out/$name.log"; then cat "$out/$name.log"; exit 1; fi
 cat "$out/$name.log"
done
[[ $(rg -c 'depends on axioms:' "$out/PA194ContextExsWitnessCode.log") == 2 ]]
check_inputs
echo 'PASS: contextual existential witness proof code under arbitrary contexts; dependencies prebuilt.'
