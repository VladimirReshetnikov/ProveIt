#!/usr/bin/env bash
set -euo pipefail
if (($# != 2)); then echo 'usage: REPO NEW_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); out=$(realpath -m "$2"); src=$(cd "$(dirname "$0")" && pwd)
[[ ! -e "$out" ]] || { echo 'Output exists' >&2; exit 2; }
check_inputs() {
 printf '%s  %s\n' \
 f2aa40e0ca4a5ffd01f2e913161b2715dd6bacadecce13614067caf8f3367725 "$src/PA194StandardOrdinalReduction.lean" \
 45054ae4bd07e96cb66b086c072b1b2bd7d1ed459ffb60c90f95c87d673a56c4 /dev/shm/pa194-quoted-induction-repo/PA194QuotedInduction.olean \
 9009cf1b28de711c03dc21c8392828917dcf69885ea887dda35e1852c32b62e4 /dev/shm/pa194-ordinal-suppliers-repo/PA194OrdinalSuppliers.olean | sha256sum -c -
}
check_inputs
mkdir -p "$out"
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
baselines="/dev/shm/pa194-unclose-envelope-replay:/dev/shm/pa194-uniform-fully-closed-replay:/dev/shm/pa194-uniform-closure-replay:/dev/shm/pa194-fully-closed-replay:/dev/shm/pa194-model-separation-full-replay:/dev/shm/pa194-model-separation-seeded-replay:/dev/shm/pa194-model-closure-definability-replay:/dev/shm/pa194-model-closure-replay:/dev/shm/pa194-general-separation-replay:/dev/shm/pa194-ranked-open-separation-replay-v3:/dev/shm/pa194-closed-sep-theory-replay:/dev/shm/pa194-uniform-sep-combined-replay:/dev/shm/pa194-standard-no-free-replay:/dev/shm/pa194-closed-sep-classifier-replay:/dev/shm/pa194-fairness-full-source-replay:/dev/shm/pa194-generic-sim-replay:/dev/shm/pa194-adjunctive-sim-v2-replay:/dev/shm/pa194-shift-interface-replay:/dev/shm/pa194-unrestricted-existential-v2-replay:/dev/shm/pa194-qf-ranked-existential-audit:/dev/shm/pa194-adjunctive-admission-audit:/dev/shm/pa194-general-shift-replay:/dev/shm/pa194-general-reverse-shift-replay:/dev/shm/pa194-unrestricted-all-replay:/dev/shm/pa194-general-freshness-audit:/dev/shm/pa194-observational-general-audit:/dev/shm/pa194-full-one-level-audit"
export LEAN_PATH="$out:/dev/shm/pa194-quoted-induction-repo:/dev/shm/pa194-ordinal-suppliers-repo:/dev/shm/pa194-ordinal-fixed-repo:/dev/shm/pa194-ordinal-induction-code-repo:/dev/shm/pa194-ordinal-statement-repo:/dev/shm/pa194-intersection-proof-repo:/dev/shm/pa194-full-sep-open-repo:/dev/shm/pa194-typed-schema-replay:/dev/shm/pa194-reopen-proof-replay:/dev/shm/pa194-full-sep-theory-replay:$baselines:/tmp/current14-standard-fresh-build-20261104/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib:$lake_path"
lean -j1 -M 5000 -R "$src" -o "$out/PA194StandardOrdinalReduction.olean" "$src/PA194StandardOrdinalReduction.lean" > "$out/check.log" 2>&1
if rg -q "sorryAx|declaration uses 'sorry'" "$out/check.log"; then cat "$out/check.log"; exit 1; fi
[[ $(rg -c 'depends on axioms:' "$out/check.log") == 1 ]]
cat "$out/check.log"
check_inputs
echo 'PASS: standard-property induction conditional on six finite context proofs; dependencies prebuilt.'
