#!/usr/bin/env bash
set -euo pipefail
if (($# != 2)); then echo 'usage: REPO NEW_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); out=$(realpath -m "$2"); src=$(cd "$(dirname "$0")" && pwd)
[[ ! -e "$out" ]] || { echo 'Output exists' >&2; exit 2; }
check_inputs() {
 printf '%s  %s\n' \
 d97904a9201f053bd3aab7f957dcafaad64509903a9bc5dedee287a60a330e08 "$src/PA194InternalBaseAtContext.lean" \
 7b7d8cccab03a7301edbaa6ea880377f1de2aa4c1720fbc2be1eac7eb4b65e7b "$src/PA194InternalStepAtContext.lean" \
 41dfabc50c604565ff90125658b838f0e15e155ce446e91adcba0bad0beb6014 /dev/shm/pa194-internal-induction-base-at-repo/PA194InternalInductionBaseAt.olean \
 1df71c4caed5133016b5af8afea38cebeece2c70139e8903d28abb090f20da2e /dev/shm/pa194-induction-step-shift-repo/PA194InductionStepShiftCode.olean | sha256sum -c -
}
check_inputs
mkdir -p "$out"
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$out:/dev/shm/pa194-internal-induction-base-at-repo:/dev/shm/pa194-induction-step-shift-repo:/dev/shm/pa194-induction-base-shift-repo:/dev/shm/pa194-ordinal-uniform-repo:/dev/shm/pa194-ordinal-fixed-repo:/dev/shm/pa194-ordinal-induction-code-repo:/dev/shm/pa194-ordinal-statement-repo:/dev/shm/pa194-typed-schema-repo:/dev/shm/pa194-fully-closed-repo:/dev/shm/pa194-fully-closed-replay:/dev/shm/pa194-model-separation-full-replay:/dev/shm/pa194-model-separation-seeded-replay:/dev/shm/pa194-model-closure-definability-replay:/dev/shm/pa194-model-closure-replay:/dev/shm/pa194-general-separation-repo:/dev/shm/pa194-ranked-open-separation-repo:/dev/shm/pa194-general-separation-replay:/dev/shm/pa194-ranked-open-separation-replay-v3:/dev/shm/pa194-unrestricted-all-replay:/dev/shm/pa194-adjunctive-admission-audit:/dev/shm/pa194-full-one-level-audit:/tmp/current14-standard-fresh-build-20261104/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib:$lake_path"
for name in PA194InternalBaseAtContext PA194InternalStepAtContext; do
 lean -j1 -M 4000 -R "$src" -o "$out/$name.olean" "$src/$name.lean" > "$out/$name.log" 2>&1
 if rg -q "sorryAx|declaration uses 'sorry'" "$out/$name.log"; then cat "$out/$name.log"; exit 1; fi
 cat "$out/$name.log"
done
[[ $(rg -c 'depends on axioms:' "$out/PA194InternalBaseAtContext.log") == 2 ]]
[[ $(rg -c 'depends on axioms:' "$out/PA194InternalStepAtContext.log") == 3 ]]
check_inputs
echo 'PASS: internal base and step application under arbitrary source context; dependencies prebuilt.'
