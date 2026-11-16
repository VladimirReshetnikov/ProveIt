#!/usr/bin/env bash
set -euo pipefail
if (($# != 2)); then echo 'usage: REPO NEW_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); out=$(realpath -m "$2"); src=$(cd "$(dirname "$0")" && pwd)
[[ ! -e "$out" ]] || { echo 'Output exists' >&2; exit 2; }
check_inputs() {
 printf '%s  %s\n' \
 35d1d3200ce4b793a11823f893490b90d7762b1ff6bcb73022dffa3a75a35177 "$src/PA194FiniteDischarge.lean" \
 78fc2762405942412aa29595de67c06d5fe2f6c21b2898638d7df500561287af "$src/PA194QuotedInduction.lean" \
 54a3a34cfa4019df7711492d5617fe2c3de115d3e617b8c308af41ae23817b5f /dev/shm/pa194-ordinal-fixed-repo/PA194OrdinalFixed.olean \
 faae8469e628599a0744e01a790b819ac0c6b234fb5cc6a4207f9cb0c9a5435e /dev/shm/pa194-adjunctive-admission-audit/PA194FoundationOrdinalInductionNumeric.olean | sha256sum -c -
}
check_inputs
mkdir -p "$out"
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$out:/dev/shm/pa194-ordinal-fixed-repo:/dev/shm/pa194-ordinal-induction-code-repo:/dev/shm/pa194-ordinal-statement-repo:/dev/shm/pa194-typed-schema-repo:/dev/shm/pa194-fully-closed-replay:/dev/shm/pa194-model-separation-full-replay:/dev/shm/pa194-model-separation-seeded-replay:/dev/shm/pa194-model-closure-definability-replay:/dev/shm/pa194-model-closure-replay:/dev/shm/pa194-general-separation-replay:/dev/shm/pa194-ranked-open-separation-replay-v3:/dev/shm/pa194-unrestricted-all-replay:/dev/shm/pa194-adjunctive-admission-audit:/dev/shm/pa194-full-one-level-audit:/tmp/current14-standard-fresh-build-20261104/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib:$lake_path"
for name in PA194FiniteDischarge PA194QuotedInduction; do
 lean -j1 -M 4000 -R "$src" -o "$out/$name.olean" "$src/$name.lean" > "$out/$name.log" 2>&1
 if rg -q "sorryAx|declaration uses 'sorry'" "$out/$name.log"; then cat "$out/$name.log"; exit 1; fi
 cat "$out/$name.log"
done
[[ $(rg -c 'depends on axioms:' "$out/PA194FiniteDischarge.log") == 1 ]]
[[ $(rg -c 'depends on axioms:' "$out/PA194QuotedInduction.log") == 3 ]]
check_inputs
echo 'PASS: quoted standard ordinal derivation with explicit finite-context proof premises; dependencies prebuilt.'
