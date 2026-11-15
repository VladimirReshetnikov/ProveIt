#!/usr/bin/env bash
set -euo pipefail
if (($# != 2)); then echo 'usage: REPO NEW_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); out=$(realpath -m "$2"); src=$(cd "$(dirname "$0")" && pwd)
[[ ! -e "$out" ]] || { echo 'Output exists' >&2; exit 2; }
check_inputs() {
 printf '%s  %s\n' \
 1ceee5a8500530a6858ba6e565ca4104c578adb851f345c256b19ef728987fb3 "$src/PA194InductionPackaging.lean" \
 54a3a34cfa4019df7711492d5617fe2c3de115d3e617b8c308af41ae23817b5f /dev/shm/pa194-ordinal-fixed-repo/PA194OrdinalFixed.olean \
 1e7bc847150dadda7ce38bac70da1e5c949afb3314c2951ec9eeb401674d8fe7 /dev/shm/pa194-ordinal-induction-code-repo/PA194OrdinalStatementFromProperty.olean \
 0e9e340bff69ad49f9407129526b22c54be14605d168532ff3cf07e93fc43f7d /dev/shm/pa194-ordinal-statement-repo/PA194InternalOrdinalStatement.olean \
 710078440560e2a21b8980d4e5b08b9801b38cf4c90771364f7989a57612c0c2 /dev/shm/pa194-typed-schema-repo/PA194TypedSchema.olean | sha256sum -c -
}
check_inputs
mkdir -p "$out"
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$out:/dev/shm/pa194-ordinal-fixed-repo:/dev/shm/pa194-ordinal-induction-code-repo:/dev/shm/pa194-ordinal-statement-repo:/dev/shm/pa194-typed-schema-repo:/dev/shm/pa194-fully-closed-replay:/dev/shm/pa194-model-separation-full-replay:/dev/shm/pa194-model-separation-seeded-replay:/dev/shm/pa194-model-closure-definability-replay:/dev/shm/pa194-model-closure-replay:/dev/shm/pa194-general-separation-replay:/dev/shm/pa194-ranked-open-separation-replay-v3:/dev/shm/pa194-unrestricted-all-replay:/dev/shm/pa194-adjunctive-admission-audit:/dev/shm/pa194-full-one-level-audit:/tmp/current14-standard-fresh-build-20261104/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib:$lake_path"
lean -j1 -M 4000 -R "$src" -o "$out/PA194InductionPackaging.olean" "$src/PA194InductionPackaging.lean" > "$out/check.log" 2>&1
if rg -q "sorryAx|declaration uses 'sorry'" "$out/check.log"; then cat "$out/check.log"; exit 1; fi
[[ $(rg -c 'depends on axioms:' "$out/check.log") == 3 ]]
cat "$out/check.log"
check_inputs
echo 'PASS: conditional induction sequent packaging; sequent derivability remains a hypothesis.'
