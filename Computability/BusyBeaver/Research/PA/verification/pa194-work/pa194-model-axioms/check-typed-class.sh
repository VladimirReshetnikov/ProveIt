#!/usr/bin/env bash
set -euo pipefail
if (($# != 4)); then echo 'usage: REPO TYPED_BASE CLASSIFIER_BASE NEW_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); typed=$(realpath "$2"); cls=$(realpath "$3"); out=$(realpath -m "$4")
src=$(cd "$(dirname "$0")" && pwd)
[[ ! -e "$out" ]] || { echo 'Output exists' >&2; exit 2; }
check_inputs() {
 printf '%s  %s\n' \
 ddcde5862b66021a997756ef18dbe7b87ee8a1d06c3c46a74659e0dbe9c39555 "$src/PA194TypedClass.lean" \
 710078440560e2a21b8980d4e5b08b9801b38cf4c90771364f7989a57612c0c2 "$typed/PA194TypedSchema.olean" \
 ad567ad36b035e5408670694f8bf137e6b00e2682954157b80e5eae4752df502 "$cls/PA194FullSepTheoryModel.olean" | sha256sum -c -
}
check_inputs
mkdir -p "$out"
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$out:$typed:$cls:/dev/shm/pa194-unclose-envelope-replay:/dev/shm/pa194-uniform-fully-closed-replay:/dev/shm/pa194-uniform-closure-replay:/dev/shm/pa194-fully-closed-replay:/dev/shm/pa194-model-separation-full-replay:/dev/shm/pa194-model-separation-seeded-replay:/dev/shm/pa194-model-closure-definability-replay:/dev/shm/pa194-model-closure-replay:/dev/shm/pa194-general-separation-replay:/dev/shm/pa194-ranked-open-separation-replay-v3:/dev/shm/pa194-closed-sep-theory-replay:/dev/shm/pa194-uniform-sep-combined-replay:/dev/shm/pa194-standard-no-free-replay:/dev/shm/pa194-closed-sep-classifier-replay:/dev/shm/pa194-fairness-full-source-replay:/dev/shm/pa194-generic-sim-replay:/dev/shm/pa194-adjunctive-sim-v2-replay:/dev/shm/pa194-shift-interface-replay:/dev/shm/pa194-unrestricted-existential-v2-replay:/dev/shm/pa194-qf-ranked-existential-audit:/dev/shm/pa194-adjunctive-admission-audit:/dev/shm/pa194-general-shift-replay:/dev/shm/pa194-general-reverse-shift-replay:/dev/shm/pa194-unrestricted-all-replay:/dev/shm/pa194-general-freshness-audit:/dev/shm/pa194-observational-general-audit:/dev/shm/pa194-full-one-level-audit:/tmp/current14-standard-fresh-build-20261104/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib:$lake_path"
lean -j1 -M 4000 -R "$src" -o "$out/PA194TypedClass.olean" "$src/PA194TypedClass.lean" > "$out/check.log" 2>&1
if rg -q "sorryAx|declaration uses 'sorry'" "$out/check.log"; then cat "$out/check.log"; exit 1; fi
[[ $(rg -c 'depends on axioms:' "$out/check.log") == 1 ]]
cat "$out/check.log"
check_inputs
echo 'PASS: typed classifier under explicit internal-code quotation surjectivity; staged dependencies prebuilt.'
