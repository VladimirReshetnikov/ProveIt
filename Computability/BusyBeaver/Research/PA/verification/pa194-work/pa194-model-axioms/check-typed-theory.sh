#!/usr/bin/env bash
set -euo pipefail
if (($# != 5)); then echo 'usage: REPO NAT_BASE TYPED_CLASS_BASE DECODE_BASE NEW_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); nat=$(realpath "$2"); typed=$(realpath "$3"); decode=$(realpath "$4"); out=$(realpath -m "$5")
src=$(cd "$(dirname "$0")" && pwd)
[[ ! -e "$out" ]] || { echo 'Output exists' >&2; exit 2; }
check_inputs() {
 printf '%s  %s\n' \
 c717b9c063ef586c0de2fd6496d13ca4371fa624bbae66abf2798ec76206392d "$src/PA194NatQuoteBridge.lean" \
 4053dcb0ed95b5056144e838a6806646f8326387cfb78edbc90669ba42ecb73a "$src/PA194TypedTheory.lean" \
 93c08411d8ee47100a710c1af41198b451dd8662bb430c39b1d517956de8021d "$src/PA194TypedTheoryAudit.lean" \
 7a8d354e8d788e8fb83def4940b29a40d61433116e5c7f98c32980aa1c324a07 "$nat/PA194NatStructureBridge.olean" \
 217d8fe379c4e4a5d23314aaeda2182531fa7c08707b6b7f0181c8b8ea0a6553 "$typed/PA194TypedClass.olean" \
 24252067ae17be2403934f2fa636712433cf0d78c50e54accc040f64e83f5c79 "$decode/PA194ModelStandardSourceDecode.olean" | sha256sum -c -
}
check_inputs
mkdir -p "$out"
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$out:$nat:$typed:$decode:/dev/shm/pa194-typed-schema-replay:/dev/shm/pa194-full-sep-theory-replay:/dev/shm/pa194-unclose-envelope-replay:/dev/shm/pa194-uniform-fully-closed-replay:/dev/shm/pa194-uniform-closure-replay:/dev/shm/pa194-fully-closed-replay:/dev/shm/pa194-model-separation-full-replay:/dev/shm/pa194-model-separation-seeded-replay:/dev/shm/pa194-model-closure-definability-replay:/dev/shm/pa194-model-closure-replay:/dev/shm/pa194-general-separation-replay:/dev/shm/pa194-ranked-open-separation-replay-v3:/dev/shm/pa194-closed-sep-theory-replay:/dev/shm/pa194-uniform-sep-combined-replay:/dev/shm/pa194-standard-no-free-replay:/dev/shm/pa194-closed-sep-classifier-replay:/dev/shm/pa194-fairness-full-source-replay:/dev/shm/pa194-generic-sim-replay:/dev/shm/pa194-adjunctive-sim-v2-replay:/dev/shm/pa194-shift-interface-replay:/dev/shm/pa194-unrestricted-existential-v2-replay:/dev/shm/pa194-qf-ranked-existential-audit:/dev/shm/pa194-adjunctive-admission-audit:/dev/shm/pa194-general-shift-replay:/dev/shm/pa194-general-reverse-shift-replay:/dev/shm/pa194-unrestricted-all-replay:/dev/shm/pa194-general-freshness-audit:/dev/shm/pa194-observational-general-audit:/dev/shm/pa194-full-one-level-audit:/tmp/current14-standard-fresh-build-20261104/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib:$lake_path"
for n in PA194NatQuoteBridge PA194TypedTheory PA194TypedTheoryAudit; do
 echo "Checking $n"
 lean -j1 -M 4000 -R "$src" -o "$out/$n.olean" "$src/$n.lean" > "$out/$n.log" 2>&1
 if rg -q "sorryAx|declaration uses 'sorry'" "$out/$n.log"; then cat "$out/$n.log"; exit 1; fi
done
[[ $(rg -c 'depends on axioms:' "$out/PA194TypedTheoryAudit.log") == 8 ]]
cat "$out/PA194TypedTheoryAudit.log"
check_inputs
echo 'PASS: standard full separation theory equals the typed universally closed schema; staged dependencies prebuilt.'
