#!/usr/bin/env bash
set -euo pipefail
if (($# != 2)); then echo 'usage: REPO NEW_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); out=$(realpath -m "$2"); src=$(cd "$(dirname "$0")" && pwd)
[[ ! -e "$out" ]] || { echo 'Output exists' >&2; exit 2; }
check_inputs() {
 printf '%s  %s\n' \
 dfab5634f54f8eb994dbd8bad647ad31cbfe18cd08e9cb4bead5042a5de08d63 "$src/PA194IntersectionTyped.lean" \
 9bfaf52a56eb244c3070c1a69c23f98e8dd3fcf8bd835262cd86915fa50a4388 "$src/PA194TypedSepMember.lean" \
 6caa6e744b17e515bb24d4dcac84665912c3e48d9d5130e7dfc0b10eb8d70d33 "$src/PA194IntersectionMember.lean" \
 06342862587a5cfb45b7ee420df127bbef09928d697fcdb8e97fdda1586874d5 /dev/shm/pa194-full-sep-open-repo/PA194FullSepOpen.olean \
 710078440560e2a21b8980d4e5b08b9801b38cf4c90771364f7989a57612c0c2 /dev/shm/pa194-typed-schema-replay/PA194TypedSchema.olean | sha256sum -c -
}
check_inputs
mkdir -p "$out"
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
baselines="/dev/shm/pa194-unclose-envelope-replay:/dev/shm/pa194-uniform-fully-closed-replay:/dev/shm/pa194-uniform-closure-replay:/dev/shm/pa194-fully-closed-replay:/dev/shm/pa194-model-separation-full-replay:/dev/shm/pa194-model-separation-seeded-replay:/dev/shm/pa194-model-closure-definability-replay:/dev/shm/pa194-model-closure-replay:/dev/shm/pa194-general-separation-replay:/dev/shm/pa194-ranked-open-separation-replay-v3:/dev/shm/pa194-closed-sep-theory-replay:/dev/shm/pa194-uniform-sep-combined-replay:/dev/shm/pa194-standard-no-free-replay:/dev/shm/pa194-closed-sep-classifier-replay:/dev/shm/pa194-fairness-full-source-replay:/dev/shm/pa194-generic-sim-replay:/dev/shm/pa194-adjunctive-sim-v2-replay:/dev/shm/pa194-shift-interface-replay:/dev/shm/pa194-unrestricted-existential-v2-replay:/dev/shm/pa194-qf-ranked-existential-audit:/dev/shm/pa194-adjunctive-admission-audit:/dev/shm/pa194-general-shift-replay:/dev/shm/pa194-general-reverse-shift-replay:/dev/shm/pa194-unrestricted-all-replay:/dev/shm/pa194-general-freshness-audit:/dev/shm/pa194-observational-general-audit:/dev/shm/pa194-full-one-level-audit"
export LEAN_PATH="$out:/dev/shm/pa194-full-sep-open-repo:/dev/shm/pa194-typed-schema-replay:/dev/shm/pa194-reopen-proof-replay:/dev/shm/pa194-full-sep-theory-replay:$baselines:/tmp/current14-standard-fresh-build-20261104/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib:$lake_path"
for name in PA194IntersectionTyped PA194TypedSepMember PA194IntersectionMember; do
 lean -j1 -M 5000 -R "$src" -o "$out/$name.olean" "$src/$name.lean" > "$out/$name.log" 2>&1
 if rg -q "sorryAx|declaration uses 'sorry'" "$out/$name.log"; then cat "$out/$name.log"; exit 1; fi
 cat "$out/$name.log"
done
[[ $(rg -c 'depends on axioms:' "$out/PA194IntersectionTyped.log") == 1 ]]
[[ $(rg -c 'depends on axioms:' "$out/PA194TypedSepMember.log") == 1 ]]
[[ $(rg -c 'depends on axioms:' "$out/PA194IntersectionMember.log") == 2 ]]
check_inputs
echo 'PASS: source intersection is an axiom and provable in the classifier-defined union; dependencies prebuilt.'
