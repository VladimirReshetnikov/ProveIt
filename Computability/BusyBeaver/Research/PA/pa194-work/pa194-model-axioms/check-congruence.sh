#!/usr/bin/env bash
set -euo pipefail
if (($# != 2)); then echo 'usage: REPO NEW_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); out=$(realpath -m "$2"); src=$(cd "$(dirname "$0")" && pwd)
[[ ! -e "$out" ]] || { echo 'Output exists' >&2; exit 2; }
check_inputs() {
 printf '%s  %s\n' \
 9bbc835f59ff814182a8bb52681f2e48a48c0634b2cfb21659fceb83f4ca874d "$src/PA194CongruenceFromRelExt.lean" \
 63ce05ccd31cc4a0e5c2756e1d75e1230e5f5ee818daeaf8f6520a0d3b75edae "$src/PA194CongruenceSourceProof.lean" \
 4590f87bc45dd46294d15f5e58c724e902bd3045b7350c45ec2ef3bab84dee65 /dev/shm/pa194-empty-source-proof-repo/PA194EmptySourceProof.olean \
 f7bb15cbd1c7f9c7de236d8903ce89854296ddd64ddaafd767c08b32c3a63fad /dev/shm/pa194-standard-equality-suppliers-repo/PA194StandardEqualitySuppliers.olean | sha256sum -c -
}
check_inputs
mkdir -p "$out"
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
baselines="/dev/shm/pa194-unclose-envelope-replay:/dev/shm/pa194-uniform-fully-closed-replay:/dev/shm/pa194-uniform-closure-replay:/dev/shm/pa194-fully-closed-replay:/dev/shm/pa194-model-separation-full-replay:/dev/shm/pa194-model-separation-seeded-replay:/dev/shm/pa194-model-closure-definability-replay:/dev/shm/pa194-model-closure-replay:/dev/shm/pa194-general-separation-replay:/dev/shm/pa194-ranked-open-separation-replay-v3:/dev/shm/pa194-closed-sep-theory-replay:/dev/shm/pa194-uniform-sep-combined-replay:/dev/shm/pa194-standard-no-free-replay:/dev/shm/pa194-closed-sep-classifier-replay:/dev/shm/pa194-fairness-full-source-replay:/dev/shm/pa194-generic-sim-replay:/dev/shm/pa194-adjunctive-sim-v2-replay:/dev/shm/pa194-shift-interface-replay:/dev/shm/pa194-unrestricted-existential-v2-replay:/dev/shm/pa194-qf-ranked-existential-audit:/dev/shm/pa194-adjunctive-admission-audit:/dev/shm/pa194-general-shift-replay:/dev/shm/pa194-general-reverse-shift-replay:/dev/shm/pa194-unrestricted-all-replay:/dev/shm/pa194-general-freshness-audit:/dev/shm/pa194-observational-general-audit:/dev/shm/pa194-full-one-level-audit"
export LEAN_PATH="$out:/dev/shm/pa194-empty-source-proof-repo:/dev/shm/pa194-standard-equality-suppliers-repo:/dev/shm/pa194-standard-ordinal-reduction-repo:/dev/shm/pa194-quoted-induction-repo:/dev/shm/pa194-ordinal-suppliers-repo:/dev/shm/pa194-ordinal-fixed-repo:/dev/shm/pa194-ordinal-induction-code-repo:/dev/shm/pa194-ordinal-statement-repo:/dev/shm/pa194-intersection-proof-repo:/dev/shm/pa194-full-sep-open-repo:/dev/shm/pa194-typed-schema-replay:/dev/shm/pa194-reopen-proof-replay:/dev/shm/pa194-full-sep-theory-replay:$baselines:/tmp/current14-standard-fresh-build-20261104/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib:$lake_path"
for name in PA194CongruenceFromRelExt PA194CongruenceSourceProof; do
 lean -j1 -M 5000 -R "$src" -o "$out/$name.olean" "$src/$name.lean" > "$out/$name.log" 2>&1
 if rg -q "sorryAx|declaration uses 'sorry'" "$out/$name.log"; then cat "$out/$name.log"; exit 1; fi
 cat "$out/$name.log"
done
[[ $(rg -c 'depends on axioms:' "$out/PA194CongruenceFromRelExt.log") == 1 ]]
[[ $(rg -c 'depends on axioms:' "$out/PA194CongruenceSourceProof.log") == 3 ]]
check_inputs
echo 'PASS: internal congruence proof and one-premise ordinal reduction; dependencies prebuilt.'
