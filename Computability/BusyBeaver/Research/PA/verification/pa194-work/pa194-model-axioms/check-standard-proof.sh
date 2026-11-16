#!/usr/bin/env bash
set -euo pipefail
if (($# != 2)); then echo 'usage: REPO NEW_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); out=$(realpath -m "$2"); src=$(cd "$(dirname "$0")" && pwd)
[[ ! -e "$out" ]] || { echo 'Output exists' >&2; exit 2; }
check_inputs() {
 printf '%s  %s\n' \
 1aba9e3ac47323041001532104b2948e0372716e9476b3efd549df91e0bdd69c "$src/PA194AdjunctionSourceSyntax.lean" \
 40f39b58025050aeb69a77571e377da408f9cf2c66b9f257a782e96909c111a5 "$src/PA194AdjunctionOpenProof.lean" \
 0beacc40be43ebdb56e32c2f9a396339a770762962e34a353d11e418d04b9c8e "$src/PA194AdjunctionClosureTyped.lean" \
 a970d578785744791d9db5a79a4c853cb0e307f52b49327561c0a8dbe64fb147 "$src/PA194StandardOrdinalProof.lean" \
 0df67b746684916c848df4214feca0aed94e559f87265645a3e776b5f148cac7 /dev/shm/pa194-close-proof-repo/PA194CloseProof.olean \
 efc0d1437a7eb574404a0e550e69807cc6a7cee75e9db5d78f87b8a3a593d45d /dev/shm/pa194-congruence-source-proof-repo/PA194CongruenceSourceProof.olean \
 33d1b680a64ca5bec5c4e15f978576f287ff96c46c3f0c08152f710266237b09 /dev/shm/pa194-ordinal-closed-repo/PA194OrdinalClosed.olean | sha256sum -c -
}
check_inputs
mkdir -p "$out"
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
baselines="/dev/shm/pa194-unclose-envelope-replay:/dev/shm/pa194-uniform-fully-closed-replay:/dev/shm/pa194-uniform-closure-replay:/dev/shm/pa194-fully-closed-replay:/dev/shm/pa194-model-separation-full-replay:/dev/shm/pa194-model-separation-seeded-replay:/dev/shm/pa194-model-closure-definability-replay:/dev/shm/pa194-model-closure-replay:/dev/shm/pa194-general-separation-replay:/dev/shm/pa194-ranked-open-separation-replay-v3:/dev/shm/pa194-closed-sep-theory-replay:/dev/shm/pa194-uniform-sep-combined-replay:/dev/shm/pa194-standard-no-free-replay:/dev/shm/pa194-closed-sep-classifier-replay:/dev/shm/pa194-fairness-full-source-replay:/dev/shm/pa194-generic-sim-replay:/dev/shm/pa194-adjunctive-sim-v2-replay:/dev/shm/pa194-shift-interface-replay:/dev/shm/pa194-unrestricted-existential-v2-replay:/dev/shm/pa194-qf-ranked-existential-audit:/dev/shm/pa194-adjunctive-admission-audit:/dev/shm/pa194-general-shift-replay:/dev/shm/pa194-general-reverse-shift-replay:/dev/shm/pa194-unrestricted-all-replay:/dev/shm/pa194-general-freshness-audit:/dev/shm/pa194-observational-general-audit:/dev/shm/pa194-full-one-level-audit"
export LEAN_PATH="$out:/dev/shm/pa194-ordinal-closed-repo:/dev/shm/pa194-ordinal-uniform-repo:/dev/shm/pa194-close-proof-repo:/dev/shm/pa194-congruence-source-proof-repo:/dev/shm/pa194-empty-source-proof-repo:/dev/shm/pa194-standard-equality-suppliers-repo:/dev/shm/pa194-standard-ordinal-reduction-repo:/dev/shm/pa194-quoted-induction-repo:/dev/shm/pa194-ordinal-suppliers-repo:/dev/shm/pa194-ordinal-fixed-repo:/dev/shm/pa194-ordinal-induction-code-repo:/dev/shm/pa194-ordinal-statement-repo:/dev/shm/pa194-intersection-proof-repo:/dev/shm/pa194-full-sep-open-repo:/dev/shm/pa194-typed-schema-replay:/dev/shm/pa194-reopen-proof-replay:/dev/shm/pa194-full-sep-theory-replay:$baselines:/tmp/current14-standard-fresh-build-20261104/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib:$lake_path"
for name in PA194AdjunctionSourceSyntax PA194AdjunctionOpenProof PA194AdjunctionClosureTyped PA194StandardOrdinalProof; do
 lean -j1 -M 5000 -R "$src" -o "$out/$name.olean" "$src/$name.lean" > "$out/$name.log" 2>&1
 if rg -q "sorryAx|declaration uses 'sorry'" "$out/$name.log"; then cat "$out/$name.log"; exit 1; fi
 cat "$out/$name.log"
done
[[ $(rg -c 'depends on axioms:' "$out/PA194AdjunctionSourceSyntax.log") == 3 ]]
[[ $(rg -c 'depends on axioms:' "$out/PA194AdjunctionOpenProof.log") == 3 ]]
[[ $(rg -c 'depends on axioms:' "$out/PA194AdjunctionClosureTyped.log") == 1 ]]
[[ $(rg -c 'depends on axioms:' "$out/PA194StandardOrdinalProof.log") == 4 ]]
check_inputs
echo 'PASS: internal open and closed ordinal induction for all standard typed properties; dependencies prebuilt.'
