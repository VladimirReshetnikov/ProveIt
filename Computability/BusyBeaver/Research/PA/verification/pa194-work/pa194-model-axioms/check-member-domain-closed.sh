#!/usr/bin/env bash
set -euo pipefail
if (($# != 2)); then echo 'usage: REPO NEW_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); out=$(realpath -m "$2"); src=$(cd "$(dirname "$0")" && pwd)
[[ ! -e "$out" ]] || { echo 'Output exists' >&2; exit 2; }
check_inputs() {
 printf '%s  %s\n' \
 f65b2104d87d4c7554a8f0f63cc9c9acc6765342c4bf414aeaeb149d8176f164 "$src/PA194MemberDomainClosedTemplate.lean" \
 863338c4e3c4c8942e7fca990bfaf5215a1896fae3cc49533b0a939291b61512 "$src/PA194MemberDomainClosedModel.lean" \
 45054ae4bd07e96cb66b086c072b1b2bd7d1ed459ffb60c90f95c87d673a56c4 /dev/shm/pa194-quoted-induction-repo/PA194QuotedInduction.olean \
 0df67b746684916c848df4214feca0aed94e559f87265645a3e776b5f148cac7 /dev/shm/pa194-close-proof-repo/PA194CloseProof.olean \
 24e755bcb503e88dc5748ea4420be262a174eae08dd7a5b6860ad646d3c7fee2 /dev/shm/pa194-full-one-level-audit/PA194FoundationOrdinalInductionMembers.olean | sha256sum -c -
}
check_inputs
mkdir -p "$out"
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$out:/dev/shm/pa194-quoted-induction-repo:/dev/shm/pa194-reopen-proof-repo:/dev/shm/pa194-close-proof-repo:/dev/shm/pa194-uniform-fully-closed-repo:/dev/shm/pa194-uniform-closure-replay:/dev/shm/pa194-unclose-envelope-replay:/dev/shm/pa194-separation-trace-open-repo:/dev/shm/pa194-separation-trace-witness-repo:/dev/shm/pa194-separation-trace-shift-repo:/dev/shm/pa194-context-exs-witness-repo:/dev/shm/pa194-context-quantifier-code-repo:/dev/shm/pa194-separation-trace-at-code-repo:/dev/shm/pa194-induction-step-shift-repo:/dev/shm/pa194-uniform-sep-combined-repo:/dev/shm/pa194-separation-shift-code-repo:/dev/shm/pa194-internal-induction-at-context-repo:/dev/shm/pa194-context-specialize-code-repo:/dev/shm/pa194-context-mp-code-repo:/dev/shm/pa194-context-conjunction-code-repo:/dev/shm/pa194-context-shift-code-repo:/dev/shm/pa194-internal-separation-shift-repo:/dev/shm/pa194-internal-induction-base-at-repo:/dev/shm/pa194-induction-base-shift-repo:/dev/shm/pa194-ordinal-uniform-repo:/dev/shm/pa194-ordinal-fixed-repo:/dev/shm/pa194-ordinal-induction-code-repo:/dev/shm/pa194-ordinal-statement-repo:/dev/shm/pa194-typed-schema-repo:/dev/shm/pa194-fully-closed-repo:/dev/shm/pa194-fully-closed-replay:/dev/shm/pa194-model-separation-full-replay:/dev/shm/pa194-model-separation-seeded-replay:/dev/shm/pa194-model-closure-definability-replay:/dev/shm/pa194-model-closure-replay:/dev/shm/pa194-general-separation-repo:/dev/shm/pa194-ranked-open-separation-repo:/dev/shm/pa194-general-separation-replay:/dev/shm/pa194-ranked-open-separation-replay-v3:/dev/shm/pa194-unrestricted-all-replay:/dev/shm/pa194-adjunctive-admission-audit:/dev/shm/pa194-full-one-level-audit:/tmp/current14-standard-fresh-build-20261104/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib:$lake_path"
for name in PA194MemberDomainClosedTemplate PA194MemberDomainClosedModel; do
 lean -j1 -M 4000 -R "$src" -o "$out/$name.olean" "$src/$name.lean" > "$out/$name.log" 2>&1
 if rg -q "sorryAx|declaration uses 'sorry'" "$out/$name.log"; then cat "$out/$name.log"; exit 1; fi
 cat "$out/$name.log"
done
[[ $(rg -c 'depends on axioms:' "$out/PA194MemberDomainClosedTemplate.log") == 4 ]]
[[ $(rg -c 'depends on axioms:' "$out/PA194MemberDomainClosedModel.log") == 5 ]]
check_inputs
echo 'PASS: fixed universal member-domain internal derivation; dependencies prebuilt.'
