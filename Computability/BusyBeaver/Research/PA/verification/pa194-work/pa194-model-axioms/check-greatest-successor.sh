#!/usr/bin/env bash
set -euo pipefail
if (($# != 2)); then echo 'usage: REPO NEW_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); out=$(realpath -m "$2"); src=$(cd "$(dirname "$0")" && pwd)
[[ ! -e "$out" ]] || { echo 'Output exists' >&2; exit 2; }
check_inputs() {
 printf '%s  %s\n' \
 fe732761208d3aa067ef894cf600083fbceeabf278afb02385b58c1dde0a6f8d "$src/PA194GreatestSuccessorClosedTemplate.lean" \
 62ba7892c7eb6a2641aa5bd5d277560863e39d15ef6f7c0bcc7a9dd8372bfcb6 "$src/PA194GreatestSuccessorClosedModel.lean" \
 c94aa867932b9b4ed48ca9061583834cc5277365863a0acff32ccbe42ac1b3f5 "$src/PA194GreatestSuccessorAtCode.lean" \
 bbe1510f9ce6b912b42e695b90bec5f049b6c30172243e416043a00d0c6ec06a /dev/shm/pa194-least-excludes-closed-repo/PA194LeastExcludesClosedModel.olean \
 e4e15431b3a62e213f3e02145bd9638aff6f71651163f404265adf15f6c5bf47 /dev/shm/pa194-domain-instances-repo/PA194DomainInstances.olean \
 8f748362231d253b73dbd4fe13ce956398ae84205bced73556ff12c9f2f85a4d /dev/shm/pa194-ordinal-step-application-code-repo/PA194ContextDoubleSpecializeCode.olean | sha256sum -c -
}
check_inputs
mkdir -p "$out"
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$out:/dev/shm/pa194-least-excludes-at-repo:/dev/shm/pa194-domain-instances-repo:/dev/shm/pa194-member-domain-at-repo:/dev/shm/pa194-member-domain-closed-repo:/dev/shm/pa194-trace-member-forward-repo:/dev/shm/pa194-expanded-trace-at-repo:/dev/shm/pa194-separation-trace-open-repo:/dev/shm/pa194-context-projections-contradiction-repo:/dev/shm/pa194-context-triple-specialize-repo:/dev/shm/pa194-least-excludes-closed-repo:/dev/shm/pa194-full-sep-witness-branch-repo:/dev/shm/pa194-separation-witness-from-root-repo:/dev/shm/pa194-separation-trace-witness-repo:/dev/shm/pa194-separation-trace-shift-repo:/dev/shm/pa194-separation-trace-at-code-repo:/dev/shm/pa194-context-exs-witness-repo:/dev/shm/pa194-context-quantifier-code-repo:/dev/shm/pa194-ordinal-step-application-code-repo:/dev/shm/pa194-context-specialize-code-repo:/dev/shm/pa194-context-mp-code-repo:/dev/shm/pa194-context-conjunction-code-repo:/dev/shm/pa194-context-shift-code-repo:/dev/shm/pa194-internal-separation-shift-repo:/dev/shm/pa194-empty-source-proof-repo:/dev/shm/pa194-congruence-source-proof-repo:/dev/shm/pa194-standard-equality-suppliers-repo:/dev/shm/pa194-ordinal-suppliers-repo:/dev/shm/pa194-standard-ordinal-reduction-repo:/dev/shm/pa194-intersection-proof-repo:/dev/shm/pa194-full-sep-open-repo:/dev/shm/pa194-full-sep-theory-replay:/dev/shm/pa194-standard-no-free-replay:/dev/shm/pa194-closed-sep-classifier-replay:/dev/shm/pa194-fairness-full-source-replay:/dev/shm/pa194-generic-sim-replay:/dev/shm/pa194-adjunctive-sim-v2-replay:/dev/shm/pa194-shift-interface-replay:/dev/shm/pa194-unrestricted-existential-v2-replay:/dev/shm/pa194-qf-ranked-existential-audit:/dev/shm/pa194-general-shift-replay:/dev/shm/pa194-general-reverse-shift-replay:/dev/shm/pa194-general-freshness-audit:/dev/shm/pa194-observational-general-audit:/dev/shm/pa194-quoted-induction-repo:/dev/shm/pa194-reopen-proof-repo:/dev/shm/pa194-close-proof-repo:/dev/shm/pa194-uniform-fully-closed-repo:/dev/shm/pa194-uniform-closure-replay:/dev/shm/pa194-unclose-envelope-replay:/dev/shm/pa194-separation-trace-open-repo:/dev/shm/pa194-separation-trace-witness-repo:/dev/shm/pa194-separation-trace-shift-repo:/dev/shm/pa194-context-exs-witness-repo:/dev/shm/pa194-context-quantifier-code-repo:/dev/shm/pa194-separation-trace-at-code-repo:/dev/shm/pa194-induction-step-shift-repo:/dev/shm/pa194-uniform-sep-combined-repo:/dev/shm/pa194-separation-shift-code-repo:/dev/shm/pa194-internal-induction-at-context-repo:/dev/shm/pa194-context-specialize-code-repo:/dev/shm/pa194-context-mp-code-repo:/dev/shm/pa194-context-conjunction-code-repo:/dev/shm/pa194-context-shift-code-repo:/dev/shm/pa194-internal-separation-shift-repo:/dev/shm/pa194-internal-induction-base-at-repo:/dev/shm/pa194-induction-base-shift-repo:/dev/shm/pa194-ordinal-uniform-repo:/dev/shm/pa194-ordinal-fixed-repo:/dev/shm/pa194-ordinal-induction-code-repo:/dev/shm/pa194-ordinal-statement-repo:/dev/shm/pa194-typed-schema-repo:/dev/shm/pa194-fully-closed-repo:/dev/shm/pa194-fully-closed-replay:/dev/shm/pa194-model-separation-full-replay:/dev/shm/pa194-model-separation-seeded-replay:/dev/shm/pa194-model-closure-definability-replay:/dev/shm/pa194-model-closure-replay:/dev/shm/pa194-general-separation-repo:/dev/shm/pa194-ranked-open-separation-repo:/dev/shm/pa194-general-separation-replay:/dev/shm/pa194-ranked-open-separation-replay-v3:/dev/shm/pa194-unrestricted-all-replay:/dev/shm/pa194-adjunctive-admission-audit:/dev/shm/pa194-full-one-level-audit:/tmp/current14-standard-fresh-build-20261104/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib:$lake_path"
for name in PA194GreatestSuccessorClosedTemplate PA194GreatestSuccessorClosedModel PA194GreatestSuccessorAtCode; do
 lean -j1 -M 4000 -R "$src" -o "$out/$name.olean" "$src/$name.lean" > "$out/$name.log" 2>&1
 if rg -q "sorryAx|declaration uses 'sorry'" "$out/$name.log"; then cat "$out/$name.log"; exit 1; fi
 cat "$out/$name.log"
done
[[ $(rg -c 'depends on axioms:' "$out/PA194GreatestSuccessorClosedTemplate.log") == 4 ]]
[[ $(rg -c 'depends on axioms:' "$out/PA194GreatestSuccessorClosedModel.log") == 4 ]]
[[ $(rg -c 'depends on axioms:' "$out/PA194GreatestSuccessorAtCode.log") == 7 ]]
check_inputs
echo 'PASS: greatest member gives raw successor; dependencies prebuilt.'
