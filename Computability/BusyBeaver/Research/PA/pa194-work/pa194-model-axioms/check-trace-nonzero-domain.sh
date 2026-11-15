#!/usr/bin/env bash
set -euo pipefail
if (($# != 2)); then echo 'usage: REPO NEW_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); out=$(realpath -m "$2"); src=$(cd "$(dirname "$0")" && pwd)
[[ ! -e "$out" ]] || { echo 'Output exists' >&2; exit 2; }
check_inputs() {
 printf '%s  %s\n' \
 a2310899d3cd425354e080db795219b1048117e6c692585faab84b82adbceba2 "$src/PA194TraceNonzeroFromDomain.lean" \
 e4e15431b3a62e213f3e02145bd9638aff6f71651163f404265adf15f6c5bf47 /dev/shm/pa194-domain-instances-repo/PA194DomainInstances.olean \
 351fd896ec95f4b37f836f5409aba2b0f7738745a26add47c43de0312259d680 /dev/shm/pa194-trace-bad-not-zero-repo/PA194TraceBadNotZeroCode.olean \
 b3691bbaddec2a56f21380074c6ee45e03fc99530d7a25e639b18451bf12e438 /dev/shm/pa194-trace-member-forward-repo/PA194TraceMemberForwardCode.olean | sha256sum -c -
}
check_inputs
mkdir -p "$out"
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$out:/dev/shm/pa194-domain-instances-repo:/dev/shm/pa194-trace-bad-not-zero-repo:/dev/shm/pa194-ordinal-bad-not-zero-repo:/dev/shm/pa194-ordinal-base-application-code-repo:/dev/shm/pa194-member-domain-at-repo:/dev/shm/pa194-member-domain-closed-repo:/dev/shm/pa194-ordinal-step-application-code-repo:/dev/shm/pa194-trace-member-forward-repo:/dev/shm/pa194-expanded-trace-at-repo:/dev/shm/pa194-context-projections-contradiction-repo:/dev/shm/pa194-quoted-induction-repo:/dev/shm/pa194-reopen-proof-repo:/dev/shm/pa194-close-proof-repo:/dev/shm/pa194-uniform-fully-closed-repo:/dev/shm/pa194-uniform-closure-replay:/dev/shm/pa194-unclose-envelope-replay:/dev/shm/pa194-separation-trace-open-repo:/dev/shm/pa194-separation-trace-witness-repo:/dev/shm/pa194-separation-trace-shift-repo:/dev/shm/pa194-context-exs-witness-repo:/dev/shm/pa194-context-quantifier-code-repo:/dev/shm/pa194-separation-trace-at-code-repo:/dev/shm/pa194-induction-step-shift-repo:/dev/shm/pa194-uniform-sep-combined-repo:/dev/shm/pa194-separation-shift-code-repo:/dev/shm/pa194-internal-induction-at-context-repo:/dev/shm/pa194-context-specialize-code-repo:/dev/shm/pa194-context-mp-code-repo:/dev/shm/pa194-context-conjunction-code-repo:/dev/shm/pa194-context-shift-code-repo:/dev/shm/pa194-internal-separation-shift-repo:/dev/shm/pa194-internal-induction-base-at-repo:/dev/shm/pa194-induction-base-shift-repo:/dev/shm/pa194-ordinal-uniform-repo:/dev/shm/pa194-ordinal-fixed-repo:/dev/shm/pa194-ordinal-induction-code-repo:/dev/shm/pa194-ordinal-statement-repo:/dev/shm/pa194-typed-schema-repo:/dev/shm/pa194-fully-closed-repo:/dev/shm/pa194-fully-closed-replay:/dev/shm/pa194-model-separation-full-replay:/dev/shm/pa194-model-separation-seeded-replay:/dev/shm/pa194-model-closure-definability-replay:/dev/shm/pa194-model-closure-replay:/dev/shm/pa194-general-separation-repo:/dev/shm/pa194-ranked-open-separation-repo:/dev/shm/pa194-general-separation-replay:/dev/shm/pa194-ranked-open-separation-replay-v3:/dev/shm/pa194-unrestricted-all-replay:/dev/shm/pa194-adjunctive-admission-audit:/dev/shm/pa194-full-one-level-audit:/tmp/current14-standard-fresh-build-20261104/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib:$lake_path"
for name in PA194TraceNonzeroFromDomain; do
 lean -j1 -M 4000 -R "$src" -o "$out/$name.olean" "$src/$name.lean" > "$out/$name.log" 2>&1
 if rg -q "sorryAx|declaration uses 'sorry'" "$out/$name.log"; then cat "$out/$name.log"; exit 1; fi
 cat "$out/$name.log"
done
[[ $(rg -c 'depends on axioms:' "$out/PA194TraceNonzeroFromDomain.log") == 4 ]]
check_inputs
echo 'PASS: bad trace member nonzero by downward closure; dependencies prebuilt.'
