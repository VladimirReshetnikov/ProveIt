#!/usr/bin/env bash
set -euo pipefail
if (($# != 2)); then echo 'usage: REPO NEW_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); out=$(realpath -m "$2"); src=$(cd "$(dirname "$0")" && pwd)
[[ ! -e "$out" ]] || { echo 'Output exists' >&2; exit 2; }
check_inputs() {
 printf '%s  %s\n' \
 54e178889ac1f03b3f189c0c79e9865844d283bb0c90278af2f882a91bd83002 "$src/PA194BadTraceGreatest.lean" \
 d0e60ddaab397b11a1f2890e27b514da3005e033d2d5da19eebe3f35fc650f8d /dev/shm/pa194-trace-nonzero-from-domain-repo/PA194TraceNonzeroFromDomain.olean \
 a85fbe811c71eedeba5153a55b27227915b06ffcf5b1fbba23a68745aa8b7655 /dev/shm/pa194-domain-greatest-repo/PA194DomainGreatestAtCode.olean \
 e4e15431b3a62e213f3e02145bd9638aff6f71651163f404265adf15f6c5bf47 /dev/shm/pa194-domain-instances-repo/PA194DomainInstances.olean | sha256sum -c -
}
check_inputs
mkdir -p "$out"
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$out:/dev/shm/pa194-trace-nonzero-from-domain-repo:/dev/shm/pa194-domain-greatest-repo:/dev/shm/pa194-domain-instances-repo:/dev/shm/pa194-trace-bad-not-zero-repo:/dev/shm/pa194-ordinal-bad-not-zero-repo:/dev/shm/pa194-ordinal-base-application-code-repo:/dev/shm/pa194-member-domain-at-repo:/dev/shm/pa194-member-domain-closed-repo:/dev/shm/pa194-ordinal-step-application-code-repo:/dev/shm/pa194-trace-member-forward-repo:/dev/shm/pa194-expanded-trace-at-repo:/dev/shm/pa194-context-projections-contradiction-repo:/dev/shm/pa194-quoted-induction-repo:/dev/shm/pa194-reopen-proof-repo:/dev/shm/pa194-close-proof-repo:/dev/shm/pa194-uniform-fully-closed-repo:/dev/shm/pa194-uniform-closure-replay:/dev/shm/pa194-unclose-envelope-replay:/dev/shm/pa194-separation-trace-open-repo:/dev/shm/pa194-separation-trace-witness-repo:/dev/shm/pa194-separation-trace-shift-repo:/dev/shm/pa194-context-exs-witness-repo:/dev/shm/pa194-context-quantifier-code-repo:/dev/shm/pa194-separation-trace-at-code-repo:/dev/shm/pa194-induction-step-shift-repo:/dev/shm/pa194-uniform-sep-combined-repo:/dev/shm/pa194-separation-shift-code-repo:/dev/shm/pa194-internal-induction-at-context-repo:/dev/shm/pa194-context-specialize-code-repo:/dev/shm/pa194-context-mp-code-repo:/dev/shm/pa194-context-conjunction-code-repo:/dev/shm/pa194-context-shift-code-repo:/dev/shm/pa194-internal-separation-shift-repo:/dev/shm/pa194-internal-induction-base-at-repo:/dev/shm/pa194-induction-base-shift-repo:/dev/shm/pa194-ordinal-uniform-repo:/dev/shm/pa194-ordinal-fixed-repo:/dev/shm/pa194-ordinal-induction-code-repo:/dev/shm/pa194-ordinal-statement-repo:/dev/shm/pa194-typed-schema-repo:/dev/shm/pa194-fully-closed-repo:/dev/shm/pa194-fully-closed-replay:/dev/shm/pa194-model-separation-full-replay:/dev/shm/pa194-model-separation-seeded-replay:/dev/shm/pa194-model-closure-definability-replay:/dev/shm/pa194-model-closure-replay:/dev/shm/pa194-general-separation-repo:/dev/shm/pa194-ranked-open-separation-repo:/dev/shm/pa194-general-separation-replay:/dev/shm/pa194-ranked-open-separation-replay-v3:/dev/shm/pa194-unrestricted-all-replay:/dev/shm/pa194-adjunctive-admission-audit:/dev/shm/pa194-full-one-level-audit:/tmp/current14-standard-fresh-build-20261104/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib:$lake_path"
for name in PA194BadTraceGreatest; do
 lean -j1 -M 4000 -R "$src" -o "$out/$name.olean" "$src/$name.lean" > "$out/$name.log" 2>&1
 if rg -q "sorryAx|declaration uses 'sorry'" "$out/$name.log"; then cat "$out/$name.log"; exit 1; fi
 cat "$out/$name.log"
done
[[ $(rg -c 'depends on axioms:' "$out/PA194BadTraceGreatest.log") == 4 ]]
check_inputs
echo 'PASS: greatest predecessor of bad trace member; dependencies prebuilt.'
