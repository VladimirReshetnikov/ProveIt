#!/usr/bin/env bash
set -euo pipefail
if (($# != 2)); then echo 'usage: REPO NEW_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); out=$(realpath -m "$2"); src=$(cd "$(dirname "$0")" && pwd)
[[ ! -e "$out" ]] || { echo 'Output exists' >&2; exit 2; }
check_inputs() {
 printf '%s  %s\n' 03e1d46f3a12d8a5b25999ccbac2eb0954499a1f503a090e074f635f227cdaee /dev/shm/pa194-context-triple-specialize-repo/PA194ContextTripleSpecializeCode.olean | sha256sum -c -
 printf '%s  %s\n' \
 05b0fc7a1aed6dda8d9d770c6e6ccaa58e2437e19859dc0c7fb03493cd533dbf "$src/PA194ContextFourSpecializeCode.lean" \
 8f748362231d253b73dbd4fe13ce956398ae84205bced73556ff12c9f2f85a4d /dev/shm/pa194-ordinal-step-application-code-repo/PA194ContextDoubleSpecializeCode.olean \
 63583ead8c3f90bb2621596aef31bd21ca32bc83eb225f32796d63b5cfa90c99 /dev/shm/pa194-context-specialize-code-repo/PA194ContextSpecializeCode.olean | sha256sum -c -
}
check_inputs
mkdir -p "$out"
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$out:/dev/shm/pa194-context-triple-specialize-repo:/dev/shm/pa194-ordinal-step-application-code-repo:/dev/shm/pa194-ordinal-base-application-code-repo:/dev/shm/pa194-uniform-sep-combined-repo:/dev/shm/pa194-separation-shift-code-repo:/dev/shm/pa194-internal-induction-at-context-repo:/dev/shm/pa194-context-specialize-code-repo:/dev/shm/pa194-context-mp-code-repo:/dev/shm/pa194-context-conjunction-code-repo:/dev/shm/pa194-context-shift-code-repo:/dev/shm/pa194-internal-separation-shift-repo:/dev/shm/pa194-internal-induction-base-at-repo:/dev/shm/pa194-induction-base-shift-repo:/dev/shm/pa194-ordinal-uniform-repo:/dev/shm/pa194-ordinal-fixed-repo:/dev/shm/pa194-ordinal-induction-code-repo:/dev/shm/pa194-ordinal-statement-repo:/dev/shm/pa194-typed-schema-repo:/dev/shm/pa194-fully-closed-repo:/dev/shm/pa194-fully-closed-replay:/dev/shm/pa194-model-separation-full-replay:/dev/shm/pa194-model-separation-seeded-replay:/dev/shm/pa194-model-closure-definability-replay:/dev/shm/pa194-model-closure-replay:/dev/shm/pa194-general-separation-repo:/dev/shm/pa194-ranked-open-separation-repo:/dev/shm/pa194-general-separation-replay:/dev/shm/pa194-ranked-open-separation-replay-v3:/dev/shm/pa194-unrestricted-all-replay:/dev/shm/pa194-adjunctive-admission-audit:/dev/shm/pa194-full-one-level-audit:/tmp/current14-standard-fresh-build-20261104/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib:$lake_path"
for name in PA194ContextFourSpecializeCode; do
 lean -j1 -M 4000 -R "$src" -o "$out/$name.olean" "$src/$name.lean" > "$out/$name.log" 2>&1
 if rg -q "sorryAx|declaration uses 'sorry'" "$out/$name.log"; then cat "$out/$name.log"; exit 1; fi
 cat "$out/$name.log"
done
[[ $(rg -c 'depends on axioms:' "$out/PA194ContextFourSpecializeCode.log") == 3 ]]
check_inputs
echo 'PASS: contextual four-fold specialization proof code under arbitrary contexts; dependencies prebuilt.'
