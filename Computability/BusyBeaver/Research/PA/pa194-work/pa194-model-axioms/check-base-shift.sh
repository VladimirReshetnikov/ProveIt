#!/usr/bin/env bash
set -euo pipefail
if (($# != 2)); then echo 'usage: REPO NEW_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); out=$(realpath -m "$2"); src=$(cd "$(dirname "$0")" && pwd)
[[ ! -e "$out" ]] || { echo 'Output exists' >&2; exit 2; }
check_inputs() {
 printf '%s  %s\n' \
 2c7af4d2c4dfce958d010116359719b77a8ce1cf6264f8ba8828047c5cc8e3cd "$src/PA194InternalInductionBaseShift.lean" \
 e4e2e718379f8ffae8aec31451f41bc348fd9b883d9e4e1e621866357143d177 "$src/PA194InductionBaseShiftCode.lean" \
 54a3a34cfa4019df7711492d5617fe2c3de115d3e617b8c308af41ae23817b5f /dev/shm/pa194-ordinal-fixed-repo/PA194OrdinalFixed.olean \
 ca883fcc331af8acc2e3f00071f78cabc8d761c2213c6b69a3ba8b15839be16c /dev/shm/pa194-ordinal-uniform-repo/PA194FixedSyntaxQuote.olean | sha256sum -c -
}
check_inputs
mkdir -p "$out"
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$out:/dev/shm/pa194-ordinal-uniform-repo:/dev/shm/pa194-ordinal-fixed-repo:/dev/shm/pa194-ordinal-induction-code-repo:/dev/shm/pa194-ordinal-statement-repo:/dev/shm/pa194-typed-schema-repo:/dev/shm/pa194-fully-closed-repo:/dev/shm/pa194-fully-closed-replay:/dev/shm/pa194-model-separation-full-replay:/dev/shm/pa194-model-separation-seeded-replay:/dev/shm/pa194-model-closure-definability-replay:/dev/shm/pa194-model-closure-replay:/dev/shm/pa194-general-separation-repo:/dev/shm/pa194-ranked-open-separation-repo:/dev/shm/pa194-general-separation-replay:/dev/shm/pa194-ranked-open-separation-replay-v3:/dev/shm/pa194-unrestricted-all-replay:/dev/shm/pa194-adjunctive-admission-audit:/dev/shm/pa194-full-one-level-audit:/tmp/current14-standard-fresh-build-20261104/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib:$lake_path"
for name in PA194InternalInductionBaseShift PA194InductionBaseShiftCode; do
 lean -j1 -M 4000 -R "$src" -o "$out/$name.olean" "$src/$name.lean" > "$out/$name.log" 2>&1
 if rg -q "sorryAx|declaration uses 'sorry'" "$out/$name.log"; then cat "$out/$name.log"; exit 1; fi
 cat "$out/$name.log"
done
[[ $(rg -c 'depends on axioms:' "$out/PA194InternalInductionBaseShift.log") == 3 ]]
[[ $(rg -c 'depends on axioms:' "$out/PA194InductionBaseShiftCode.log") == 3 ]]
check_inputs
echo 'PASS: induction-base proof shift and fixed uniform graph for arbitrary internal properties; dependencies prebuilt.'
