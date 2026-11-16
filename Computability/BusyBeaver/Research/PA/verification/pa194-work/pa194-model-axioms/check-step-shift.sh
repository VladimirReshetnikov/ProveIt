#!/usr/bin/env bash
set -euo pipefail
if (($# != 2)); then echo 'usage: REPO NEW_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); out=$(realpath -m "$2"); src=$(cd "$(dirname "$0")" && pwd)
[[ ! -e "$out" ]] || { echo 'Output exists' >&2; exit 2; }
check_inputs() {
 printf '%s  %s\n' \
 76f256e9e83849e8f9457dd77fa6c467483d5b1b4e2e2d7b5884cdede53b5e21 "$src/PA194InternalInductionStepShift.lean" \
 f526ea1cc66064fbedbfcf7570fb0ab73526c0fe86b9cc43f48ed1441392d3c0 "$src/PA194InductionStepShiftCode.lean" \
 749881f217531e5c00dc7e84a784e61a9d40a3cedc28b236b22ff703cf42545b /dev/shm/pa194-induction-base-shift-repo/PA194InternalInductionBaseShift.olean \
 ca883fcc331af8acc2e3f00071f78cabc8d761c2213c6b69a3ba8b15839be16c /dev/shm/pa194-ordinal-uniform-repo/PA194FixedSyntaxQuote.olean | sha256sum -c -
}
check_inputs
mkdir -p "$out"
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$out:/dev/shm/pa194-induction-base-shift-repo:/dev/shm/pa194-ordinal-uniform-repo:/dev/shm/pa194-ordinal-fixed-repo:/dev/shm/pa194-ordinal-induction-code-repo:/dev/shm/pa194-ordinal-statement-repo:/dev/shm/pa194-typed-schema-repo:/dev/shm/pa194-fully-closed-repo:/dev/shm/pa194-fully-closed-replay:/dev/shm/pa194-model-separation-full-replay:/dev/shm/pa194-model-separation-seeded-replay:/dev/shm/pa194-model-closure-definability-replay:/dev/shm/pa194-model-closure-replay:/dev/shm/pa194-general-separation-repo:/dev/shm/pa194-ranked-open-separation-repo:/dev/shm/pa194-general-separation-replay:/dev/shm/pa194-ranked-open-separation-replay-v3:/dev/shm/pa194-unrestricted-all-replay:/dev/shm/pa194-adjunctive-admission-audit:/dev/shm/pa194-full-one-level-audit:/tmp/current14-standard-fresh-build-20261104/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib:$lake_path"
for name in PA194InternalInductionStepShift PA194InductionStepShiftCode; do
 lean -j1 -M 4000 -R "$src" -o "$out/$name.olean" "$src/$name.lean" > "$out/$name.log" 2>&1
 if rg -q "sorryAx|declaration uses 'sorry'" "$out/$name.log"; then cat "$out/$name.log"; exit 1; fi
 cat "$out/$name.log"
done
[[ $(rg -c 'depends on axioms:' "$out/PA194InternalInductionStepShift.log") == 3 ]]
[[ $(rg -c 'depends on axioms:' "$out/PA194InductionStepShiftCode.log") == 4 ]]
check_inputs
echo 'PASS: induction-step proof shift and fixed uniform graph for arbitrary internal properties; dependencies prebuilt.'
