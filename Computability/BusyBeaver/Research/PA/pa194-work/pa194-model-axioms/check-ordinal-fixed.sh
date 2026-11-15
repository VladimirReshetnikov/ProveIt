#!/usr/bin/env bash
set -euo pipefail
if (($# != 4)); then echo 'usage: REPO INDUCTION_BASE STATEMENT_BASE NEW_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); induction=$(realpath "$2"); statement=$(realpath "$3"); out=$(realpath -m "$4")
src=$(cd "$(dirname "$0")" && pwd)
[[ ! -e "$out" ]] || { echo 'Output exists' >&2; exit 2; }
check_inputs() {
 printf '%s  %s\n' \
 2df546291db26a45abac1581f79aadb2d33ac9d604a99047f854147ea8f78773 "$src/PA194OrdinalFixed.lean" \
 1e7bc847150dadda7ce38bac70da1e5c949afb3314c2951ec9eeb401674d8fe7 "$induction/PA194OrdinalStatementFromProperty.olean" | sha256sum -c -
}
check_inputs
mkdir -p "$out"
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$out:$induction:$statement:/dev/shm/pa194-typed-schema-replay:/dev/shm/pa194-fully-closed-replay:/dev/shm/pa194-model-separation-full-replay:/dev/shm/pa194-model-separation-seeded-replay:/dev/shm/pa194-model-closure-definability-replay:/dev/shm/pa194-model-closure-replay:/dev/shm/pa194-general-separation-replay:/dev/shm/pa194-ranked-open-separation-replay-v3:/dev/shm/pa194-unrestricted-all-replay:/dev/shm/pa194-adjunctive-admission-audit:/dev/shm/pa194-full-one-level-audit:/tmp/current14-standard-fresh-build-20261104/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib:$lake_path"
lean -j1 -M 4000 -R "$src" -o "$out/PA194OrdinalFixed.olean" "$src/PA194OrdinalFixed.lean" > "$out/check.log" 2>&1
if rg -q "sorryAx|declaration uses 'sorry'" "$out/check.log"; then cat "$out/check.log"; exit 1; fi
[[ $(rg -c 'depends on axioms:' "$out/check.log") == 4 ]]
cat "$out/check.log"
check_inputs
echo 'PASS: model-local definable ordinal-induction statement with actual quoted templates; dependencies prebuilt.'
