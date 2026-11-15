#!/usr/bin/env bash
set -euo pipefail
if (($# != 4)); then echo 'usage: REPO OPEN_BASE FULL_BASE NEW_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); op=$(realpath "$2"); base=$(realpath "$3"); out=$(realpath -m "$4")
source_dir=$(cd "$(dirname "$0")" && pwd)
[[ ! -e "$out" ]] || { echo 'Output already exists' >&2; exit 2; }
check_inputs() {
 printf '%s  %s\n' \
 1fb1ca92cb8df7135d0d3fbad4eb5ae80b13f01ca829d66d49178d4b9b2b2cc8 "$source_dir/PA194BindSourceTerm.lean" \
 bef096342795672ac14b5ef70bdd2e9268b6c79e5e023b729c7ebf9149e54e4f "$op/PA194ModelSourceOpeningLabel.olean" \
 cae60ed5bb428e2c4b22aa37aa3841780edf1293c9458e08839de6f03c4e094f "$op/PA194ModelSourceQVecTyped.olean" | sha256sum -c -
}
check_inputs
mkdir -p "$out"
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$out:$op:/dev/shm/pa194-adjunctive-admission-audit:$base:/tmp/current14-standard-fresh-build-20261104/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib:$lake_path"
lean -j1 -M 4000 -R "$source_dir" -o "$out/PA194BindSourceTerm.olean" "$source_dir/PA194BindSourceTerm.lean" > "$out/PA194BindSourceTerm.log" 2>&1
if rg -q "sorryAx|declaration uses 'sorry'" "$out/PA194BindSourceTerm.log"; then cat "$out/PA194BindSourceTerm.log"; exit 1; fi
[[ $(rg -c 'depends on axioms:' "$out/PA194BindSourceTerm.log") == 2 ]]
cat "$out/PA194BindSourceTerm.log"
check_inputs
echo 'PASS: definable source-term inverse opening in PRA plus IΣ₁ models; staged baselines and foundations prebuilt.'
