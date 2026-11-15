#!/usr/bin/env bash
set -euo pipefail
if (($# != 6)); then echo 'usage: REPO OPEN_BASELINE ALL_BASELINE SEED_BASELINE FULL_BASELINE NEW_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); op=$(realpath "$2"); all=$(realpath "$3"); seed=$(realpath "$4"); base=$(realpath "$5"); out=$(realpath -m "$6")
source_dir=$(cd "$(dirname "$0")" && pwd)
[[ ! -e "$out" ]] || { echo 'Output already exists' >&2; exit 2; }
check_inputs() {
 printf '%s  %s\n' \
 14caa704bc72d5a20b2109711e04869e671ea8d1286898de3384bd1fcd5626c1 "$source_dir/PA194OneParameterSeparation.lean" \
 170ad595360834d17170f00f9fba29f5302384a0142f49d34805eb143c64a7f3 "$op/PA194RankedOpenSeparation.olean" | sha256sum -c -
 test -f "$all/PA194ModelSourceOpeningGeneral.olean"
}
check_inputs
mkdir -p "$out"
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$out:$op:$all:$seed:$base:/tmp/current14-standard-fresh-build-20261104/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib:$lake_path"
lean -j1 -M 7000 -R "$source_dir" -o "$out/PA194OneParameterSeparation.olean" "$source_dir/PA194OneParameterSeparation.lean" > "$out/PA194OneParameterSeparation.log" 2>&1
if rg -q "sorryAx|declaration uses 'sorry'" "$out/PA194OneParameterSeparation.log"; then cat "$out/PA194OneParameterSeparation.log"; exit 1; fi
rg -F "'PA194ModelLogic.simRuleSeparation_closedOnce' depends on axioms:" "$out/PA194OneParameterSeparation.log"
check_inputs
echo 'PASS: conditional single universal closure of a separation leaf; baseline and foundations prebuilt.'
