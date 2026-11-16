#!/usr/bin/env bash
set -euo pipefail
if (($# != 9)); then echo 'usage: REPO SEEDED_BASE DEF_BASE CLOSURE_BASE GENERAL_BASE SEP_BASE OPEN_BASE FULL_BASE NEW_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); seeded=$(realpath "$2"); df=$(realpath "$3"); closure=$(realpath "$4"); gen=$(realpath "$5"); sep=$(realpath "$6"); op=$(realpath "$7"); base=$(realpath "$8"); out=$(realpath -m "$9")
src=$(cd "$(dirname "$0")" && pwd)
[[ ! -e "$out" ]] || { echo 'Output exists' >&2; exit 2; }
check_inputs() {
 printf '%s  %s\n' \
 ce3a062a4fc20a9c061af81b637d0cd2a69ad98e4fcb406116c5ffd9d03e71ec "$src/PA194ModelClosureComplexity.lean" \
 bc37296382e00cebc3dfd7e4d768b990a795950e0481895b8910a5b5419c1633 "$seeded/PA194ModelClosureSeparation.olean" \
 7a2a0892f886d02ca15d09e8c61685564f1eb090f4f349c20ceeafc8dc41135b "$df/PA194ModelClosureDefinable.olean" \
 369f786d3a1a36276732e27e40dcef80cc93ca48f1c2d235503f5784713e1bab "$closure/PA194PushHistory.olean" | sha256sum -c -
}
check_inputs
mkdir -p "$out"
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$out:$seeded:$df:$closure:$gen:$sep:$op:/dev/shm/pa194-adjunctive-admission-audit:$base:/tmp/current14-standard-fresh-build-20261104/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib:$lake_path"
lean -j1 -M 4000 -R "$src" -o "$out/PA194ModelClosureComplexity.olean" "$src/PA194ModelClosureComplexity.lean" > "$out/check.log" 2>&1
if rg -q "sorryAx|declaration uses 'sorry'" "$out/check.log"; then cat "$out/check.log"; exit 1; fi
[[ $(rg -c 'depends on axioms:' "$out/check.log") == 6 ]]
cat "$out/check.log"
check_inputs
echo 'PASS: seeded model-length separation leaf with size discharged; dependencies prebuilt.'
