#!/usr/bin/env bash
set -euo pipefail
if (($# != 8)); then echo 'usage: REPO DEF_BASE CLOSURE_BASE GENERAL_BASE SEP_BASE OPEN_BASE FULL_BASE NEW_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); df=$(realpath "$2"); closure=$(realpath "$3"); gen=$(realpath "$4"); sep=$(realpath "$5"); op=$(realpath "$6"); base=$(realpath "$7"); out=$(realpath -m "$8")
src=$(cd "$(dirname "$0")" && pwd)
[[ ! -e "$out" ]] || { echo 'Output exists' >&2; exit 2; }
check_inputs() {
 printf '%s  %s\n' \
 865498b669e712ac074d59f7f59a6f3b6cd783f771edf6b9d706440658aa71c8 "$src/PA194ModelClosureSeparation.lean" \
 7a2a0892f886d02ca15d09e8c61685564f1eb090f4f349c20ceeafc8dc41135b "$df/PA194ModelClosureDefinable.olean" \
 369f786d3a1a36276732e27e40dcef80cc93ca48f1c2d235503f5784713e1bab "$closure/PA194PushHistory.olean" | sha256sum -c -
}
check_inputs
mkdir -p "$out"
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$out:$df:$closure:$gen:$sep:$op:/dev/shm/pa194-adjunctive-admission-audit:$base:/tmp/current14-standard-fresh-build-20261104/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib:$lake_path"
lean -j1 -M 4000 -R "$src" -o "$out/PA194ModelClosureSeparation.olean" "$src/PA194ModelClosureSeparation.lean" > "$out/check.log" 2>&1
if rg -q "sorryAx|declaration uses 'sorry'" "$out/check.log"; then cat "$out/check.log"; exit 1; fi
[[ $(rg -c 'depends on axioms:' "$out/check.log") == 4 ]]
cat "$out/check.log"
check_inputs
echo 'PASS: seeded model-length separation leaf with explicit size premise; dependencies prebuilt.'
