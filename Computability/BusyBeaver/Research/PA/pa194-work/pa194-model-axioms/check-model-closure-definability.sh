#!/usr/bin/env bash
set -euo pipefail
if (($# != 7)); then echo 'usage: REPO CLOSURE_BASE GENERAL_BASE SEP_BASE OPEN_BASE FULL_BASE NEW_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); closure=$(realpath "$2"); gen=$(realpath "$3"); sep=$(realpath "$4"); op=$(realpath "$5"); base=$(realpath "$6"); out=$(realpath -m "$7")
src=$(cd "$(dirname "$0")" && pwd)
[[ ! -e "$out" ]] || { echo 'Output exists' >&2; exit 2; }
check_inputs() {
 printf '%s  %s\n' \
 d860b98aba8dc0142d72020269407f6655da430bd5d454be5ecf2426ea2dd930 "$src/PA194ModelClosureDefinable.lean" \
 369f786d3a1a36276732e27e40dcef80cc93ca48f1c2d235503f5784713e1bab "$closure/PA194PushHistory.olean" | sha256sum -c -
}
check_inputs
mkdir -p "$out"
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$out:$closure:$gen:$sep:$op:/dev/shm/pa194-adjunctive-admission-audit:$base:/tmp/current14-standard-fresh-build-20261104/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib:$lake_path"
lean -j1 -M 4000 -R "$src" -o "$out/PA194ModelClosureDefinable.olean" "$src/PA194ModelClosureDefinable.lean" > "$out/check.log" 2>&1
if rg -q "sorryAx|declaration uses 'sorry'" "$out/check.log"; then cat "$out/check.log"; exit 1; fi
[[ $(rg -c 'depends on axioms:' "$out/check.log") == 2 ]]
cat "$out/check.log"
check_inputs
echo 'PASS: canonical model-valued closure and push are Σ₁-definable; dependencies prebuilt.'
