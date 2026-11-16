#!/usr/bin/env bash
set -euo pipefail
if (($# != 5)); then echo 'usage: REPO TERM_BASE OPEN_BASE FULL_BASE NEW_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); term=$(realpath "$2"); op=$(realpath "$3"); base=$(realpath "$4"); out=$(realpath -m "$5")
source_dir=$(cd "$(dirname "$0")" && pwd)
[[ ! -e "$out" ]] || { echo 'Output already exists' >&2; exit 2; }
check_inputs() {
 printf '%s  %s\n' \
 ab84b14a4c04e87c53c61c5503bb85739731c68a3a8daf355830cfa07f0ad007 "$source_dir/PA194BindSourceAtom.lean" \
 b01ff544a8a0850faf66e09593e086f46075b3cbebde954732d2328e9d2d8d9c "$term/PA194BindSourceTerm.olean" \
 694d6ee82d7f6f02feaf2c09e15764b9372b1ac1bda223f7ec9875dac77baedd "$op/PA194ModelSourceOpeningAtom.olean" | sha256sum -c -
}
check_inputs
mkdir -p "$out"
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$out:$term:$op:/dev/shm/pa194-adjunctive-admission-audit:$base:/tmp/current14-standard-fresh-build-20261104/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib:$lake_path"
lean -j1 -M 4000 -R "$source_dir" -o "$out/PA194BindSourceAtom.olean" "$source_dir/PA194BindSourceAtom.lean" > "$out/PA194BindSourceAtom.log" 2>&1
if rg -q "sorryAx|declaration uses 'sorry'" "$out/PA194BindSourceAtom.log"; then cat "$out/PA194BindSourceAtom.log"; exit 1; fi
[[ $(rg -c 'depends on axioms:' "$out/PA194BindSourceAtom.log") == 4 ]]
cat "$out/PA194BindSourceAtom.log"
check_inputs
echo 'PASS: definable binary-source-atom inverse opening in PRA plus IΣ₁ models; staged baselines and foundations prebuilt.'
