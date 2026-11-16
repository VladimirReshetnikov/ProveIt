#!/usr/bin/env bash
set -euo pipefail
if (($# != 7)); then echo 'usage: REPO ATOMIC_BASE ONE_BASE OPEN_BASE ALL_BASE FULL_BASE NEW_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); atomic=$(realpath "$2"); one=$(realpath "$3"); op=$(realpath "$4"); all=$(realpath "$5"); base=$(realpath "$6"); out=$(realpath -m "$7")
source_dir=$(cd "$(dirname "$0")" && pwd)
[[ ! -e "$out" ]] || { echo 'Output already exists' >&2; exit 2; }
check_inputs() {
 printf '%s  %s\n' \
 042db640252e2587c49adfac1b1e830193524c263f4aec3c55f0caefd21ad663 "$source_dir/PA194IntersectionSourceBinding.lean" \
 5e17dc8cf1cf0de7877b63e831810d64b9c43c988424cb3faad3dc6be3057a7e "$repo/Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-source-intersection/PA194SourceIntersection.lean" \
 1be3293ba0c4e2a6502645431be23898eac8d2502a3f08491fcfd09b54fe1fa1 "$atomic/PA194AtomicParameterSeparation.olean" \
 42cb917454cc6f01e34d7b728a782e3a645a7ea99834e9e32582656286d70f50 "$base/PA194SourceIntersection.olean" | sha256sum -c -
}
check_inputs
mkdir -p "$out"
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$out:$atomic:$one:$op:$all:/dev/shm/pa194-adjunctive-admission-audit:$base:/tmp/current14-standard-fresh-build-20261104/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib:$lake_path"
lean -j1 -M 5000 -R "$source_dir" -o "$out/PA194IntersectionSourceBinding.olean" "$source_dir/PA194IntersectionSourceBinding.lean" > "$out/PA194IntersectionSourceBinding.log" 2>&1
if rg -q "sorryAx|declaration uses 'sorry'" "$out/PA194IntersectionSourceBinding.log"; then cat "$out/PA194IntersectionSourceBinding.log"; exit 1; fi
[[ $(rg -c 'depends on axioms:' "$out/PA194IntersectionSourceBinding.log") == 3 ]]
cat "$out/PA194IntersectionSourceBinding.log"
check_inputs
echo 'PASS: source intersection sentence, quote, and seeded target leaf; staged baseline and foundations prebuilt.'
