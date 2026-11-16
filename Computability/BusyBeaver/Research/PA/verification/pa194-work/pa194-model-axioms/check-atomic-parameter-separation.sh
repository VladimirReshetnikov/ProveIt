#!/usr/bin/env bash
set -euo pipefail
if (($# != 7)); then echo 'usage: REPO ONE_BASE OPEN_BASE ALL_BASE SEED_BASE FULL_BASE NEW_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); one=$(realpath "$2"); op=$(realpath "$3"); all=$(realpath "$4"); seed=$(realpath "$5"); base=$(realpath "$6"); out=$(realpath -m "$7")
source_dir=$(cd "$(dirname "$0")" && pwd)
[[ ! -e "$out" ]] || { echo 'Output already exists' >&2; exit 2; }
check_inputs() {
 printf '%s  %s\n' \
 d9120145a2590671813ed21ce154c5a6fe094f713166b4fb0a779531a701e6d2 "$source_dir/PA194ClosedSeparationRank.lean" \
 80a4cb158a384e41b2054c88257de6a41abe9fc55ec03239a589640b4a2e96fd "$source_dir/PA194AtomicParameterSeparation.lean" \
 40617971ae4e7b1cf341ed53d63430f7da1516c9c0613e23eb0e3056c68515a4 "$source_dir/PA194AtomicSeparationAudit.lean" \
 e50bc37881a83306417b5d13648f3e07e32309ddb0209e264c47d6ac4579a47a "$one/PA194OneParameterSeparation.olean" \
 170ad595360834d17170f00f9fba29f5302384a0142f49d34805eb143c64a7f3 "$op/PA194RankedOpenSeparation.olean" \
 aaafd6f6b06a22fd3eedac088f7a33c6679699421efb4c9e36f3616c32681e62 "$all/PA194ModelSourceOpeningGeneral.olean" | sha256sum -c -
}
check_inputs
mkdir -p "$out"
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$out:$one:$op:$all:$seed:$base:/tmp/current14-standard-fresh-build-20261104/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib:$lake_path"
for n in PA194ClosedSeparationRank PA194AtomicParameterSeparation PA194AtomicSeparationAudit; do
 lean -j1 -M 4000 -R "$source_dir" -o "$out/$n.olean" "$source_dir/$n.lean" > "$out/$n.log" 2>&1
 if rg -q "sorryAx|declaration uses 'sorry'" "$out/$n.log"; then cat "$out/$n.log"; exit 1; fi
done
[[ $(rg -c 'depends on axioms:' "$out/PA194AtomicSeparationAudit.log") == 4 ]]
cat "$out/PA194AtomicSeparationAudit.log"
check_inputs
echo 'PASS: one atomic parameter separation closure and seeded axiom leaf; staged baseline and foundations prebuilt.'
