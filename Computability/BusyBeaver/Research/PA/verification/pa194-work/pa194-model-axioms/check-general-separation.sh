#!/usr/bin/env bash
set -euo pipefail
if (($# != 5)); then echo 'usage: REPO OPEN_SEPARATION_BASE OPEN_FORMULA_BASE FULL_BASE NEW_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); sep=$(realpath "$2"); op=$(realpath "$3"); base=$(realpath "$4"); out=$(realpath -m "$5")
source_dir=$(cd "$(dirname "$0")" && pwd)
[[ ! -e "$out" ]] || { echo 'Output already exists' >&2; exit 2; }
check_inputs() {
 printf '%s  %s\n' \
 1fb1ca92cb8df7135d0d3fbad4eb5ae80b13f01ca829d66d49178d4b9b2b2cc8 "$source_dir/PA194BindSourceTerm.lean" \
 ab84b14a4c04e87c53c61c5503bb85739731c68a3a8daf355830cfa07f0ad007 "$source_dir/PA194BindSourceAtom.lean" \
 432f8e3c81c19d9e99303d69a65fd965f8fe17bdd62be8afaa9c911cfac94125 "$source_dir/PA194BindTermGraph.lean" \
 18ad3067b900ce312f5087b57a0583172991333949815018fbf7aa312d151ca5 "$source_dir/PA194BindPairGraph.lean" \
 5cf4f809dfa8731bcf3a05edf0f65f2edd1e16ee2370e5d4e7fb2f9734f11bc0 "$source_dir/PA194BindSourceFormula.lean" \
 0361f0ed3241eac43082040bdcd9bd2b3232bf7fa4210c9dc761d22e4f327b89 "$source_dir/PA194BindFormulaInverse.lean" \
 d9120145a2590671813ed21ce154c5a6fe094f713166b4fb0a779531a701e6d2 "$source_dir/PA194ClosedSeparationRank.lean" \
 53200e360552e9f7b9ad1074a8473c6f86af9b1bbbf4fa70d98907ba555928d3 "$source_dir/PA194BoundSeparation.lean" \
 530888117125b53b9cb9cc9ad4f0457a849dfaca3823386b2d6f9550ea5dd87d "$source_dir/PA194GeneralSeparationAudit.lean" \
 170ad595360834d17170f00f9fba29f5302384a0142f49d34805eb143c64a7f3 "$sep/PA194RankedOpenSeparation.olean" \
 aaafd6f6b06a22fd3eedac088f7a33c6679699421efb4c9e36f3616c32681e62 "$op/PA194ModelSourceOpeningGeneral.olean" | sha256sum -c -
}
check_inputs
mkdir -p "$out"
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$out:$sep:$op:/dev/shm/pa194-adjunctive-admission-audit:$base:/tmp/current14-standard-fresh-build-20261104/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib:$lake_path"
for n in PA194BindSourceTerm PA194BindSourceAtom PA194BindTermGraph PA194BindPairGraph PA194BindSourceFormula PA194BindFormulaInverse PA194ClosedSeparationRank PA194BoundSeparation PA194GeneralSeparationAudit; do
 echo "Checking $n"
 lean -j1 -M 4000 -R "$source_dir" -o "$out/$n.olean" "$source_dir/$n.lean" > "$out/$n.log" 2>&1
 if rg -q "sorryAx|declaration uses 'sorry'" "$out/$n.log"; then cat "$out/$n.log"; exit 1; fi
done
[[ $(rg -c 'depends on axioms:' "$out/PA194GeneralSeparationAudit.log") == 14 ]]
cat "$out/PA194GeneralSeparationAudit.log"
check_inputs
echo 'PASS: generalized one-parameter separation in PRA plus IΣ₁ models; staged baselines and foundations prebuilt.'
