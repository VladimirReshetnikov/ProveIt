#!/usr/bin/env bash
set -euo pipefail
if (($# != 5)); then echo 'usage: REPO SEED_BASELINE FULL_BASELINE PACKAGE NEW_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); seed=$(realpath "$2"); base=$(realpath "$3"); package=$(realpath "$4"); out=$(realpath -m "$5")
source_dir=$(cd "$(dirname "$0")" && pwd)
[[ ! -e "$out" ]] || { echo 'Output already exists' >&2; exit 2; }
for x in PA194ModelWeakAdjunction PA194ModelWeakAdjunctionAxiom; do test -f "$seed/$x.olean"; done
for x in PA194ModelFreshInduction PA194ModelRankedEnvironment PA194ModelSimAxiomRules; do test -f "$base/$x.olean"; done
check_inputs() {
 printf '%s  %s\n' \
  4afcf8a0990217ec6dc2143db6a81f3a5f563ee2e4ac2934cb9d3f5903d47ccf "$repo/Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/PA194ModelSeparation.lean" \
  5fcb45ee0b598839625aba648573ec80188f2ceda6f9ae5a5a796faaee379c36 "$repo/Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/PA194ModelLowVacuity.lean" \
  f9d6636abc9323fcb46024e249931fac242bb5cc91ecad32d4cc3de386647dd3 "$repo/Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/PA194ModelSeparationAxiom.lean" \
  a11f9da06ef66ac7bf08fcbc5e1f176b52adb9a1605b48138c7d1b5992a12a5a "$source_dir/PA194RankedOpenSeparation.lean" \
  6bdfb0530de20631767af3fa1dcc4ac9b0e350342acf156bb554ccfe54936c01 "$seed/PA194ModelWeakAdjunction.olean" \
  9929924b4568b7745d4c7927782cd507bc708409e5d2f38fb75c80fa42a9f840 "$seed/PA194ModelWeakAdjunctionAxiom.olean" | sha256sum -c -
}
check_inputs
mkdir -p "$out"
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$out:$seed:$base:/tmp/current14-standard-fresh-build-20261104/lib:$package:$lake_path"
for n in PA194ModelSeparation PA194ModelLowVacuity PA194ModelSeparationAxiom; do
  lean -j1 -M 7000 -R "$repo/Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms" -o "$out/$n.olean" "$repo/Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/$n.lean" > "$out/$n.log" 2>&1
  if rg -q "sorryAx|declaration uses 'sorry'" "$out/$n.log"; then cat "$out/$n.log"; exit 1; fi
done
lean -j1 -M 7000 -R "$source_dir" -o "$out/PA194RankedOpenSeparation.olean" "$source_dir/PA194RankedOpenSeparation.lean" > "$out/PA194RankedOpenSeparation.log" 2>&1
if rg -q "sorryAx|declaration uses 'sorry'" "$out/PA194RankedOpenSeparation.log"; then cat "$out/PA194RankedOpenSeparation.log"; exit 1; fi
for thm in sepRoot_exceeds_two simRuleSeparation_ranked simRuleSeparation_rankedAxiom simRuleSeparation_seededAxiom; do
 rg -F "'PA194ModelLogic.$thm' depends on axioms:" "$out/PA194RankedOpenSeparation.log"
done
check_inputs
echo 'PASS: open separation for ranked and seeded axiom nodes; baseline and foundations prebuilt.'
