#!/usr/bin/env bash
set -euo pipefail
repo=$1
out=$2
shift 2
source_dir=$(cd -- "$(dirname -- "$0")" && pwd)
mkdir -p "$out"
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
baselines=$(IFS=:; printf '%s' "$*")
export LEAN_PATH="$out:$baselines:$lake_path"
for module in PA194PAeqSequent PA194PAeqProofTransport PA194TransportSentence PA194FiniteAxioms PA194PAeqPASupplier PA194PAeqPAExceptFinite PA194PAeqPAExceptFiniteAudit; do
  case "$module" in
    PA194PAeqSequent) input_dir="$repo/Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-paeq-sequent" ;;
    PA194PAeqProofTransport) input_dir="$repo/Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-paeq-proof-transport" ;;
    PA194TransportSentence) input_dir="$repo/Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-paeq-transport-sentence" ;;
    PA194FiniteAxioms) input_dir="$repo/Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-finite-axiom-classifier" ;;
    PA194PAeqPASupplier) input_dir="$repo/Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-paeq-pa-supplier" ;;
    *) input_dir="$source_dir" ;;
  esac
  lean -j1 -R "$input_dir" -M 7000 -o "$out/$module.olean" "$input_dir/$module.lean" > "$out/$module.log" 2>&1
  if rg -q "sorryAx|declaration uses 'sorry'" "$out/$module.log"; then exit 1; fi
done
count=$(rg -c 'depends on axioms:' "$out/PA194PAeqPAExceptFiniteAudit.log")
[[ "$count" -eq 5 ]]
