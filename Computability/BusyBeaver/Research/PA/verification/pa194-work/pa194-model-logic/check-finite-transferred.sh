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
for module in PA194PAeqTermQuote PA194PAeqAtomQuote PA194PAeqFormulaQuote PA194PAeqQuoteProof PA194PAeqReflSource PA194PAeqEqualitySource PA194PAeqZeroCongruence PA194PAeqZeroInternal PA194PAeqOneCongruence PA194PAeqOneInternal PA194PAeqZeroLtOne PA194PAeqZeroLtOneInternal PA194PAeqFiniteTransferred PA194PAeqFiniteTransferredAudit; do
  case "$module" in
    PA194PAeqAtomQuote) input_dir="$repo/Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-paeq-quote-calibration" ;;
    PA194PAeqEqualitySource) input_dir="$repo/Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-paeq-equality-source" ;;
    PA194PAeqFormulaQuote) input_dir="$repo/Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-paeq-quote-calibration" ;;
    PA194PAeqOneCongruence) input_dir="$repo/Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-paeq-one-congruence" ;;
    PA194PAeqOneInternal) input_dir="$repo/Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-paeq-one-congruence" ;;
    PA194PAeqQuoteProof) input_dir="$repo/Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-paeq-quote-proof" ;;
    PA194PAeqReflSource) input_dir="$repo/Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-paeq-refl-source" ;;
    PA194PAeqTermQuote) input_dir="$repo/Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-paeq-quote-calibration" ;;
    PA194PAeqZeroCongruence) input_dir="$repo/Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-paeq-zero-congruence" ;;
    PA194PAeqZeroInternal) input_dir="$repo/Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-paeq-zero-congruence" ;;
    PA194PAeqZeroLtOne) input_dir="$repo/Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-paeq-zero-lt-one" ;;
    PA194PAeqZeroLtOneInternal) input_dir="$repo/Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-paeq-zero-lt-one" ;;
    *) input_dir="$source_dir" ;;
  esac
  lean -j1 -R "$input_dir" -M 7000 -o "$out/$module.olean" "$input_dir/$module.lean" > "$out/$module.log" 2>&1
  if rg -q "sorryAx|declaration uses 'sorry'" "$out/$module.log"; then exit 1; fi
done
count=$(rg -c 'depends on axioms:' "$out/PA194PAeqFiniteTransferredAudit.log")
[[ "$count" -eq 7 ]]
