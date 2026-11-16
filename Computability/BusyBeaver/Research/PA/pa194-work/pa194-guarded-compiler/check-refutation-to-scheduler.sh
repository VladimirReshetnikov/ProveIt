#!/usr/bin/env bash
set -euo pipefail
repo=$(realpath "${1:?repository root required}")
out=$(realpath -m "${2:?fresh output directory required}")
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
cd "$repo"
ulimit -c 0
mkdir "$out"
sha256sum -c "$here/refutation-to-scheduler-pins.sha256"
mapfile -t stages < "$here/refutation-to-scheduler-stages.txt"
for stage in "${stages[@]}"; do
  [[ -d "$stage" ]] || { printf 'Missing stage: %s\n' "$stage" >&2; exit 1; }
done
stage_path=$(IFS=:; printf '%s' "${stages[*]}")
export LEAN_PATH="$out:$stage_path:$(lake env printenv LEAN_PATH)"
rebuild() {
  local src=$1 mod=$2 reports=$3
  local log="$out/$mod.log"
  if ! lean -j1 -R "$src" -M 6000 -o "$out/$mod.olean" "$src/$mod.lean" > "$log" 2>&1; then
    head -40 "$log"
    return 1
  fi
  if rg -q "sorryAx|declaration uses 'sorry'" "$log"; then
    cat "$log"
    return 1
  fi
  [[ $(rg -c 'depends on axioms:' "$log") == "$reports" ]]
}
for entry in PA194PAeqAtoms:4 PA194PAeqAtomCode:2 PA194PAeqFormulaConstruction:1 PA194PAeqFormulaCode:12; do
  rebuild "$here/../pa194-paeq-formula" "${entry%:*}" "${entry#*:}"
done
for entry in PA194InductionSupplier:3 PA194OrdinalInductionLink:3 PA194RemainingFixedSupplier:2 \
             PA194FullSourceRefutationReduction:1 PA194PARefutationScheduler:1; do
  rebuild "$here" "${entry%:*}" "${entry#*:}"
done
sha256sum -c "$here/refutation-to-scheduler-pins.sha256"
printf 'PASS: conditional PA-refutation transport through the modeled scheduler; staged lower dependencies.\n'
