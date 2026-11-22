#!/bin/sh
# Run from any directory with the Lean 4.19 standard library and Python 3.10+.
set -eu
project_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
build_dir=$(mktemp -d)
trap 'rm -rf "$build_dir"' EXIT
cd "$project_dir/lean"
export LEAN_PATH="$build_dir"
lean --version
for module in Arithmetic FiniteRamsey Graph MaskBridge ThreeColors
do
  lean -o "$build_dir/$module.olean" "$module.lean"
done
cat > "$build_dir/Audit.lean" <<'LEAN'
import MaskBridge
import ThreeColors
#print axioms FiniteRamsey.finiteRamsey
#print axioms FiniteRamsey.asymmetricRamsey
#print axioms FiniteRamsey.search_total
#print axioms Ramsey.MaskBridge.census_true
#print axioms Ramsey.MaskBridge.winner_correct
#print axioms Ramsey.MaskBridge.exactRamsey_spec
#print axioms Ramsey.MaskBridge.counterColor_spec
#print axioms Ramsey.Graph.extract
#print axioms Ramsey.Graph.pentagon_obstruction
#print axioms Ramsey.ThreeColors.triangleOnSeventeen
#print axioms Ramsey.ThreeColors.sixteen_obstruction
LEAN
lean "$build_dir/Audit.lean" > "$build_dir/axioms.txt"
cat "$build_dir/axioms.txt"
if grep -Eq 'sorryAx|Classical\.choice|Lean\.ofReduceBool' "$build_dir/axioms.txt"
then
  echo "Unexpected proof dependency in the audit." >&2
  exit 1
fi
python3 -B "$project_dir/code/test_ramsey.py" -v
python3 -B "$project_dir/code/ramsey.py"
