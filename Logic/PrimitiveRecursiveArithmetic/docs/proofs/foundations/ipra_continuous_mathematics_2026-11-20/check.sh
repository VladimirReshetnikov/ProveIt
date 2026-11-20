#!/bin/sh
# From an extracted archive, point PROVEIT_ROOT at a ProveIt checkout.
# Requires Python 3.9+, git, Lake, and the toolchain in ProveIt's lean-toolchain.
set -eu
bundle=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
: "${PROVEIT_ROOT:?Set PROVEIT_ROOT to the ProveIt checkout.}"
cd "$PROVEIT_ROOT"
repo=$(pwd)
src=Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean
pin=5f3be02388442f16487d2dc5c2529961dd783d2b
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
trap 'exit 1' HUP INT TERM

# Check the exact dependency files even with an exported tree lacking .git.
echo "Reference ProveIt commit: $pin"
check_blob() {
  actual=$(git hash-object "$1")
  if [ "$actual" != "$2" ]; then
    echo "Source mismatch: $1 (expected $2, found $actual)" >&2
    exit 1
  fi
  echo "Verified git blob $actual  $1"
}
check_blob "$src/ConciseIPRA/Syntax.lean" a3c8ec9700382e34df9ffdeaa2f2066bbfaf1348
check_blob "$src/ConciseIPRA/Deduction.lean" 0969040f77fdd3ed9526e360e7a998584b4d9d8c
check_blob "$src/ConciseIPRA/PR.lean" 3251631592070d9ed3687cc0bf7dbd5eb452e46f
check_blob lakefile.toml 43fbd77ec99f5e010a47e5d2a0b3d289f698e58f
check_blob lake-manifest.json dc6d553da8d0ca6a9ad926545920d21f9dc6b4c7
check_blob lean-toolchain 94b9f495baff80fd9cb44aad8f4762cb3b2066fe
echo "Toolchain declaration: $(cat lean-toolchain)"
lake env lean --version
# Build only what the delivered sources import. Lake resolves packages from
# the pinned manifest. A populated mathlib cache speeds up the first build.
lake build +ConciseIPRA.PR:olean @mathlib/+Mathlib.Tactic.Linarith:olean \
  @mathlib/+Mathlib.Tactic.Ring:olean @mathlib/+Mathlib.Data.Rat.Lemmas:olean
echo "Mathlib checkout: $(git -C .lake/packages/mathlib rev-parse HEAD)"

lake env sh -s -- "$tmp" "$bundle" "$repo/$src" <<'RUN_LEAN'
set -eu
tmp=$1
bundle=$2
upstream=$3
export LEAN_PATH="$tmp:$LEAN_PATH"
mkdir -p "$tmp/ConciseIPRA"
for name in Syntax Deduction PR; do
  lean -R "$upstream" -o "$tmp/ConciseIPRA/$name.olean" "$upstream/ConciseIPRA/$name.lean"
  echo "Compiled upstream ConciseIPRA.$name"
done
for name in Abstract Complex FunctionSpace ObjectTransport Topology Variational; do
  lean -R "$bundle/lean" -o "$tmp/$name.olean" "$bundle/lean/$name.lean"
  echo "Compiled $name"
done
cat > "$tmp/Audit.lean" <<'AUDIT'
import Abstract
import Complex
import FunctionSpace
import ObjectTransport
import Topology
import Variational

#print axioms FiniteMetricLogic.formula_transport
#print axioms FiniteMetricLogic.circle_line_obstruction
#print axioms FiniteMetricLogic.glue_oscillation
#print axioms MovingCentre.same_increments
#print axioms MovingCentre.four_strips
#print axioms MovingCentre.diagonal_regular
#print axioms Precision.FunctionSpace.unitCodeSpace
#print axioms Precision.FunctionSpace.cover
#print axioms Precision.FunctionSpace.fits_retract
#print axioms Precision.ObjectTransport.Plan.derive
#print axioms PresentedTopology.overlap_segments
#print axioms Precision.Variational.minimax
AUDIT
echo "Lean kernel axiom reports for selected declarations"
lean -R "$tmp" "$tmp/Audit.lean"
RUN_LEAN

for file in "$bundle"/examples/*.py; do
  echo "Running examples/$(basename "$file")"
  python3 -B "$file"
done
echo "All six package modules compiled and all examples passed."
