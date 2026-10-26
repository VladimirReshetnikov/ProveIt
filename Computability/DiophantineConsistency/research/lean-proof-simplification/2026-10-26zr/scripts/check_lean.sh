#!/bin/sh
set -eu
task_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$task_root"
lake env lean --version
for task_source in lean/RotationPeriod.lean lean/Capacity.lean lean/InternalQuotientGap.lean lean/TwoRowZeroTest.lean lean/AffinePositions.lean
do
  printf '\nChecking %s\n' "$task_source"
  lake env lean "$task_source"
done
