#!/usr/bin/env bash
set -euo pipefail
: "${PA196_TASK_CHECK_DIR:?Run check-assembly.sh instead of invoking this script directly}"
python3 -B Computability/BusyBeaver/Research/PA/pa194/ipra/generate.py "$PWD" "$PA196_TASK_CHECK_DIR"
(
  cd "$PA196_TASK_CHECK_DIR"
  lean -M6000 -j1 PA194Literal.lean -o PA194Literal.olean
  lean -M6000 -j1 PA194Rows.lean -o PA194Rows.olean
)
bridge195=Computability/BusyBeaver/Research/PA/pa194/ipra
for task_mod in PA194Bounded PA194Endpoint PA194ForwardGG PA194PRAAssembly; do
  lean -M6000 -j1 "$bridge195/$task_mod.lean" -o "$PA196_TASK_CHECK_DIR/$task_mod.olean" | tee -a "$PA196_TASK_CHECK_DIR/axioms.log"
done
