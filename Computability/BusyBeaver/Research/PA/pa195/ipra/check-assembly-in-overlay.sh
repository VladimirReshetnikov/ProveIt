#!/usr/bin/env bash
set -euo pipefail
: "${PA196_TASK_CHECK_DIR:?Run check-assembly.sh instead of invoking this script directly}"
python3 -B Computability/BusyBeaver/Research/PA/pa195/ipra/generate.py "$PWD" "$PA196_TASK_CHECK_DIR"
(
  cd "$PA196_TASK_CHECK_DIR"
  lean -M6000 -j1 PA195Literal.lean -o PA195Literal.olean
  lean -M6000 -j1 PA195Rows.lean -o PA195Rows.olean
)
bridge195=Computability/BusyBeaver/Research/PA/pa195/ipra
for task_mod in PA195Bounded PA195Endpoint PA195ForwardGG PA195PRAAssembly; do
  lean -M6000 -j1 "$bridge195/$task_mod.lean" -o "$PA196_TASK_CHECK_DIR/$task_mod.olean" | tee -a "$PA196_TASK_CHECK_DIR/axioms.log"
done
