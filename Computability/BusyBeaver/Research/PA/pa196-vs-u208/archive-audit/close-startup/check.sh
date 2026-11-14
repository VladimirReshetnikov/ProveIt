#!/usr/bin/env bash
set -euo pipefail

repo=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
cd "$repo"
sha256sum -c <<'PINS'
152d1d552b27baca8db0ac05b16092d9083c2ab979bb0b4e7f96a95803d9a9b0  Computability/BusyBeaver/Research/PA/jamesyc-upstream/pa196/M6/Zip.lean
e5ed123ad8e54d431472621d46b6f147a76ed94426efc9e9298f475e8ecca944  Computability/BusyBeaver/Research/PA/jamesyc-upstream/pa196/PA196/Literal.lean
PINS

task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa196-close-startup.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
mkdir -p "$task_dir/M6" "$task_dir/PA196"
: "${PA196_CLOSE_JOBS:=2}"
[[ "$PA196_CLOSE_JOBS" =~ ^[1-9][0-9]*$ ]] || { echo "PA196_CLOSE_JOBS must be a positive integer" >&2; exit 1; }
bridge=Computability/BusyBeaver/Research/PA/pa196-vs-u208/archive-audit/close-startup
python3 -B "$bridge/generate.py" "$repo" "$task_dir"
export PA196_CLOSE_TASK_DIR="$task_dir" PA196_CLOSE_REPO="$repo" PA196_CLOSE_JOBS
lake env bash -c '
set -euo pipefail
lean --version | rg -q "Lean \(version 4\.32\.0"
export LEAN_PATH="$PA196_CLOSE_TASK_DIR:${LEAN_PATH:-}"
base=Computability/BusyBeaver/Research/PA/jamesyc-upstream/pa196
lean -M3000 -j1 "$base/M6/Zip.lean" -o "$PA196_CLOSE_TASK_DIR/M6/Zip.olean"
lean -M3000 -j1 "$base/PA196/Literal.lean" -o "$PA196_CLOSE_TASK_DIR/PA196/Literal.olean"
cd "$PA196_CLOSE_TASK_DIR"
lean -M3000 -j1 Table.lean -o Table.olean
cd "$PA196_CLOSE_REPO"
lean -M3000 -j1 Computability/BusyBeaver/Research/PA/pa196-vs-u208/archive-audit/close-startup/Common.lean \
  -o "$PA196_CLOSE_TASK_DIR/Common.olean" | tee "$PA196_CLOSE_TASK_DIR/axioms.log"
cd "$PA196_CLOSE_TASK_DIR"
seq 0 14 | xargs -n 1 -P "$PA196_CLOSE_JOBS" bash -c '\''
  lean -M2500 -j1 "Batch$1.lean" -o "Batch$1.olean" > "Batch$1.log" 2>&1 || { cat "Batch$1.log"; exit 1; }
'\'' _
cat Batch*.log >> "$PA196_CLOSE_TASK_DIR/axioms.log"
lean -M3000 -j1 Final.lean | tee -a "$PA196_CLOSE_TASK_DIR/axioms.log"
if rg -q "sorryAx" "$PA196_CLOSE_TASK_DIR/axioms.log"; then
  echo "Unexpected sorryAx in theorem dependencies" >&2
  exit 1
fi
'
