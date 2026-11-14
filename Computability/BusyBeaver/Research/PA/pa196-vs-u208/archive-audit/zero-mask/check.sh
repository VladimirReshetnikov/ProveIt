#!/usr/bin/env bash
set -euo pipefail

repo=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
cd "$repo"
sha256sum -c <<'PINS'
960070a24cc17646d9e814e4f665b8e01337d363a4e345a036ea9dde8b82da76  docs/incoming/pa_tm_extended_research_2026-11-13.zip
4edcf4eb98b24999f610f06a22d943db68c7c2cae8d96160bbf614c75821738a  Computability/BusyBeaver/Research/PA/jamesyc-upstream/pa196/M6/Source/Syntax.lean
8689481036b4c29d1a8ce7fec25e6ae12e8ac54fd4a86f23fb9cb5ee01b39f38  Computability/BusyBeaver/Research/PA/jamesyc-upstream/pa196/M6/Source/Semantics.lean
98bdd0185ee5db469d400e32d349d20368ac117742386b6e253d3636c677cdd8  Computability/BusyBeaver/Research/PA/jamesyc-upstream/pa196/M6/Source/PathTrie.lean
09896e31c4d5d3fd5cf636d3cfea0dddfb4396fe48781aaf5ab90f151878b8fb  Computability/BusyBeaver/Research/PA/jamesyc-upstream/pa196/M6/FastResolve.lean
8f4b3d4ce58cff2f9787300c206092fcf1e62410b5bad9a5fe54216da39209f0  Computability/BusyBeaver/Research/PA/jamesyc-upstream/pa196/M6/TreeSite.lean
8c7c6c6884ecbb8f56e893404bb81162db15ef3dd6fd3212881a93994d63d872  Computability/BusyBeaver/Research/PA/jamesyc-upstream/pa196/PA196/Program.lean
PINS

task_dir=$(mktemp -d "${TMPDIR:-/tmp}/pa196-zero-mask.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
mkdir -p "$task_dir/M6/Source" "$task_dir/PA196"
: "${PA196_ZERO_JOBS:=2}"
[[ "$PA196_ZERO_JOBS" =~ ^[1-9][0-9]*$ ]] || { echo "PA196_ZERO_JOBS must be a positive integer" >&2; exit 1; }
bridge=Computability/BusyBeaver/Research/PA/pa196-vs-u208/archive-audit/zero-mask
python3 -B "$bridge/generate.py" "$repo" "$task_dir"
export PA196_ZERO_TASK_DIR="$task_dir" PA196_ZERO_REPO="$repo" PA196_ZERO_JOBS
lake env bash -c '
set -euo pipefail
lean --version | rg -q "Lean \(version 4\.32\.0"
export LEAN_PATH="$PA196_ZERO_TASK_DIR:${LEAN_PATH:-}"
base=Computability/BusyBeaver/Research/PA/jamesyc-upstream/pa196
for mod in M6/Source/Syntax M6/Source/Semantics M6/Source/PathTrie M6/FastResolve M6/TreeSite PA196/Program; do
  lean -M4000 -j1 "$base/$mod.lean" -o "$PA196_ZERO_TASK_DIR/$mod.olean"
done
lean -M4000 -j1 Computability/BusyBeaver/Research/PA/pa196-vs-u208/archive-audit/zero-mask/Transfer.lean \
  -o "$PA196_ZERO_TASK_DIR/Transfer.olean" | tee "$PA196_ZERO_TASK_DIR/axioms.log"
lean -M4000 -j1 Computability/BusyBeaver/Research/PA/pa196-vs-u208/archive-audit/zero-mask/Abstraction.lean \
  -o "$PA196_ZERO_TASK_DIR/Abstraction.olean" | tee -a "$PA196_ZERO_TASK_DIR/axioms.log"
for file in MaskEncoding MaskSets CertificateBridge; do
  lean -M4000 -j1 "Computability/BusyBeaver/Research/PA/pa196-vs-u208/archive-audit/zero-mask/$file.lean" \
    -o "$PA196_ZERO_TASK_DIR/$file.olean" | tee -a "$PA196_ZERO_TASK_DIR/axioms.log"
done
cd "$PA196_ZERO_TASK_DIR"
for file in Closure Zero Rows; do
  lean -M4000 -j1 "$file.lean" -o "$file.olean" | tee -a "$PA196_ZERO_TASK_DIR/axioms.log"
done
lean -M1600 -j1 SegmentBase.lean -o SegmentBase.olean
cd "$PA196_ZERO_REPO"
lean -M1600 -j1 Computability/BusyBeaver/Research/PA/pa196-vs-u208/archive-audit/zero-mask/SegmentAssembly.lean \
  -o "$PA196_ZERO_TASK_DIR/SegmentAssembly.olean" | tee -a "$PA196_ZERO_TASK_DIR/axioms.log"
cd "$PA196_ZERO_TASK_DIR"
for begin in 0 256 512 768; do
  lean -M1600 -j1 "segment$begin.lean" -o "segment$begin.olean" | tee -a "$PA196_ZERO_TASK_DIR/axioms.log"
done
seq 1024 64 3808 | xargs -n 1 -P "$PA196_ZERO_JOBS" bash -c '\''
  lean -M1600 -j1 "part$1.lean" -o "part$1.olean" > "part$1.log" 2>&1 || { cat "part$1.log"; exit 1; }
'\'' _
cat part*.log >> "$PA196_ZERO_TASK_DIR/axioms.log"
seq 1024 256 3584 | xargs -n 1 -P "$PA196_ZERO_JOBS" bash -c '\''
  lean -M1600 -j1 "aggregate$1.lean" -o "aggregate$1.olean" > "aggregate$1.log" 2>&1 || { cat "aggregate$1.log"; exit 1; }
'\'' _
cat aggregate*.log >> "$PA196_ZERO_TASK_DIR/axioms.log"
lean -M1600 -j1 SegmentAll2.lean -o SegmentAll2.olean | tee -a "$PA196_ZERO_TASK_DIR/axioms.log"
cd "$PA196_ZERO_REPO"
lean -M4000 -j1 Computability/BusyBeaver/Research/PA/pa196-vs-u208/archive-audit/zero-mask/Conclusion.lean \
  -o "$PA196_ZERO_TASK_DIR/Conclusion.olean" | tee -a "$PA196_ZERO_TASK_DIR/axioms.log"
lean -M1600 -j1 Computability/BusyBeaver/Research/PA/pa196-vs-u208/archive-audit/zero-mask/SegmentEnd.lean \
  -o "$PA196_ZERO_TASK_DIR/SegmentEnd.olean" | tee -a "$PA196_ZERO_TASK_DIR/axioms.log"
if rg -q "sorryAx" "$PA196_ZERO_TASK_DIR/axioms.log"; then
  echo "Unexpected sorryAx in theorem dependencies" >&2
  exit 1
fi
'
