#!/usr/bin/env bash
set -euo pipefail
repo=${PA194_REPO_ROOT:-$(git -C "$(dirname "$0")" rev-parse --show-toplevel)}
cd "$repo"
base=Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-first-instruction-wrapper.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
python3 - "$base/check-startup-source-frame.sh" "$task_dir/prerequisites.sh" <<'PY'
from pathlib import Path
import sys
s = Path(sys.argv[1]).read_text()
old_repo = 'repo=${PA194_REPO_ROOT:-$(git -C "$(dirname "$0")" rev-parse --show-toplevel)}'
new_repo = 'repo=$(git rev-parse --show-toplevel)'
old = 'for name in firstSeedSourceStep seedArgs_logical modelSourceSeed seedRight_sourceLayout modelDenseStartupSourceFrame; do'
new = r'''printf '%s  %s\n' \
  aed8a442b59f79560be715e917266b38fde85f3814a4eaf9ca2990208802aba6 "$PA194_BRIDGE_OVERLAY/PA194StartupSentence.olean" \
  cdb6a955eee0322c86be2909a6d60d89719bd3cefec8c4e5cfacab295083afe4 "$PA194_BRIDGE_OVERLAY/PA194PackedNumeralBridge.olean" \
  1d6b79498c7772f370065c35e7a0f11a89ba48a0d4710c609843a6cc5c1b307c "$PA194_DENSE_OVERLAY/PA194DenseStartupData.olean" \
  0839f147afdc3d3fc797c53523480ea55aeea92e39fb84d808d8d982d6c9824b "$PA194_PARENT_OVERLAY/PA196/FastRun.olean" \
  bfb3245b742173c47f94222800fdccb189f26486140bc69db844f7e9870e1deb "Computability/BusyBeaver/Research/PA/other-machines/jamesyc-upstream/pa196/PA196/FastRun.lean" | sha256sum -c
first_gen=${PA194_FIRST_INSTRUCTION_GENERATOR:-$base/generate-first-instruction.py}
first_source=${PA194_FIRST_INSTRUCTION_SENTENCE_SOURCE:-$base/PA194FirstInstructionSentence.lean}
first_source=$(realpath "$first_source")
python3 "$first_gen" --repo "$repo" --startup-data "$PA194_PARENT_OVERLAY/PA194StartupData.lean" --out "$task_dir"
for module in PA194FirstInstructionData PA194FirstInstructionBlock0 PA194FirstInstructionBlock1 PA194FirstInstructionBlock2 PA194FirstInstructionBlock3 PA194FirstInstructionComplete; do
  lake env env LEAN_PATH="$lean_path" lean -R "$task_dir" -M6000 -j1 \
    -o "$task_dir/$module.olean" "$task_dir/$module.lean" | tee -a "$task_dir/axioms.log"
done
lake env env LEAN_PATH="$lean_path" lean -R "$(dirname "$first_source")" -M6000 -j1 \
  -o "$task_dir/PA194FirstInstructionSentence.olean" "$first_source" | tee -a "$task_dir/axioms.log"
for theorem in PA194FirstInstructionData.first_eq PA194FirstInstructionData.target_eq \
    PA194FirstInstructionBlock0.checked PA194FirstInstructionBlock1.checked \
    PA194FirstInstructionBlock2.checked PA194FirstInstructionBlock3.checked \
    PA194FirstInstructionComplete.firstInstruction PA194FirstInstructionComplete.blankToSite27 \
    PA194FirstInstructionSentence.modelBlankToSite27 PA194FirstInstructionSentence.modelSentence \
    PA194FirstInstructionSentence.classicalPRA PA194FirstInstructionSentence.nativeIPRA; do
  rg -q "'$theorem'" "$task_dir/axioms.log"
done
''' + old
if s.count(old_repo) != 1 or s.count(old) != 1:
    raise SystemExit('unexpected startup source-frame checker structure')
Path(sys.argv[2]).write_text(s.replace(old_repo, new_repo, 1).replace(old, new, 1))
PY
bash -n "$task_dir/prerequisites.sh"
bash "$task_dir/prerequisites.sh"
