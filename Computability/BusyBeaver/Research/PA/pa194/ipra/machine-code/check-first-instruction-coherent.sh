#!/usr/bin/env bash
set -euo pipefail
repo=${PA194_REPO_ROOT:-$(git -C "$(dirname "$0")" rev-parse --show-toplevel)}
cd "$repo"
base=Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code
wrapper_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-first-instruction-coherent-wrapper.XXXXXXXX")
trap 'rm -rf "$wrapper_dir"' EXIT
python3 - "$base/check-dense-startup-coherent.sh" "$wrapper_dir/combined.sh" <<'PY'
from pathlib import Path
import sys
source = Path(sys.argv[1]).read_text()
marker = 'for m in PA194ModelDenseStartup PA194StartupSentence; do'
if source.count(marker) != 1:
    raise SystemExit('unexpected coherent startup checker structure')
extra = r'''
# Rebuild the source-file layout and first-instruction semantics in the same
# common object directory, using the already rebuilt machine and seed objects.
for m in PA194StateFifteen PA194UnaryRuns PA194RegisterFile PA194RegisterFileStandard PA194RegisterPermutation PA194ZeroRuns; do
  lean -M6000 -j1 -o "$task_dir/$m.olean" "$base/$m.lean" | tee "$task_dir/$m.first-audit.log"
  if rg -q 'sorryAx' "$task_dir/$m.first-audit.log"; then exit 1; fi
done
lean -M6000 -j1 -o "$task_dir/PA194FetchPrefixBinding.olean" \
  Computability/BusyBeaver/Research/PA/pa194-work/pa194-command-source/PA194FetchPrefixBinding.lean
lean -M6000 -j1 -o "$task_dir/PA194StartupSourceFrame.olean" "$base/PA194StartupSourceFrame.lean" | tee "$task_dir/source-frame.first-audit.log"
python3 "$base/generate-first-instruction.py" --repo "$repo" --startup-data "$task_dir/PA194StartupData.lean" --out "$task_dir"
: > "$task_dir/first-instruction.audit.log"
for m in PA194FirstInstructionData PA194FirstInstructionBlock0 PA194FirstInstructionBlock1 PA194FirstInstructionBlock2 PA194FirstInstructionBlock3 PA194FirstInstructionComplete; do
  lean -M6000 -j1 -R "$task_dir" -o "$task_dir/$m.olean" "$task_dir/$m.lean" | tee -a "$task_dir/first-instruction.audit.log"
done
lean -M6000 -j1 -o "$task_dir/PA194FirstInstructionSentence.olean" "$base/PA194FirstInstructionSentence.lean" | tee -a "$task_dir/first-instruction.audit.log"
if rg -q 'sorryAx' "$task_dir/source-frame.first-audit.log" "$task_dir/first-instruction.audit.log"; then
  echo 'Unexpected sorryAx in first-instruction theorem dependencies' >&2
  exit 1
fi
for theorem in PA194FirstInstructionData.first_eq PA194FirstInstructionData.target_eq \
    PA194FirstInstructionBlock0.checked PA194FirstInstructionBlock1.checked \
    PA194FirstInstructionBlock2.checked PA194FirstInstructionBlock3.checked \
    PA194FirstInstructionComplete.firstInstruction PA194FirstInstructionComplete.blankToSite27 \
    PA194FirstInstructionSentence.modelBlankToSite27 PA194FirstInstructionSentence.modelSentence \
    PA194FirstInstructionSentence.classicalPRA PA194FirstInstructionSentence.nativeIPRA; do
  rg -Fq "'$theorem'" "$task_dir/first-instruction.audit.log"
done
for theorem in firstSeedSourceStep seedArgs_logical modelSourceSeed seedRight_sourceLayout modelDenseStartupSourceFrame; do
  rg -Fq "'PA194StartupSourceFrame.$theorem'" "$task_dir/source-frame.first-audit.log"
done
'''
Path(sys.argv[2]).write_text(source + '\n' + extra)
PY
bash -n "$wrapper_dir/combined.sh"
# This supplies only the repository path; it does not override Git internals.
export PA194_AUDIT_REPO_OVERRIDE="$repo"
bash "$wrapper_dir/combined.sh"
