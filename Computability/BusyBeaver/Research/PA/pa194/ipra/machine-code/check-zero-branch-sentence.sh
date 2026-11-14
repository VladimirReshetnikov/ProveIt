#!/usr/bin/env bash
set -euo pipefail
if (($# != 3)); then
  echo "usage: $0 REPO SENTENCE_SOURCE PREBUILT_ROOTS_COLON_SEPARATED" >&2
  exit 2
fi
repo=$(realpath "$1")
sentence=$(realpath "$2")
roots=$3
base="$repo/Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code"
for v in GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE GIT_OBJECT_DIRECTORY GIT_ALTERNATE_OBJECT_DIRECTORIES; do
  if [[ -v "$v" ]]; then echo "Refusing inherited $v" >&2; exit 2; fi
done
IFS=: read -r -a root_array <<< "$roots"
for root in "${root_array[@]}"; do
  if [[ "$root" != /* || ! -d "$root" ]]; then echo "Invalid prebuilt root: $root" >&2; exit 2; fi
done
printf '%s  %s\n' \
  10479e620f643cf11aa2d1f84fd50f3f648cd634ca24cbcfb7d2290d0e94a336 "$base/PRAEqualityToIPRA.lean" \
  5da81c6be780d630c30c9f4e2daedc9bd485febf49c192d877f32f5475e1db19 "$base/PA194ZeroOutputFile.lean" \
  11380e570860ca4bd0b682339d23145a39174259132c7daccfb26f138e28d910 "$base/PA194ZeroOutputArithmetic.lean" \
  488194572ecb882fe2ab78b8347c9c423f359d4a2e6aecd43cafa4f52460a6ad "$base/PA194TwoPassesZeroTo24.lean" \
  3424619483aa57117b3233c3cbf654f4d872beddaf529302266dffaa703c15d5 "$base/PA194Site27Step.lean" \
  c3d0c31ef4425f033cf812fd0f64dba40c3329852944d20d9088344fdfe3b918 "$base/PA194StartupSentence.lean" \
  7283ab49386aa7db9cfcb61b31431f5a7bf7efae209a755811d0a9136de42f03 "$sentence" | sha256sum -c -
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-zero-branch-sentence.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$task_dir:$roots:$lake_path"
for m in PRAEqualityToIPRA PA194ZeroOutputFile PA194ZeroOutputArithmetic PA194TwoPassesZeroTo24 PA194Site27Step PA194StartupSentence; do
  cp "$base/$m.lean" "$task_dir/$m.lean"
done
cp "$sentence" "$task_dir/PA194ZeroBranchSentence.lean"
for m in PRAEqualityToIPRA PA194ZeroOutputFile PA194ZeroOutputArithmetic PA194TwoPassesZeroTo24 PA194Site27Step PA194StartupSentence PA194ZeroBranchSentence; do
  echo "Checking $m"
  lake env env LEAN_PATH="$LEAN_PATH" lean -R "$task_dir" -o "$task_dir/$m.olean" "$task_dir/$m.lean" 2>&1 | tee "$task_dir/$m.log"
  if rg -q 'sorryAx' "$task_dir/$m.log"; then echo 'Unexpected sorryAx' >&2; exit 1; fi
done
for thm in modelSentence classicalPRA nativeIPRA; do
  rg -q "^'PA194ZeroBranchSentence\.$thm' depends on axioms:" "$task_dir/PA194ZeroBranchSentence.log"
done
echo 'PASS: seven pinned source modules checked in one output; imported transitive object overlays remain prebuilt.'
