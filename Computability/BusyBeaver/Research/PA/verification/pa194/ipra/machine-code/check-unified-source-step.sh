#!/usr/bin/env bash
set -euo pipefail
if (($# != 6)); then
  echo "usage: $0 REPO BOTH_SOURCE SELECTED_FILE_SOURCE FRAME_SOURCE UNIFIED_SOURCE PREBUILT_ROOTS_COLON_SEPARATED" >&2
  exit 2
fi
repo=$(realpath "$1")
both=$(realpath "$2")
selected=$(realpath "$3")
frame=$(realpath "$4")
unified=$(realpath "$5")
roots=$6
base="$repo/Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code"
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
  2d359448873ffcc96f347826dd511e5bf589cbe55454b56f324a8d33349f7ddd "$base/PA194Path27Header.lean" \
  61e768ee58c34f1d14942ab521a2d6eabacb2a1c231141c1356d3c9794b24fb9 "$base/PA194Path27Frame.lean" \
  1d36207c6cee69ef00453695b6c57e780d305dda2fdbc4f495aa70de759a2642 "$base/PA194SelectedFile.lean" \
  5fe2df80831c2d4ce6fefee984438cacc7f00cd4e93d6ef343252e103dedfb2d "$base/PA194Path25Input.lean" \
  15f95b7dbdf443c755255e98f2af819d06ce1c25a0ecaad0456ffd1fba47e8e1 "$base/PA194PositiveOutputFile.lean" \
  53bac9bf091ac5bc879f77761d7e20dc4e8b37751084fd6dc52a89df83263c40 "$base/PA194Path26Header.lean" \
  d272a71d57453686fad3f73a5ce8c28908134762fd91fcc3db31b1f226b4e0c3 "$base/PA194TwoPassesPositiveTo24.lean" \
  b23f7ac04368703c81233e4733d1a8b272c1419d55109184430e7391007a31c7 "$base/PA194Site26PathStep.lean" \
  a6a73d41e952fcc6413b07f2cfc533709aabdf13f4141e16540dfc3d7bbe1009 "$base/PA194Path25To26.lean" \
  11380e570860ca4bd0b682339d23145a39174259132c7daccfb26f138e28d910 "$base/PA194ZeroOutputArithmetic.lean" \
  488194572ecb882fe2ab78b8347c9c423f359d4a2e6aecd43cafa4f52460a6ad "$base/PA194TwoPassesZeroTo24.lean" \
  3424619483aa57117b3233c3cbf654f4d872beddaf529302266dffaa703c15d5 "$base/PA194Site27Step.lean" \
  c3d0c31ef4425f033cf812fd0f64dba40c3329852944d20d9088344fdfe3b918 "$base/PA194StartupSentence.lean" \
  7283ab49386aa7db9cfcb61b31431f5a7bf7efae209a755811d0a9136de42f03 "$base/PA194ZeroBranchSentence.lean" \
  76082b1cf2db24b00b9d2af3dd5d50b3d3ac7d7e077e1c3d7eb9a0ef856dd53e "$base/PA194PositiveBranchSentence.lean" \
  2353afc06a97de8243a8ccd8eaddf7de152ca835872b251741aab0aec28a699c "$both" \
  5cbfe3228ff1e423273e151b4543681ac3731847e118de662378e02a235d1923 "$selected" \
  6bb27de7f123b9294f25d12f24543482f9dda673d91f0adb43afd64c625572f9 "$frame" \
  74fded290c1b154bc7ba461470939c940a9d36450cecf1df54b1ed57c604a631 "$unified" | sha256sum -c -
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-unified-step.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$task_dir:$roots:$lake_path"
for m in PRAEqualityToIPRA PA194ZeroOutputFile PA194Path27Header PA194Path27Frame PA194SelectedFile PA194Path25Input PA194PositiveOutputFile PA194Path26Header PA194TwoPassesPositiveTo24 PA194Site26PathStep PA194Path25To26 PA194ZeroOutputArithmetic PA194TwoPassesZeroTo24 PA194Site27Step PA194StartupSentence PA194ZeroBranchSentence PA194PositiveBranchSentence; do
  cp "$base/$m.lean" "$task_dir/$m.lean"
done
cp "$both" "$task_dir/PA194BothBranchesSentence.lean"
cp "$selected" "$task_dir/PA194SelectedInputFile.lean"
cp "$frame" "$task_dir/PA194SelectedInputFrame.lean"
cp "$unified" "$task_dir/PA194UnifiedSourceStepSentence.lean"
for m in PRAEqualityToIPRA PA194ZeroOutputFile PA194Path27Header PA194Path27Frame PA194SelectedFile PA194Path25Input PA194PositiveOutputFile PA194Path26Header PA194TwoPassesPositiveTo24 PA194Site26PathStep PA194Path25To26 PA194ZeroOutputArithmetic PA194TwoPassesZeroTo24 PA194Site27Step PA194StartupSentence PA194ZeroBranchSentence PA194PositiveBranchSentence PA194BothBranchesSentence PA194SelectedInputFile PA194SelectedInputFrame PA194UnifiedSourceStepSentence; do
  echo "Checking $m"
  lake env env LEAN_PATH="$LEAN_PATH" lean -R "$task_dir" -o "$task_dir/$m.olean" "$task_dir/$m.lean" 2>&1 | tee "$task_dir/$m.log"
  if rg -q 'sorryAx' "$task_dir/$m.log"; then echo 'Unexpected sorryAx' >&2; exit 1; fi
done
for thm in modelSentence classicalPRA nativeIPRA; do
  rg -q "^'PA194UnifiedSourceStepSentence\.$thm' depends on axioms:" "$task_dir/PA194UnifiedSourceStepSentence.log"
done
for spec in 'PA194SelectedInputFile:selectedFile' 'PA194SelectedInputFrame:selectedInput_eq'; do
  module=${spec%%:*}; thm=${spec#*:}
  rg -q "^'$module\.$thm' depends on axioms:" "$task_dir/$module.log"
done
echo 'PASS: twenty-one pinned source modules checked in one output; imported transitive object overlays remain prebuilt.'
