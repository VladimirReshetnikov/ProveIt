#!/usr/bin/env bash
set -euo pipefail
if (($# != 3)); then
  echo "usage: $0 REPO SENTENCE_SOURCE PREBUILT_ROOTS_COLON_SEPARATED" >&2
  exit 2
fi
repo=$(realpath "$1")
sentence=$(realpath "$2")
roots=$3
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
  c3d0c31ef4425f033cf812fd0f64dba40c3329852944d20d9088344fdfe3b918 "$base/PA194StartupSentence.lean" \
  76082b1cf2db24b00b9d2af3dd5d50b3d3ac7d7e077e1c3d7eb9a0ef856dd53e "$sentence" | sha256sum -c -
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-positive-branch-sentence.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$task_dir:$roots:$lake_path"
for m in PRAEqualityToIPRA PA194ZeroOutputFile PA194Path27Header PA194Path27Frame PA194SelectedFile PA194Path25Input PA194PositiveOutputFile PA194Path26Header PA194TwoPassesPositiveTo24 PA194Site26PathStep PA194Path25To26 PA194StartupSentence; do
  cp "$base/$m.lean" "$task_dir/$m.lean"
done
cp "$sentence" "$task_dir/PA194PositiveBranchSentence.lean"
for m in PRAEqualityToIPRA PA194ZeroOutputFile PA194Path27Header PA194Path27Frame PA194SelectedFile PA194Path25Input PA194PositiveOutputFile PA194Path26Header PA194TwoPassesPositiveTo24 PA194Site26PathStep PA194Path25To26 PA194StartupSentence PA194PositiveBranchSentence; do
  echo "Checking $m"
  lake env env LEAN_PATH="$LEAN_PATH" lean -R "$task_dir" -o "$task_dir/$m.olean" "$task_dir/$m.lean" 2>&1 | tee "$task_dir/$m.log"
  if rg -q 'sorryAx' "$task_dir/$m.log"; then echo 'Unexpected sorryAx' >&2; exit 1; fi
done
for thm in modelSentence classicalPRA nativeIPRA; do
  rg -q "^'PA194PositiveBranchSentence\.$thm' depends on axioms:" "$task_dir/PA194PositiveBranchSentence.log"
done
echo 'PASS: thirteen pinned source modules checked in one output; imported transitive object overlays remain prebuilt.'
