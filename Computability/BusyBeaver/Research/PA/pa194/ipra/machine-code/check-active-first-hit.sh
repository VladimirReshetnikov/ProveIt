#!/usr/bin/env bash
set -euo pipefail
if (($# != 6)); then
  echo "usage: $0 REPO SOURCE_DIR UNIFIED_BASELINE CODE_GRAPH_OVERLAY PROJECT_FOUNDATION PACKAGE_FOUNDATION" >&2
  exit 2
fi
repo=$(realpath "$1")
source=$(realpath "$2")
baseline=$(realpath "$3")
graph=$(realpath "$4")
project=$(realpath "$5")
package=$(realpath "$6")
for v in GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE GIT_OBJECT_DIRECTORY GIT_ALTERNATE_OBJECT_DIRECTORIES; do
  if [[ -v "$v" ]]; then echo "Refusing inherited $v" >&2; exit 2; fi
done
printf '%s  %s\n' \
  9a7d34bcc9d3fe5f98a40c36bbd3e9d8eef3a1eb029abbea483fa69efcf56872 "$source/PA194ConditionalModelLength.lean" \
  e80bebe51d09ff1f74b1205db992d82e050ce0aa2c26e5a0f5656add84ff48b4 "$source/PA194CumulativeClock.lean" \
  cb222585a8a00789886393046065e49abb070f28ed15b289e39cbac4362c5d72 "$source/PA194ClockInvariantDefinable.lean" \
  39ee862fb3dd391aff229bce7d7c52e0448c45be36bffafdc4d0f2a56a28f862 "$source/PA194ActivePrefix.lean" \
  6925aca5dde06902dbb46211fce1d41d05a1119822b037719cb11bf0963938c3 "$source/PA194ActiveFirstHit.lean" \
  d804c0fdbc8bd885d553665d8c0e3a671f0dc4db4001680f9223eb86b0c9b944 "$baseline/unified-coherent-manifest.json" \
  8b23b791247e4fb374ee0115773c59db0bd4eede5c3a14a4728758e3b6070778 "$baseline/PA194StepperCompose.olean" \
  7aa72b74a53bdc78cecc68fca7eee8192e6f556fe91c8cf4cadb899edadeb0d8 "$baseline/PA194Stepper.olean" \
  6167e5a2f0474023ec16588877f5b3abf1394efbbdaa0f388d9e0fea917c5ae2 "$graph/PA194CodeGraph.olean" \
  fbdf4fe0e3e66cce18d31e8bae714b47147633cc3295ad85ad50fd4194d28e64 "$graph/PA194ParamComp.olean" \
  703b246d062915d3d819d970aa66147219d796aa8517a6421f238ea3cc9db257 "$graph/PA194ParamRecursionDefined.olean" \
  2654808e5cfba0266f38ce2ddad33987635e8e06c3934cc131eb2a475bc1eeae "$graph/DiophantineConsistency/PRAHistoryResultGraph.olean" \
  bdfeb2a5aa83198a61c345ccb137a8bf99ef9fc23bccc7f6fc96a1d3295eb094 "$repo/Computability/BusyBeaver/Research/PA/pa195-work/pa195-calibration/PA194CodeGraph.lean" | sha256sum -c -
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-active-first-hit.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$task_dir:$baseline:$graph:$project:$package:$lake_path"
for m in PA194ConditionalModelLength PA194CumulativeClock PA194ActivePrefix PA194ClockInvariantDefinable PA194ActiveFirstHit; do
  cp "$source/$m.lean" "$task_dir/$m.lean"
  echo "Checking $m"
  lake env env LEAN_PATH="$LEAN_PATH" lean -R "$task_dir" -o "$task_dir/$m.olean" "$task_dir/$m.lean" 2>&1 | tee "$task_dir/$m.log"
  if rg -q 'sorryAx' "$task_dir/$m.log"; then echo 'Unexpected sorryAx' >&2; exit 1; fi
done
for spec in 'PA194ConditionalModelLength:simulateModelLength' 'PA194CumulativeClock:clockZero' 'PA194CumulativeClock:clockSucc' 'PA194ClockInvariantDefinable:invariantDef' 'PA194ActivePrefix:activeZero' 'PA194ActivePrefix:activeSucc' 'PA194ActivePrefix:activeContinues' 'PA194ActiveFirstHit:prefixPredicateDef' 'PA194ActiveFirstHit:prefixOrHit' 'PA194ActiveFirstHit:boundedHit' 'PA194ActiveFirstHit:hitHasActivePredecessor'; do
  module=${spec%%:*}; thm=${spec#*:}
  rg -q "^'$module\.$thm' depends on axioms:" "$task_dir/$module.log"
done
echo 'PASS: five source modules checked in one output; machine and graph/foundation overlays remain prebuilt.'
