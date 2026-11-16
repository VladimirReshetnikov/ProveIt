#!/usr/bin/env bash
set -euo pipefail
if (($# != 9)); then echo 'usage: REPO SOURCE FETCH_OUTPUT DISPATCH_OUTPUT DISPATCH_LOG PROJECT_FOUNDATION PACKAGE_FOUNDATION RECEIPT NEW_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); source=$(realpath "$2"); base=$(realpath "$3"); dispatch=$(realpath "$4"); log=$(realpath "$5"); project=$(realpath "$6"); package=$(realpath "$7"); receipt=$(realpath "$8"); out="$9"
for v in GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE GIT_OBJECT_DIRECTORY GIT_ALTERNATE_OBJECT_DIRECTORIES; do
 if [[ -v "$v" ]]; then echo "Refusing inherited $v" >&2; exit 2; fi
done
[[ ! -e "$out" ]] || { echo 'Output must be fresh' >&2; exit 2; }
rg -Fq 'PASS: model-length source dispatch transfers and pinned tag branches; graph and general foundations remain prebuilt.' "$log" || { echo 'Missing completed dispatch source replay' >&2; exit 1; }
check_inputs() {
 printf '%s  %s\n' \
 e3b17c6b00287bfa4aeded197f4ce8772fe4da80ac110b13e1256744e66dae93 "$receipt" \
 1af06be57f64f41cd440d51ace6de1e15130e85d451b8e87cd1030c3a6ebea00 "$source/PA194SchedulerDispatch.lean" \
 ede5c65b25f0af23f74fe4d304087ed8004bff82b43fcfca435da32ecd0d448f "$source/PA194SchedulerBranches.lean" | sha256sum -c -
 python3 - "$dispatch" "$receipt" <<'PY'
import hashlib,json,pathlib,sys
root=pathlib.Path(sys.argv[1]); expected=json.loads(pathlib.Path(sys.argv[2]).read_text())
files={p.name for p in root.glob('*.olean')}
if files != set(expected) or len(files)!=26: raise SystemExit('dispatch object set changed')
for name,h in expected.items():
 p=root/name
 if p.is_symlink() or hashlib.sha256(p.read_bytes()).hexdigest()!=h: raise SystemExit('changed dispatch object: '+name)
print('All 26 source-built dispatch objects match the receipt.')
PY
}
check_inputs
mkdir -p "$out"; out=$(realpath "$out")
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$out:$dispatch:$base:$base/foundation-view:$project:$package:$lake_path"
for m in PA194SchedulerDispatch PA194SchedulerBranches; do
 echo "Checking $m"
 lake env env LEAN_PATH="$LEAN_PATH" lean -j1 -M 7000 -R "$source" -o "$out/$m.olean" "$source/$m.lean" > "$out/$m.log" 2>&1
 if rg -q 'sorryAx|declaration uses .sorry.' "$out/$m.log"; then cat "$out/$m.log"; exit 1; fi
 rg 'depends on axioms:' "$out/$m.log"
done
for spec in PA194SchedulerDispatch:fetchDecodeDispatch PA194SchedulerBranches:fetchDecodeBranches; do
 module=${spec%%:*}; thm=${spec#*:}; rg -Fq "'$module.$thm' depends on axioms:" "$out/$module.log"
done
check_inputs
echo 'PASS: scheduler fetch/decode and actual source tag branches; source-built machine/dispatch outputs and prebuilt foundations as documented.'
