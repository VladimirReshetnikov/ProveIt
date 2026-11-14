#!/usr/bin/env bash
set -euo pipefail
: "${IPRA_LEAN_OVERLAY:?Set IPRA_LEAN_OVERLAY to the audited PR/iPRA object directory}"
: "${IPRA_FOUNDATION_OVERLAY:?Set IPRA_FOUNDATION_OVERLAY to the audited Foundation object directory}"
repo=${PA194_AUDIT_REPO_OVERRIDE:-$(git -C "$(dirname "$0")" rev-parse --show-toplevel)}
cd "$repo"
IPRA_LEAN_OVERLAY=$(realpath "$IPRA_LEAN_OVERLAY")
IPRA_FOUNDATION_OVERLAY=$(realpath "$IPRA_FOUNDATION_OVERLAY")
export IPRA_LEAN_OVERLAY IPRA_FOUNDATION_OVERLAY
# Reject PA194 machine-object fallback roots, so every machine-specific object
# used below comes from this new common build directory.
python3 - "$IPRA_LEAN_OVERLAY" "$IPRA_FOUNDATION_OVERLAY" <<'PYCHK'
from pathlib import Path
import subprocess
import sys
roots = [Path(p) for p in sys.argv[1:]] + [Path(p) for p in subprocess.check_output(
    ['lake','env','printenv','LEAN_PATH'], text=True).strip().split(':') if p]
names = ('BinaryTapeCodes','TapeStepCodes','ConfigurationStep','PackedClock',
         'PackedStandard','PackedRootModel','PackedDecoderModel',
         'PackedIterationModel','TableDispatch','TableModelSemantics',
         'ConfigurationStandard','PRAEqualityToIPRA')
for root in roots:
    if not root.is_dir():
        continue
    bad = [p for pattern in ('PA194*.olean','PA195*.olean','PA196*.olean') for p in root.glob(pattern)]
    bad += [root / (name + '.olean') for name in names if (root / (name + '.olean')).exists()]
    bad += [root / name for name in ('M6','PA196','PA194') if (root / name).exists()]
    if bad:
        raise SystemExit(f'machine-specific fallback object/directory in {root}: {bad[0]}')
PYCHK
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-coherent-startup.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
export PA194_AUDIT_TASK_DIR="$task_dir" PA194_AUDIT_REPO="$repo"
python3 - "$repo" "$task_dir" <<'PYPREP'
from pathlib import Path
import re
import sys
root, out = map(Path,sys.argv[1:])
p = root / 'Computability/BusyBeaver/Research/PA/pa194-work/pa194-startup/check.sh'
s = p.read_text()
old = 'task_dir=$(mktemp -d /dev/shm/pa194-startup.XXXXXXXX)'
if s.count(old) != 1:
    raise SystemExit('unexpected parent startup checker task directory')
s = s.replace(old,'task_dir=$PA194_AUDIT_TASK_DIR',1)
old = "trap 'rm -rf \"$task_dir\"' EXIT"
if s.count(old) != 1:
    raise SystemExit('unexpected parent startup checker cleanup')
s = s.replace(old,'',1)
(out / 'parent.sh').write_text(s)
p = root / 'Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-stepper-zip.sh'
s = p.read_text()
old = 'repo=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)'
if s.count(old) != 1:
    raise SystemExit('unexpected stepper checker repository discovery')
s = s.replace(old,'repo=$PA194_AUDIT_REPO',1)
s,n = re.subn(r'^task_dir=\$\(mktemp[^\n]*\)[ \t]*$',
              'task_dir=$PA194_AUDIT_TASK_DIR',s,count=1,flags=re.M)
if n != 1:
    raise SystemExit('unexpected stepper checker task directory')
old = "trap 'rm -rf \"$task_dir\"' EXIT"
if s.count(old) != 1:
    raise SystemExit('unexpected stepper checker cleanup')
s = s.replace(old,'',1)
(out / 'stepper.sh').write_text(s)
PYPREP
bash -n "$task_dir/parent.sh"
bash -n "$task_dir/stepper.sh"
bash "$task_dir/parent.sh" --start-block 0 --stop-block 1
bash "$task_dir/stepper.sh"
task_dir=$PA194_AUDIT_TASK_DIR
base=Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code
export LEAN_PATH="$task_dir:$IPRA_LEAN_OVERLAY:$IPRA_FOUNDATION_OVERLAY:$(lake env printenv LEAN_PATH)"
for m in PA194BinaryDouble PA194FiniteControls PA194StateOne PRAEqualityToIPRA PA194StandardCodeBridge PA194StandardStepperBridge PA194PackedNumeralBridge; do
  lean -M6000 -j1 -o "$task_dir/$m.olean" "$base/$m.lean" | tee "$task_dir/$m.audit.log"
  if rg -q 'sorryAx' "$task_dir/$m.audit.log"; then exit 1; fi
done
printf '%s  %s\n' 7cd4f1ae6f6f5d0ee476840d6e7aa447500a3ec4e2293f6830e672cca735bbd7 "$task_dir/PA194StartupData.lean" | sha256sum -c
python3 "$base/generate-dense-startup.py" "$PWD" "$task_dir"
lean -M6000 -j1 -R "$task_dir" -o "$task_dir/PA194DenseStartupData.olean" "$task_dir/PA194DenseStartupData.lean" | tee "$task_dir/data.audit.log"
if rg -q 'sorryAx' "$task_dir/data.audit.log"; then exit 1; fi
python3 - "$task_dir" "${PA194_AUDIT_BLOCK_GROUPS:-46}" <<'PY'
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
import subprocess
import sys
root = Path(sys.argv[1])
count = int(sys.argv[2])
modules = sorted(root.glob('PA194DenseStartupBlock*.lean'))
if len(modules) != 46 or not 1 <= count <= 46:
    raise SystemExit('invalid generated batch list or audit count')
def check(path):
    log=path.with_suffix('.audit.log')
    with log.open('w') as out:
        run=subprocess.run(['lean','-M6000','-j1','-R',str(root),'-o',str(path.with_suffix('.olean')),str(path)],stdout=out,stderr=subprocess.STDOUT)
    return path,run.returncode,log.read_text()
failed=[]
with ThreadPoolExecutor(max_workers=2) as pool:
    for future in as_completed([pool.submit(check,p) for p in modules[:count]]):
        path,rc,output=future.result()
        print(path.name, 'passed' if not rc and 'sorryAx' not in output else 'FAILED',flush=True)
        if rc or 'sorryAx' in output:
            print(output,file=sys.stderr);failed.append(path.name)
if failed: raise SystemExit('failed: '+', '.join(failed))
PY
if [ "${PA194_AUDIT_BLOCK_GROUPS:-46}" != 46 ]; then
  echo 'PARTIAL audit: startup theorem and model sentence not yet checked.'
  exit 0
fi
lean -M6000 -j1 -R "$task_dir" -o "$task_dir/PA194DenseStartupComplete.olean" "$task_dir/PA194DenseStartupComplete.lean" | tee "$task_dir/completion.audit.log"
if rg -q 'sorryAx' "$task_dir/completion.audit.log"; then exit 1; fi
for m in PA194ModelDenseStartup PA194StartupSentence; do
  lean -M6000 -j1 -o "$task_dir/$m.olean" "$base/$m.lean" | tee "$task_dir/$m.audit.log"
  if rg -q 'sorryAx' "$task_dir/$m.audit.log"; then exit 1; fi
done
