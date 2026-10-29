"""Read-only reauthentication after the final BinderAbsorption source update."""
from pathlib import Path
import hashlib
import json
import subprocess

R = Path('/home/codex/.codex/worktrees/46be/Proofs')
D = R / 'Computability/DiophantineConsistency/research'
def record(p):
    p = Path(p)
    b = p.read_bytes()
    return dict(path=str(p), sha256=hashlib.sha256(b).hexdigest(), bytes=len(b))
def require(b, message):
    if not b:
        raise RuntimeError(message)

plan_path = D / 'arithmetic-current-hierarchy2011-cache-plan.json'
plan_pin = record(plan_path)
require(plan_pin['sha256'] == 'b5170702be3f9d00916436b1fe26af3edc1db2defe02303d6c0bf1e671ac1c3f', 'frozen plan')
plan = json.loads(plan_path.read_text())
head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=R, text=True).strip()
require(head == '8bb2c583d0f87154a0a2e50570011a015e566029', 'current snapshot')
name = 'ZFCinPA.ModelCodedBinderAbsorption'
module = next(m for m in plan['modules'] if m['module'] == name)
require(module['mode'] == 'FRESH_CURRENT_SOURCE_REQUIRED', 'already fresh')
old = module['source']
new = record(old['path'])
require(new['sha256'] == '1c464c6993b76a1c7de25ec440323a2662e92c424c2c2b0867e7be184510f998', 'new source')
comparisons = []
for expected in plan['pins']:
    actual = record(expected['path'])
    wanted = new if expected['path'] == old['path'] else expected
    require(actual['sha256'] == wanted['sha256'], 'pin ' + actual['path'])
    require(actual['bytes'] == wanted['bytes'], 'size ' + actual['path'])
    comparisons.append(actual)
# All header changes are checked directly; only this already-fresh source changed.
before = subprocess.check_output(['git', 'show', plan['final_head'] + ':' + str(Path(old['path']).relative_to(R))], cwd=R)
require(hashlib.sha256(before).hexdigest() == old['sha256'], 'historical source snapshot')
history = D / 'arithmetic-current-hierarchy2011-plan-history'
snapshot = history / 'v4-ModelCodedBinderAbsorption.lean'
require(not snapshot.exists(), 'new historical snapshot')
snapshot.write_bytes(before)
diff = subprocess.check_output(['git', 'diff', plan['final_head'], head, '--', str(Path(old['path']).relative_to(R))], cwd=R)
require(not any(line.startswith((b'+import ', b'-import ', b'+public import ', b'-public import ')) for line in diff.splitlines()), 'unchanged imports')
diff_path = history / 'v5-BinderAbsorption.diff'
require(not diff_path.exists(), 'new diff')
diff_path.write_bytes(diff)
require(subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=R, text=True).strip() == head, 'stable snapshot')
out = D / 'arithmetic-current-hierarchy2011-current-supplement.json'
require(not out.exists(), 'new supplement')
result = dict(status='PASS_READ_ONLY_NO_COMPILER_OR_OVERLAY', snapshot_head=head,
    frozen_plan=plan_pin, module=name, previous_source=old, current_source=new,
    unchanged_imports=module['imports'], unchanged_counts=plan['counts'],
    historical_snapshot=record(snapshot), complete_diff=record(diff_path),
    script=record(__file__), comparisons=comparisons, comparison_count=len(comparisons),
    scope='Only the input pin of an already-required fresh prerequisite changes. All cached source/object and boundary pins are unchanged. Frozen baseline remains intact.')
out.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(dict(supplement=record(out), comparisons=len(comparisons)), indent=2))
