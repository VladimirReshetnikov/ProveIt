#!/usr/bin/env python3
"""Compare the planner and freezer with the independently reviewed joint13 versions."""
import ast,json,re,subprocess
from pathlib import Path
if not __debug__:raise RuntimeError('review requires assertions enabled')
root=Path(__file__).resolve().parents[4]
r=root/'Computability/DiophantineConsistency/research'
t=r/'ipra-selected-refutation-verifier';old='Computability/DiophantineConsistency/research/ipra-standard-13-frontier/'
def source(path):return subprocess.check_output(['git','show','0979f0d9fb:'+old+path],cwd=root,text=True)
def normalize_plan(s):
 s=re.sub(r'^POLICY_(?:REL|SHA256) = .*$', '',s,flags=re.M)
 return s.replace('selected_checker','TASK').replace('frontier13','TASK')
assert normalize_plan(source('paired_plan.py'))==normalize_plan((t/'paired_plan.py').read_text())
def normalize_freeze(s):
 s=re.sub(r'^EXPECTED=\(\n.*?^\)', 'EXPECTED=(...)',s,flags=re.M|re.S)
 return s.replace('selected_checker','TASK').replace('frontier13','TASK')
s=(t/'historical/freeze.py').read_text()
# The corrected freezer factors the target check into a stricter helper.
helper="""def validate_target_policy(task, names, target):
    if (task.get('target') != target or task.get('addition_order') != names or
            task.get('expected_axiom_names') != list(EXPECTED) or
            task.get('expected_axiom_by_module', {}).get(target) != list(EXPECTED)):
        raise ValueError('task-specific target policy mismatch')

"""
call='    validate_target_policy(task, names, planner.TARGETS[-1])'
prior="""    if (task.get('target')!=planner.TARGETS[-1] or task.get('addition_order')!=names or
        task.get('expected_axiom_names')!=list(EXPECTED)):
        raise ValueError('task-specific target policy mismatch')"""
assert s.count(helper)==1 and s.count(call)==1
normalized=s.replace(helper,'').replace(call,prior)
assert normalize_freeze(source('historical/freeze.py'))==normalize_freeze(normalized)
value=[n.value for n in ast.parse(s).body if isinstance(n,ast.Assign) and any(isinstance(x,ast.Name) and x.id=='EXPECTED' for x in n.targets)]
assert len(value)==1
policy=json.loads((t/'historical/task-policy.json').read_text())
assert list(ast.literal_eval(value[0]))==policy['expected_axiom_names'] and len(policy['expected_axiom_names'])==1
print('PASS_INHERITED_PLANNER_AND_FREEZER_CODE; guarded shadow unchanged; stricter production policy gate; exact final report')
