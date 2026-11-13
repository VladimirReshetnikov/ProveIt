#!/usr/bin/env python3
"""Compare the planner and freezer with the independently reviewed direct14 versions."""
import ast,json,re,subprocess
from pathlib import Path
if not __debug__:raise RuntimeError('review requires assertions enabled')
root=Path(__file__).resolve().parents[4]
r=root/'Computability/DiophantineConsistency/research'
t=r/'ipra-standard-13-frontier';old='Computability/DiophantineConsistency/research/ipra-standard-direct14/'
def source(path):return subprocess.check_output(['git','show','dbe2ba1fcb:'+old+path],cwd=root,text=True)
def normalize_plan(s):
 s=re.sub(r'^POLICY_(?:REL|SHA256) = .*$', '',s,flags=re.M)
 return s.replace('direct14','TASK').replace('frontier13','TASK')
assert normalize_plan(source('paired_plan.py'))==normalize_plan((t/'paired_plan.py').read_text())
def normalize_freeze(s):
 s=re.sub(r'^EXPECTED=\(\n.*?^\)', 'EXPECTED=(...)',s,flags=re.M|re.S)
 return s.replace('direct14','TASK').replace('frontier13','TASK')
s=(t/'historical/freeze.py').read_text()
assert normalize_freeze(source('historical/freeze.py'))==normalize_freeze(s)
value=[n.value for n in ast.parse(s).body if isinstance(n,ast.Assign) and any(isinstance(x,ast.Name) and x.id=='EXPECTED' for x in n.targets)]
assert len(value)==1
policy=json.loads((t/'historical/task-policy.json').read_text())
assert list(ast.literal_eval(value[0]))==policy['expected_axiom_names'] and len(policy['expected_axiom_names'])==5
print('PASS_INHERITED_PLANNER_AND_FREEZER_CODE; guarded shadow unchanged; exact final five reports')
