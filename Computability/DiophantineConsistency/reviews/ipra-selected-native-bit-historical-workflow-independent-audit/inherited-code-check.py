#!/usr/bin/env python3
"""Compare production planner/freezer with the reviewed selected-checker versions."""
import ast,json,re,subprocess
from pathlib import Path
if not __debug__:raise RuntimeError('review requires assertions enabled')
root=Path(__file__).resolve().parents[4];r=root/'Computability/DiophantineConsistency/research'
t=r/'ipra-selected-native-bit';old='Computability/DiophantineConsistency/research/ipra-selected-refutation-verifier/'
def source(path):return subprocess.check_output(['git','show','c8b07a001b:'+old+path],cwd=root,text=True)
def normalize_plan(s):return re.sub(r'^POLICY_(?:REL|SHA256) = .*$', '',s,flags=re.M)
def normalize_freeze(s):return re.sub(r'^EXPECTED=\(\n.*?^\)', 'EXPECTED=(...)',s,flags=re.M|re.S)
assert normalize_plan(source('paired_plan.py'))==normalize_plan((t/'paired_plan.py').read_text())
s=(t/'historical/freeze.py').read_text();assert normalize_freeze(source('historical/freeze.py'))==normalize_freeze(s)
values=[n.value for n in ast.parse(s).body if isinstance(n,ast.Assign) and any(isinstance(x,ast.Name) and x.id=='EXPECTED' for x in n.targets)];assert len(values)==1
policy=json.loads((t/'historical/task-policy.json').read_text())
assert list(ast.literal_eval(values[0]))==policy['expected_axiom_names']==['DiophantineConsistency.IPRASelectedCheckerNativeBit.nativeBitOfClassical','DiophantineConsistency.IPRASelectedCheckerNativeBit.selected_checker_boolean_endpoints']
assert s.count('validate_target_policy(task, names, planner.TARGETS[-1])')==1
print('PASS_NATIVE_BIT_INHERITED_CODE production freezer target exactly two; shadow guard and isolation unchanged')
