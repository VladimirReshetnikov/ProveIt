#!/usr/bin/env python3
"""Reproduce the independent structural check and five negative controls."""
import copy
import json
from pathlib import Path
from check_and_render import check

data = json.loads(Path(__file__).with_name('expanded_proof.json').read_text())
check(data)
cases = {}
case = copy.deepcopy(data)
case['steps'][0]['formula'] = 0
cases['wrong_mp_conclusion'] = case
case = copy.deepcopy(data)
case['steps'][0]['major']['ref'] = 'd58'
cases['forward_reference'] = case
case = copy.deepcopy(data)
case['steps'][0]['guards'] = []
cases['removed_side_condition'] = case
case = copy.deepcopy(data)
case['goals']['rho8_all']['formula'] = 0
cases['changed_public_goal'] = case
case = copy.deepcopy(data)
case['row_guards'] = []
cases['unrestricted_row_leaf'] = case
results = {'positive': True, 'negative_controls': {}}
for name, case in cases.items():
    try:
        check(case)
    except ValueError as err:
        results['negative_controls'][name] = {'rejected': True, 'message': str(err)}
    else:
        raise RuntimeError('negative control accepted: ' + name)
print(json.dumps(results, indent=2))
