#!/usr/bin/env python3
"""Check the production freezer's target names against the pinned real policy."""
import copy
import json
from pathlib import Path
import freeze
import prepare

if not __debug__:
    raise RuntimeError('controls require Python assertions enabled')

here = Path(__file__).resolve().parent
policy = json.loads((here / 'task-policy.json').read_text())
assert prepare.digest(here / 'task-policy.json') == prepare.POLICY_SHA256

def validate(task):
    freeze.validate_target_policy(task, policy['addition_order'], policy['target'])

validate(policy)
for field in ('expected_axiom_names', 'expected_axiom_by_module', 'target'):
    bad = copy.deepcopy(policy)
    if field == 'expected_axiom_names':
        bad[field] = []
    elif field == 'expected_axiom_by_module':
        bad[field][bad['target']] = []
    else:
        bad[field] = bad['addition_order'][0]
    try:
        validate(bad)
    except ValueError:
        pass
    else:
        raise AssertionError(('real policy mutation accepted', field))
print('PASS_SELECTED_CHECKER_REAL_FREEZER_POLICY 1 target report; 3 mutations rejected')
