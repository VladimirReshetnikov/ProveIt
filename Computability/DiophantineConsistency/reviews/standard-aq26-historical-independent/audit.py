#!/usr/bin/env python3
"""Re-run AQ26 historical extension toy controls in a copied workspace."""
if not __debug__:
    raise RuntimeError('audit requires Python assertions enabled')

import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import tempfile

D = Path(__file__).resolve().parent
RESEARCH = D.parents[1] / 'research'
H = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
source = RESEARCH / 'ipra-standard-aq26'
historical = source / 'historical'
inputs = [source/'paired_plan.py', source/'author-additions.json', historical/'task-policy.json']
inputs += sorted(historical.glob('*.py'))
inputs += [RESEARCH/'fresh-project-closure'/name for name in ('rebuild.py','compare.py','run_pair.py')]
before = {str(p.resolve()): H(p) for p in inputs}

def run(command):
    p = subprocess.run(command, capture_output=True, text=True, timeout=360)
    if p.returncode:
        raise RuntimeError((command, p.returncode, p.stdout, p.stderr))
    return {'exit': p.returncode, 'stdout': p.stdout, 'stderr': p.stderr}

with tempfile.TemporaryDirectory(prefix='aq26-pair-review-') as tmp:
    dest = Path(tmp)/'Computability/DiophantineConsistency/research'
    for name in ('ipra-standard-aq26','fresh-project-closure'):
        shutil.copytree(RESEARCH/name, dest/name,
                        ignore=shutil.ignore_patterns('__pycache__','*.pdf','*.tex','*.lean',
                                                      'control-receipt.json','control-observation.json'))
    copy = dest/'ipra-standard-aq26/historical'
    controls = run(['python3', str(copy/'run_controls.py')])
    receipt = json.loads((copy/'control-receipt.json').read_text())
    if receipt['status'] != 'PASS_HISTORICAL_TOY_CONTROLS' or len(receipt['controls']) != 10:
        raise ValueError('incomplete normal and optimized-mode controls')
    source_test = (copy/'test_real_extension.py').read_text()
    anchor = '    # Omitting the same absent output companion from both records must fail.\n'
    if source_test.count(anchor) != 1:
        raise ValueError('independent mutation insertion point changed')
    injected = '''    # Forge the same forbidden nonterminal axiom in both sibling logs and states.\n    saved={}\n    for label in ('author','peer'):\n        sp=out/label/'rebuild-state.json';raw=sp.read_bytes();s=json.loads(raw);row=s['records'][0]\n        lp=Path(row['log']);log=lp.read_bytes();saved[label]=(sp,raw,lp,log)\n        assert b"'extResult' does not depend on any axioms" in log\n        lp.write_bytes(log.replace(b"'extResult' does not depend on any axioms",b"'extResult' depends on axioms: [Classical.em]"));row['log_sha256']=H(lp)\n        row['axiom_report_names']=['extResult'];row['axiom_reports']=['Classical.em'];sp.write_text(json.dumps(s))\n    compare_fails('per-module axioms')\n    for sp,raw,lp,log in saved.values():sp.write_bytes(raw);lp.write_bytes(log)\n'''
    mutation = copy/'independent_forbidden_axiom_test.py'
    mutation.write_text(source_test.replace(anchor, injected+anchor))
    forbidden = run(['python3', str(mutation)])
    if 'PASS: paired real-Lean historical extension' not in forbidden['stdout']:
        raise ValueError('independent mutation did not reach the test completion')

if {str(p.resolve()): H(p) for p in inputs} != before:
    raise ValueError('production test inputs changed during independent audit')
task = json.loads((historical/'task-policy.json').read_text())
prior = json.loads((source/'author-additions.json').read_text())
if (task['addition_order'] != prior['order'] or task['sources'] != prior['sources'] or
        task['expected_axiom_by_module'] != {n:prior['axiom_reports'].get(n,[]) for n in prior['order']} or
        len(task['addition_order']) != 30 or sum(map(len,task['expected_axiom_by_module'].values())) != 79 or
        sum(bool(x) for x in task['expected_axiom_by_module'].values()) != 22):
    raise ValueError('policy does not match the successful author manifest')

out = D/'receipt.json'
if out.exists() or out.is_symlink():
    raise ValueError('refusing to overwrite receipt')
result = {'status':'PASS_INDEPENDENT_HISTORICAL_TOY_REVIEW',
          'inputs_sha256':before,'addition_count':30,'report_count':79,
          'reporting_module_count':22,'controls':controls,'forbidden_axiom_mutation':forbidden,
          'scope':'Toy sources and a synthetic Foundation provider; no real parent or endpoint replay. '
                  'Package-transitive, dynamic and transient mutation provenance remain open.'}
out.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(result['status'],H(out))
