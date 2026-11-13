#!/usr/bin/env python3
"""Inspect the historical AQ26 runbook without launching or changing a replay."""
import ast
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys

if not __debug__:
    raise RuntimeError('run the audit without Python optimization')

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
TOOLS = ROOT / 'research/ipra-standard-aq26/historical'
RUNBOOK = TOOLS / 'REAL-RUN.md'
PARENT = Path('/tmp/ipra-aq29-fresh-project-pair')
SNAPSHOT = Path('/tmp/ipra-aq29-fresh-source-closure-v2')
PAIR_TOOLS = ROOT / 'research/fresh-project-closure'

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def require(condition, message):
    if not condition:
        raise ValueError(message)

inputs = [Path(__file__).resolve(), RUNBOOK, TOOLS/'task-policy.json', TOOLS/'prepare.py',
          TOOLS/'freeze.py', TOOLS/'rebuild.py', TOOLS/'compare.py', TOOLS/'run_pair.py',
          TOOLS.parent/'paired_plan.py', PAIR_TOOLS/'compare.py', SNAPSHOT/'manifest.json']
before = {str(p): digest(p) for p in inputs}
text = RUNBOOK.read_text()
blocks = re.findall(r'```bash\n(.*?)\n```', text, re.S)
require(len(blocks) == 1, 'expected one runnable shell block')
syntax = subprocess.run(['bash', '-n'], input=blocks[0], text=True, capture_output=True)
require(syntax.returncode == 0, ('bash syntax', syntax.stderr))
scripts = re.findall(r"python3 - <<'PY'\n(.*?)\nPY", blocks[0], re.S)
require(len(scripts) == 4, 'expected four Python heredocs')
for script in scripts:
    ast.parse(script)

manifest = json.loads((SNAPSHOT/'manifest.json').read_text())
policy = json.loads((TOOLS/'task-policy.json').read_text())
require(digest(SNAPSHOT/'manifest.json') == '63b846158674d41beeaa99843d92008465f8e0fe5c45bb9e1fed4b78e1a2ab48', 'parent manifest pin')
require(manifest['head'] == '74f797792c2ef3f81bc9d9e8eb14a58664a3aded' and len(manifest['order']) == 1210, 'parent identity')
require(digest(TOOLS/'task-policy.json') == '500a50fdaf136f32ddd945309d0793725e0de1a006bccbc81342d92d0826976b', 'policy pin')
require(len(policy['addition_order']) == 30 and sum(map(len, policy['expected_axiom_by_module'].values())) == 79, 'AQ26 policy coverage')
require(len(policy['expected_axiom_names']) == 4 and policy['target'] == policy['addition_order'][-1], 'target reports')

required = [
    'set -euo pipefail', 'prepare.check_parent_observation(', "pair['status']!='MATCHED_PASS'",
    "[('author',0),('peer',0)]", 'mod.compare(', '--basis historical',
    "'observed_exit_code':p.returncode", "'snapshot_manifest_sha256':digest",
    "p['workspace_head_before']!=p['workspace_head_after']", '--expected-axiom-reports',
    'MATCHED_SELECTIVE_PASS 30 affected modules', 'not a current',
    'missing outer Foundation-wrapper exit observation',
]
for token in required:
    require(token in text, ('missing runbook safeguard', token))

# Unit-check the separately observed parent exit gate. The accepted observation
# below is synthetic and is never written to the actual parent location.
sys.path.insert(0, str(TOOLS))
import prepare
fake_path = Path('/synthetic/parent/pair-state.json')
good = {'observed_exit_code': 0, 'observed_stdout': 'author exit 0\npeer exit 0\nMATCHED_PASS 1210 rows\n',
        'pair_state_sha256': 'synthetic', 'pair_state_path': str(fake_path)}
prepare.check_parent_observation(good, 'synthetic', fake_path, 1210)
mutations = [dict(good, observed_exit_code=1), dict(good, observed_stdout='MATCHED_PASS 1210 rows\nextra\n'),
             dict(good, pair_state_sha256='wrong'), dict(good, pair_state_path='/wrong'),
             {k:v for k,v in good.items() if k != 'observed_exit_code'}]
for item in mutations:
    try:
        prepare.check_parent_observation(item, 'synthetic', fake_path, 1210)
    except ValueError:
        continue
    raise ValueError('parent observation mutation was accepted')

pair = json.loads((PARENT/'pair-state.json').read_text())
parent_status = pair['status']
require(parent_status in ('RUNNING', 'MATCHED_PASS', 'FAILED'), 'unexpected live parent status')
require({str(p): digest(p) for p in inputs} == before, 'audit input changed')
result = {'status': 'PASS_STATIC_RUNBOOK_AUDIT', 'inputs_sha256': before,
          'shell_blocks': len(blocks), 'python_heredocs': len(scripts),
          'parent_manifest_modules': 1210, 'addition_modules': 30,
          'per_module_diagnostics': 79, 'target_diagnostics': 4,
          'synthetic_parent_observation_negative_controls': len(mutations),
          'observed_parent_state_status': parent_status,
          'scope': 'Static source, syntax, pins and synthetic gate checks only; no real launch, '
                   'observed parent exit, Lean replay, or package/dynamic authentication.'}
out = HERE/'receipt.json'
if out.exists():
    raise RuntimeError('refusing to overwrite receipt')
out.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
print(result['status'], digest(out))
