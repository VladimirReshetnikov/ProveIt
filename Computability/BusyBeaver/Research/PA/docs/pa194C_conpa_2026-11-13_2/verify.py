#!/usr/bin/env python3
"""Replay the complete, portable PA194C construction and certificate suite.

This checks literal-program and symbolic-contract facts. The PA calibration
is the ordinary mathematical argument in report/pa194C_conpa.pdf, not a
proof-assistant theorem proved by this driver.
"""
from pathlib import Path
import hashlib
import json
import os
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
EXPECTED = 'd759313c03b515293fe06b12769fa1771d3829a2bad89febaa9b4391990f3a4b'
STEPS = [
    ('build', ['construction/build194c.py']),
    ('independent', ['construction/verify194c_independent.py']),
    ('commands', ['construction/command_audit/check_composite_commands.py']),
    ('novelty', ['comparison/compare_candidate.py', '--candidate',
                 'construction/output/pa194C.tm', '--output',
                 'validation/novelty.json']),
]

def main():
    if not __debug__ or os.environ.get('PYTHONOPTIMIZE'):
        raise SystemExit('Assertions must be enabled: remove -O and PYTHONOPTIMIZE.')
    logs = ROOT / 'validation'
    logs.mkdir(exist_ok=True)
    checks = []
    for name, args in STEPS:
        print(f'Checking {name} ...', flush=True)
        started = time.monotonic()
        with (logs / f'{name}.log').open('w') as stream:
            result = subprocess.run([sys.executable, '-B', *args], cwd=ROOT,
                                    stdout=stream, stderr=subprocess.STDOUT)
        checks.append({'name': name, 'exit_code': result.returncode,
                       'elapsed_seconds': round(time.monotonic() - started, 4)})
        if result.returncode:
            raise SystemExit(f'{name} failed; see validation/{name}.log')
    literal = ROOT / 'construction/output/pa194C.tm'
    digest = hashlib.sha256(literal.read_bytes()).hexdigest()
    if digest != EXPECTED:
        raise SystemExit('Reconstructed table differs from the published literal table.')
    independent = json.loads((ROOT / 'construction/independent/receipt.json').read_text())
    novelty = json.loads((logs / 'novelty.json').read_text())
    if independent['status'] != 'PASS' or not novelty['no_isomorphism_in_any_checked_orientation']:
        raise SystemExit('A final certificate did not establish its advertised result.')
    receipt = {'status': 'PASS', 'machine': 'PA194C', 'working_states': 194,
               'transition_rows': 388, 'literal_sha256': digest,
               'source_sites': independent['source_sites'],
               'universal_source_outcomes': independent['universal_source_outcomes'],
               'blank_startup_steps': independent['blank_startup_steps'],
               'no_prior_194_graph_match': True, 'checks': checks,
               'proof_scope': 'Executable certificates; ordinary PA calibration in the report; no new Lean/Rocq endpoint'}
    (logs / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))

if __name__ == '__main__':
    main()
