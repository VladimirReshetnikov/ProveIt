"""Reproduce the 90 frozen threshold/future-witness capture trials.

The checker is read but never edited. No network, external checkout, or local
module import is required. This complements tests/verify.py; it is not a proof
of universal soundness.
"""
from pathlib import Path
import ast
import hashlib
import json

ROOT = Path(__file__).resolve().parent.parent
CHECKER = ROOT / 'code/checker.py'
FIXTURE = ROOT / 'tests/fixtures/capture_four.json'
EXPECTED = ROOT / 'evidence/threshold_protocol_comparison.json'
source = CHECKER.read_bytes()
source_hash = hashlib.sha256(source).hexdigest()
expected = json.loads(EXPECTED.read_text())
if source_hash != expected['candidate_sha256']:
    raise SystemExit('The checker differs from the frozen 90-trial receipt.')

# Extract exactly the fixed kernel preceding its JSON-reader import. Supply
# a fresh parsed document and q=list.pop for each independent execution.
body = []
for node in ast.parse(source).body:
    if isinstance(node, (ast.Import, ast.ImportFrom)):
        break
    body.append(node)
kernel = compile(ast.Module(body=body, type_ignores=[]), str(CHECKER), 'exec')
fixture = json.loads(FIXTURE.read_text())
modes = [-10, -1, -.5, False, True, 0, 1, 1.5, 2, 2.0, 3,
         float('inf'), float('-inf'), float('nan'), None, [], {}, 'x']
trials = []
for mode in modes:
    for delta in [0, .25, -.25, .5, -.5]:
        def alter(value):
            if type(value) is int and value < 0:
                return value + delta
            if type(value) is list:
                return [alter(item) for item in value]
            return value
        document = alter(fixture)
        document[-2][1] = mode
        environment = {}
        exec(kernel, environment)
        try:
            parsed = json.loads(json.dumps(document, allow_nan=True))
            environment['q'] = parsed.pop
            environment['c']([[]], environment['q']())
            accepted = True
        except Exception:
            accepted = False
        trials.append({'mode': mode, 'delta': delta, 'accepted': accepted})

# Canonical JSON comparison also handles the deliberate NaN mode consistently.
matched = json.dumps(trials, sort_keys=True, allow_nan=True) == json.dumps(
    expected['capture_trials'], sort_keys=True, allow_nan=True)
unchanged = hashlib.sha256(CHECKER.read_bytes()).hexdigest() == source_hash
failures = [trial for trial in trials if trial['accepted']]
print(json.dumps({'candidate_sha256': source_hash, 'capture_trials': len(trials),
                  'capture_acceptances': len(failures), 'frozen_receipt_matches': matched,
                  'checker_unchanged': unchanged, 'failures': failures}, indent=2))
if not matched or not unchanged or failures or len(trials) != 90:
    raise SystemExit(1)
