#!/usr/bin/env python3
"""Check the runbook gate against the guarded author state's direct inputs."""
import ast
import copy
import hashlib
import json
import re
from pathlib import Path

if not __debug__:
    raise RuntimeError('gate controls require Python assertions enabled')
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
state_path = ROOT / 'reviews/ipra-standard-13-frontier-guarded-author/state.json'
raw = state_path.read_bytes()
assert hashlib.sha256(raw).hexdigest() == 'b6d867bb44502dd78f3b833ebe2c4c23b1a5875a4f065e538abbe9fd0fedfae4'
state = json.loads(raw)
assert state['status'] == 'AUTHOR_ONLY_PASS' and len(state['rows']) == 8
direct_edges = sum(len(row['imports']) for row in state['rows'])
assert direct_edges == 27
audit = ROOT / 'reviews/ipra-standard-13-frontier-guarded-author-independent-audit'
receipt_raw = (audit / 'receipt.json').read_bytes()
terminal_raw = (audit / 'terminal-observation.json').read_bytes()
assert hashlib.sha256(receipt_raw).hexdigest() == '8c7f44e394b42ee0dfc0233845fde3704d6301cb132c37300099678da812c792'
assert hashlib.sha256(terminal_raw).hexdigest() == '9711c0239df6f2391e930b32bc7cec36a3e9f5245a2b29f378b8a530c84e79a9'
author = json.loads(receipt_raw)
terminal = json.loads(terminal_raw)
assert author['status'] == 'PASS_INDEPENDENT_FRONTIER13_AUTHOR_ARTIFACT_AUDIT'
assert terminal['observed_exit_code'] == 0 and terminal['receipt_sha256'] == hashlib.sha256(receipt_raw).hexdigest()
assert author['parent_state_sha256'] == state['parent_state_sha256']
assert author['added_modules'] == len(state['rows']) and author['added_direct_import_edges'] == direct_edges
shell = (HERE / 'REAL-RUN.md').read_text().split('```bash\n', 1)[1].split('\n```', 1)[0]
gates = []
for _, body in re.findall(r"python3 - <<'([^']+)'\n(.*?)\n\1(?:\n|$)", shell, re.S):
    gates.extend(node for node in ast.walk(ast.parse(body))
                 if isinstance(node, ast.If) and 'added_direct_import_edges' in ast.unparse(node.test))
assert len(gates) == 1
code = compile(ast.fix_missing_locations(ast.Module(body=gates, type_ignores=[])), 'runbook-author-gate', 'exec')
def accepted(candidate):
    try:
        exec(code, {'author': candidate, 'ValueError': ValueError})
    except ValueError:
        return False
    return True
assert accepted(author)
for count in (19, 26, 28):
    wrong = copy.deepcopy(author)
    wrong['added_direct_import_edges'] = count
    assert not accepted(wrong)
print('PASS_FRONTIER13_AUTHOR_ANCESTRY_GATE 27 accepted; 19, 26, 28 rejected')
