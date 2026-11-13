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
state_path = ROOT / 'reviews/ipra-selected-native-bit-guarded-author/state.json'
raw = state_path.read_bytes()
assert hashlib.sha256(raw).hexdigest() == '3bee2db67ca881cf02458d6688f3b8252eab6cc36ce2b7a610d2ef2a84127321'
state = json.loads(raw)
assert state['status'] == 'AUTHOR_ONLY_PASS' and len(state['rows']) == 11
direct_edges = sum(len(row['imports']) for row in state['rows'])
assert direct_edges == 37
audit = ROOT / 'reviews/ipra-selected-native-bit-guarded-author-independent-audit'
receipt_raw = (audit / 'receipt.json').read_bytes()
terminal_raw = (audit / 'terminal-observation.json').read_bytes()
assert hashlib.sha256(receipt_raw).hexdigest() == 'e47a76773c98a19ffdf90165ffda5b2f338c9b03bb31f92cc7aa8403656c8516'
assert hashlib.sha256(terminal_raw).hexdigest() == 'ab4a876dc8e60b13f55f9b4ee43b3e3fdd29bd8a8871265e4a13d6671e1d37b9'
author = json.loads(receipt_raw)
terminal = json.loads(terminal_raw)
assert author['status'] == 'PASS_INDEPENDENT_SELECTED_NATIVE_BIT_AUTHOR_ARTIFACT_AUDIT'
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
for count in (35, 36, 38):
    wrong = copy.deepcopy(author)
    wrong['added_direct_import_edges'] = count
    assert not accepted(wrong)
print('PASS_SELECTED_NATIVE_BIT_AUTHOR_ANCESTRY_GATE 37 accepted; 35, 36, 38 rejected')
