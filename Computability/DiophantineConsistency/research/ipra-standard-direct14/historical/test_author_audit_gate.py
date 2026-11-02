#!/usr/bin/env python3
"""Exercise the actual runbook author-ancestry gate with its audited receipt."""
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
receipt = ROOT / 'reviews/ipra-standard-direct14-guarded-author-independent-audit/receipt.json'
raw = receipt.read_bytes()
assert hashlib.sha256(raw).hexdigest() == 'd0c84f8c77bd9f64b6aba64b237f83e405ed9573ac82256243f781a39fff7859'
author = json.loads(raw)
assert author['status'] == 'PASS_INDEPENDENT_DIRECT14_AUTHOR_ARTIFACT_AUDIT'
text = (HERE / 'REAL-RUN.md').read_text()
shell = text.split('```bash\n', 1)[1].split('\n```', 1)[0]
blocks = re.findall(r"python3 - <<'([^']+)'\n(.*?)\n\1(?:\n|$)", shell, re.S)
gates = []
for _, body in blocks:
    tree = ast.parse(body)
    for node in ast.walk(tree):
        if isinstance(node, ast.If) and 'added_direct_import_edges' in ast.unparse(node.test):
            gates.append(node)
assert len(gates) == 1
gate = compile(ast.fix_missing_locations(ast.Module(body=gates, type_ignores=[])), 'runbook-author-gate', 'exec')

def accepted(candidate):
    try:
        exec(gate, {'author': candidate, 'ValueError': ValueError})
    except ValueError:
        return False
    return True

assert author['added_direct_import_edges'] == 16 and accepted(author)
for count in (11, 15, 17):
    altered = copy.deepcopy(author)
    altered['added_direct_import_edges'] = count
    assert not accepted(altered), count
print('PASS_DIRECT14_REAL_AUTHOR_ANCESTRY_GATE 16 accepted; 11, 15, 17 rejected')
