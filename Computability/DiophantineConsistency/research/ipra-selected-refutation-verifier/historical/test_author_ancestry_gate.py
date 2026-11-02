#!/usr/bin/env python3
"""Exercise runbook audit gates against toy receipts, not an independent audit."""
import ast, copy, hashlib, json, re
from pathlib import Path
if not __debug__: raise RuntimeError('gate controls require Python assertions enabled')
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
raw=(ROOT/'reviews/ipra-selected-verifier-guarded-author/state.json').read_bytes()
assert hashlib.sha256(raw).hexdigest()=='385b40c10de33c60da377b0b84ba22ee2c9103e2a32d8dffc25e84857c26af30'
state=json.loads(raw); assert state['status']=='AUTHOR_ONLY_PASS' and len(state['rows'])==10
assert sum(len(row['imports']) for row in state['rows'])==35
shell=(HERE/'REAL-RUN.md').read_text().split('```bash\n',1)[1].split('\n```',1)[0]
gates=[]
for _,body in re.findall(r"python3 - <<'([^']+)'\n(.*?)\n\1(?:\n|$)",shell,re.S):
    gates.extend(n for n in ast.walk(ast.parse(body)) if isinstance(n,ast.If) and 'added_direct_import_edges' in ast.unparse(n.test))
assert len(gates)==1
code=compile(ast.fix_missing_locations(ast.Module(body=gates,type_ignores=[])),'runbook-author-gate','exec')
def accepted(author):
    try: exec(code,{'author':author,'ValueError':ValueError})
    except ValueError: return False
    return True
toy={'parent_state_sha256':'b9ab036bf00296c9491ef6f06eb44aca805b51ab36f0d48e090d5620a55f6153','added_modules':10,'added_direct_import_edges':35}
assert accepted(toy)
for field, value in [('parent_state_sha256','wrong'),('added_modules',8),('added_direct_import_edges',27),('added_direct_import_edges',34),('added_direct_import_edges',36)]:
    wrong=copy.deepcopy(toy);wrong[field]=value;assert not accepted(wrong)
print('PASS_SELECTED_CHECKER_AUTHOR_ANCESTRY_GATE 35 accepted; wrong ancestry and counts rejected')
