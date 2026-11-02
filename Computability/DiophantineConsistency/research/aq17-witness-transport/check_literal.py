#!/usr/bin/env python3
"""Check the exact AQ17 literal against the pinned finite circuit."""
import hashlib,json
from pathlib import Path
if not __debug__: raise RuntimeError('assertions required')
D=Path(__file__).resolve().parent
g=D.parent/'aq22-positive-binding-survey/candidate17.json'
assert hashlib.sha256(g.read_bytes()).hexdigest()=='760b9e7babbb559b7175344915456fdc3d9bd8ce85382873d4915faf2cd76d81'
c=json.loads(g.read_text());s=(D/'draft-src/AdaptiveAQ17Literal.lean').read_text()
def check(s):
 marker='def literal (p : Fin 4 → ℤ) : Expr (Fin 17) :=\n'
 assert s.count(marker)==1
 body=s.split(marker,1)[1].split('\nend DiophantineConsistency.AdaptiveAQ17Literal',1)[0]
 expected=[f'  let {name} : Expr (Fin 17) := .var {i}' for i,name in enumerate(c['witnesses'])]
 expected += [f'  let {name} : Expr (Fin 17) := .constant (p {i})' for i,name in enumerate(c['fixed_numerals'])]
 expected += [f'  let {name} := {a} {op} {b}' for name,op,a,b in c['source']]
 expected += [f"  {c['output']}"]
 assert len(c['witnesses'])==17 and len(c['source'])==99 and body.splitlines()==expected
check(s)
for old,new in [('.var 0','.var 1'),('.constant (p 0)','.constant (p 1)'),('let qm := J * beta','let qm := J + beta'),('  bindingSurveySum6\nend ','  bindingSurveySum5\nend ')]:
 t=s.replace(old,new,1);assert t!=s
 try:check(t)
 except AssertionError:pass
 else:raise AssertionError('mutation survived')
print('PASS_AQ17_LITERAL_BINDING 17 variables 4 ports 99 gates 4 mutations')
