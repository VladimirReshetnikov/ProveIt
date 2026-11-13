#!/usr/bin/env python3
"""Check the exact AQ16 literal against the pinned finite circuit."""
import hashlib,json
from pathlib import Path
if not __debug__: raise RuntimeError('assertions required')
D=Path(__file__).resolve().parent
g=D.parent/'aq17-positive-signed-binding/candidate16.json'
assert hashlib.sha256(g.read_bytes()).hexdigest()=='a7d6f8a618a810b37eb7a9de6bd92ceb73bd6351971fdd39045bf95f8bf9edac'
c=json.loads(g.read_text());s=(D/'draft-src/AdaptiveAQ16Literal.lean').read_text()
def check(s):
 marker='def literal (p : Fin 4 → ℤ) : Expr (Fin 16) :=\n'
 assert s.count(marker)==1
 body=s.split(marker,1)[1].split('\nend DiophantineConsistency.AdaptiveAQ16Literal',1)[0]
 expected=[f'  let {name} : Expr (Fin 16) := .var {i}' for i,name in enumerate(c['witnesses'])]
 expected += [f'  let {name} : Expr (Fin 16) := .constant (p {i})' for i,name in enumerate(c['fixed_numerals'])]
 expected += [f'  let {name} := {a} {op} {b}' for name,op,a,b in c['source']]
 expected += [f"  {c['output']}"]
 assert len(c['witnesses'])==16 and len(c['source'])==96 and body.splitlines()==expected
check(s)
for old,new in [('.var 0','.var 1'),('.constant (p 0)','.constant (p 1)'),('let qm := J * beta','let qm := J + beta'),('  aq16Sum6\nend ','  aq16Sum5\nend ')]:
 t=s.replace(old,new,1);assert t!=s
 try:check(t)
 except AssertionError:pass
 else:raise AssertionError('mutation survived')
print('PASS_AQ16_LITERAL_BINDING 16 variables 4 ports 96 gates 4 mutations')
