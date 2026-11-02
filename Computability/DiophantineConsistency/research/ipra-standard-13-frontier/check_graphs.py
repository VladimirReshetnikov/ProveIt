#!/usr/bin/env python3
"""Check both 13-variable historical/generated Lean literals against pinned graphs."""
import hashlib,json
from pathlib import Path
if not __debug__:raise RuntimeError('assertions required')
D=Path(__file__).resolve().parent
ROOT=D.parents[1];SNAP=Path('/tmp/ipra-aq29-fresh-source-closure-v2')
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
m=json.loads((SNAP/'manifest.json').read_text());assert H(SNAP/'manifest.json')=='63b846158674d41beeaa99843d92008465f8e0fe5c45bb9e1fed4b78e1a2ab48'
cases=[('sum87',D.parent/'adaptive-square-sums/candidate.json',D/'draft-src/AdaptiveDirectOrdinateSquareSumsLiteral.lean',
        '11fb3c192fb3a8ab9204ef0a5401198d986e002242e4f48442147aa356263828','def literal','\n\n/-- The generated DAG',87),
       ('product86',D.parent/'adaptive-direct-ordinate86/candidate.json',SNAP/'src/DiophantineConsistency/AdaptiveDirectOrdinate86Literal.lean',
        'e9889a81a491b85491dde749e82158109ea98ff94ed41fc0f05dc810ec58b91f','def expressionAt86','\ndef contextAt',86)]
assert H(cases[0][2])=='9eb21e1febd710884d971be3431387144845d9eb8e6a0747d7224d1321c01a78'
assert H(cases[1][2])==m['sources']['DiophantineConsistency.AdaptiveDirectOrdinate86Literal']['sha256']
for label,graph,source,pin,start,end,count in cases:
 assert H(graph)==pin;c=json.loads(graph.read_text());assert len(c['witnesses'])==13 and len(c['source'])==count
 signature=start+' (p : Fin 4 → ℤ) : Expr (Fin 13) :=\n'
 def check(s):
  assert s.count(signature)==1
  body=s.split(signature,1)[1].split(end,1)[0].rstrip('\n').splitlines()
  want=[f'  let {n} : Expr (Fin 13) := .var {i}' for i,n in enumerate(c['witnesses'])]
  want += [f'  let {n} : Expr (Fin 13) := .constant (p {i})' for i,n in enumerate(c['fixed_numerals'])]
  want += [f'  let {n} := {a} {op} {b}' for n,op,a,b in c['source']]
  want += ['  '+c['output']]
  assert body==want,(label,len(body),len(want),next(((a,b) for a,b in zip(body,want) if a!=b),None))
 text=source.read_text();check(text);pre,body=text.split(signature,1)
 for old,new in [('.var 0','.var 1'),('.constant (p 0)','.constant (p 1)'),('let qm := J * beta','let qm := J + beta')]:
  trial=body.replace(old,new,1);assert trial!=body
  try:check(pre+signature+trial)
  except AssertionError:pass
  else:raise AssertionError((label,'mutation accepted'))
 print('PASS_GRAPH_LITERAL',label,count,'gates, 13 inputs, 4 ports, 3 mutations')
