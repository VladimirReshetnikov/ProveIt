#!/usr/bin/env python3
"""External, pinned comparison of Lean graph source and candidate JSON."""
from pathlib import Path
from hashlib import sha256
import json, re
H=Path(__file__).resolve().parent
D=H.parents[1]
source=D/'research/ordinary12-ipra-bridge/free-j-prototype/Ordinary12FreeJ.lean'
bridge=H/'FreeJSumSquares.lean'
obj=H/'candidate.json'
def sha(p):return sha256(p.read_bytes()).hexdigest()
def need(c,m):
    if not c:raise RuntimeError(m)
need(sha(source)=='542bb6913f5b7e6d1ef3cd9e430fcbee20ee727966d3bfc9f2b6d71c566ef96a','source pin')
need(sha(bridge)=='77f22764b45732e2f7b837bf98caf40e6563c232f48ba682c421889b396b7794','bridge pin')
need(sha(obj)=='dc13e87a45a687e99e9bcb1cd3276e7c80d3e014bb7f51074084ca3214ac45ee','candidate pin')
s=source.read_text();need(s.count('-- BEGIN LITERAL GRAPH')==s.count('-- END LITERAL GRAPH')==1,'graph markers')
section=s.split('-- BEGIN LITERAL GRAPH',1)[1].split('-- END LITERAL GRAPH',1)[0]
rows=[]
def token(x):return int(x) if x.isdecimal() else x
for line in section.splitlines():
    if not line.strip():continue
    m=re.fullmatch(r'\s*let (\w+) := (\w+) ([+*\-]) (\w+)\s*',line)
    need(m is not None,'unparsed Lean graph row: '+line)
    name,a,op,b=m.groups();rows.append([name,op,token(a),token(b)])
g=json.loads(obj.read_text()); need(len(rows)==95 and rows[:89]==g['source'][:89], 'Lean and JSON prefix differ')
need(rows[-6:]==[['g94','+',1,'A0'],['g95','+',1,'A1'],['g96','*','g94','g95'],['g97','+',1,'N'],['g98','*','g96','g97'],['P12','-','g98',1]],'factor tail')
need('⟨g94,g95,g97,P12,qm,Z,g41,U,a,c,Dstar,polarA,den,polarT,polarCy⟩' in s,'core factor projection')
for i,n in enumerate(g['witnesses']):
    need(f'let {n} : Expr (Fin 12) := .var {i}' in s,'witness mismatch '+n)
for i,n in enumerate(g['fixed_numerals']):
    need(f'let {n} : Expr (Fin 12) := .constant (p {i})' in s,'port mismatch '+n)
b=bridge.read_text()
need('| .add _ b => b' in b and all(x in b for x in [
 'rightAdd (core p).first','rightAdd (core p).main','rightAdd (core p).ordinary',
 'let a := firstResidual p','let b := mainResidual p','let c := ordinaryResidual p',
 'a*a + b*b + c*c']), 'residual projection shape')
need(g['source'][89:]==[['A0sq','*','A0','A0'],['A1sq','*','A1','A1'],['Nsq','*','N','N'],['sum01','+','A0sq','A1sq'],['P12','+','sum01','Nsq']],'new tail mismatch')
print(json.dumps({'status':'PASS_EXTERNAL_SOURCE_COMPARISON', 'prefix_rows':89,
                  'witnesses':len(g['witnesses']),'fixed_ports':len(g['fixed_numerals']),
                  'old_tail_rows':6,'new_tail_rows':5,'lean_source_sha256':sha(source),
                  'bridge_source_sha256':sha(bridge),'candidate_sha256':sha(obj),
                  'scope':'text/JSON comparison only; no Lean theorem relating filesystem files'},indent=2,sort_keys=True))
