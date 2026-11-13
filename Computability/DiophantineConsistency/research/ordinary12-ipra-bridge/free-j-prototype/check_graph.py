#!/usr/bin/env python3
"""Bind every displayed free-J Lean row and port to the pinned 95-gate graph."""
import hashlib,json
from pathlib import Path
if not __debug__: raise RuntimeError('checks require Python assertions enabled')
here=Path(__file__).resolve().parent
root=here.parents[2]
graph=root/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/circuits/positive12_95_degree70.json'
if hashlib.sha256(graph.read_bytes()).hexdigest()!='2348183cb8e366433f668cdcc9d77ca9c7e2d0c55b7b630bda39bd8db7506d22': raise ValueError('graph drift')
j=json.loads(graph.read_text())
assert len(j['source'])==95 and j['operations']==95
assert j['witnesses']==['J','F','alpha','t','T','X','Y','r','eta','zeta','n','gamma']
assert j['fixed_numerals']==['beta','K0','MC','MF'] and j['output']=='P12'
def check(s):
 for i,w in enumerate(j['witnesses']): assert s.count(f'  let {w} : Expr (Fin 12) := .var {i}\n')==1
 for i,w in enumerate(j['fixed_numerals']): assert s.count(f'  let {w} : Expr (Fin 12) := .constant (p {i})\n')==1
 graph_text='\n'.join(f'  let {name} := {a} {op} {b}' for name,op,a,b in j['source'])
 assert s.split('  -- BEGIN LITERAL GRAPH\n',1)[1].split('\n  -- END LITERAL GRAPH',1)[0]==graph_text
 assert s.count('  ⟨g94,g95,g97,P12,qm,Z,g41,U,a,c,Dstar,polarA,den,polarT,polarCy⟩')==1
s=(here/'Ordinary12FreeJ.lean').read_text(); check(s)
for bad in (s.replace('let qm := J * beta','let qm := J + beta',1),
            s.replace('let J : Expr (Fin 12) := .var 0','let J : Expr (Fin 12) := .var 1',1),
            s.replace('let K0 : Expr (Fin 12) := .constant (p 1)','let K0 : Expr (Fin 12) := .constant (p 0)',1),
            s.replace('⟨g94,g95,g97,P12','⟨g94,g95,N,P12',1)):
 try: check(bad)
 except AssertionError: pass
 else: raise AssertionError('mutation accepted')
print('PASS_FREE_J_GRAPH 95 rows 12 free variables 4 ports 4 mutations rejected')
