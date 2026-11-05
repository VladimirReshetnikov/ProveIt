#!/usr/bin/env python3
"""Generate the 72-gate free-main graph and its Lean transcription."""
import hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B without optimization')
here=Path(__file__).resolve().parent
source=here.parent/'p64-qcube76-independent-y-candidate/graph.json'
raw=source.read_bytes(); parent='196ef3bdf6805c7ed7d44c278359e32c0f658634db357cc19f0e87464ed6b11c'
if hashlib.sha256(raw).hexdigest()!=parent:raise RuntimeError('source graph drift')
g=json.loads(raw); removed=['r_plus_one','r','U_gamma','main_gap']
expected=[['r_plus_one','-','k','R'],['r','-','r_plus_one',1],['U_gamma','*','U','gamma'],['main_gap','-','U_gamma','r']]
if [r for r in g['source'] if r[0] in removed]!=expected:raise RuntimeError('source gate mismatch')
rows=[['H_main_gap','*','H','h'] if r[0]=='H_main_gap' else r for r in g['source'] if r[0] not in removed]
if len(rows)!=72 or rows.count(['H_main_gap','*','H','h'])!=1:raise RuntimeError('wrong modification')
witnesses=g['witnesses'][:-1]+['h']; inputs=witnesses+g['fixed_numerals']; seen=set(inputs)
for n,op,a,b in rows:
    if n in seen or op not in ('+','-','*') or any(isinstance(x,str) and x not in seen for x in (a,b)):raise RuntimeError('bad gate '+n)
    seen.add(n)
live={'polynomial'}
for n,op,a,b in reversed(rows):
    if n in live:live.update(x for x in (a,b) if isinstance(x,str))
if not all(r[0] in live for r in rows):raise RuntimeError('dead gate')
out={'name':'p64_qcube_free_main_positive14','witness_domain':'strictly positive integers','witnesses':witnesses,'fixed_numerals':g['fixed_numerals'],'source':rows,'output':'polynomial','operations':72,'operation_counts':{o:sum(r[1]==o for r in rows) for o in ('*','+','-')},'parent_graph_sha256':parent,'status':'candidate; forward witness map pending Lean check, converse and endpoint open'}
lines=['import DiophantineConsistency.Compact44.P64Graph','','/-! Generated 72-gate free-main graph. No converse is asserted. -/','set_option autoImplicit false','set_option Elab.async false','noncomputable section','namespace P64QCube72Free','open LO LO.FirstOrder LO.FirstOrder.Arithmetic','open scoped LO.FirstOrder.Arithmetic','open DiophantineConsistency AdaptiveEquationSyntax2011','','def graph (p : Fin 4 → ℤ) : P64Graph.Graph :=']
for i,n in enumerate(witnesses):lines.append(f'  let {n} : Expr (Fin 14) := .var {i}')
for i,n in enumerate(g['fixed_numerals']):lines.append(f'  let {n} : Expr (Fin 14) := .constant (p {i})')
lines.append('  -- BEGIN GENERATED GRAPH')
for n,op,a,b in rows:lines.append(f'  let {n} := {a} {op} {b}')
lines.extend(['  -- END GENERATED GRAPH','  ⟨A0, M, W, Na, Lt, polynomial⟩','','end P64QCube72Free',''])
outputs={'graph.json':json.dumps(out,indent=2)+'\n','P64QCube72Free.lean':'\n'.join(lines)}
for name,content in outputs.items():
    p=here/name
    if sys.argv[1:]==['--write']:
        with p.open('x') as f:f.write(content)
    elif sys.argv[1:]:raise SystemExit('usage: build.py [--write]')
    elif p.read_text()!=content:raise RuntimeError('output drift '+name)
print(json.dumps({'status':'PASS','operations':72,'counts':out['operation_counts'],'parent_sha256':parent,'outputs':{n:hashlib.sha256(v.encode()).hexdigest() for n,v in outputs.items()},'scope':'Graph generation only, no Lean theorem or equivalence.'},sort_keys=True))
