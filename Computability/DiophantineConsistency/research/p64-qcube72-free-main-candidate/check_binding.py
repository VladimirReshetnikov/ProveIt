#!/usr/bin/env python3
"""Finite structural and evaluator checks for the 76Y-to-72 carrier map."""
import hashlib,json,operator,random,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B without optimization')
here=Path(__file__).resolve().parent;source=here.parent/'p64-qcube76-independent-y-candidate/graph.json';target=here/'graph.json'
a=source.read_bytes();b=target.read_bytes()
if hashlib.sha256(a).hexdigest()!='196ef3bdf6805c7ed7d44c278359e32c0f658634db357cc19f0e87464ed6b11c' or hashlib.sha256(b).hexdigest()!='875a9d0972c350e6858e25b68f2dc794b1f330e61f29cd52a5853ece90b24806':raise RuntimeError('graph pin mismatch')
old=json.loads(a);new=json.loads(b);remove={'r_plus_one','r','U_gamma','main_gap'}
reconstructed=[['H_main_gap','*','H','h'] if r[0]=='H_main_gap' else r for r in old['source'] if r[0] not in remove]
if new['source']!=reconstructed:raise RuntimeError('rewrite mismatch')
if [r[0] for r in old['source'] if 'gamma' in r[2:]]!=['U_gamma'] or [r[0] for r in new['source'] if 'h' in r[2:]]!=['H_main_gap']:raise RuntimeError('coordinate use mismatch')
ops={'+':operator.add,'-':operator.sub,'*':operator.mul}
def evaluate(rows,vals):
    d=vals.copy()
    for n,op,x,y in rows:d[n]=ops[op](d[x] if isinstance(x,str) else x,d[y] if isinstance(y,str) else y)
    return d
r=random.Random(640072)
for _ in range(120):
    v={n:r.randrange(1,5) for n in old['witnesses']};v.update({n:r.randrange(0,5) for n in old['fixed_numerals']})
    o=evaluate(old['source'],v);w=v.copy();w['h']=o['U']*v['gamma']-(o['k']-o['R']-1);del w['gamma'];n=evaluate(new['source'],w)
    if any(n[x]!=o[x] for x in ('A0','M','W','Na','Lt','polynomial')):raise RuntimeError('residual mismatch')
    if n['h']!=o['main_gap']:raise RuntimeError('gap mismatch')
print(json.dumps({'status':'PASS','cases':120,'source_sha256':hashlib.sha256(a).hexdigest(),'target_sha256':hashlib.sha256(b).hexdigest(),'scope':'Structural and finite evaluator check only; arbitrary ring and model-forward Lean statements require separate checks.'},sort_keys=True))
