#!/usr/bin/env python3
"""Independent structural and finite forward-map tests for freeing f²."""
import hashlib,json,operator,random,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('requires -I -S without -O')
root=Path(__file__).resolve().parents[2];p=root/'research/p64-qcube76-independent-y-candidate/graph.json';raw=p.read_bytes()
if hashlib.sha256(raw).hexdigest()!='196ef3bdf6805c7ed7d44c278359e32c0f658634db357cc19f0e87464ed6b11c':raise RuntimeError('graph drift')
g=json.loads(raw);rows=g['source'];
if [r for r in rows if r[0]=='f2']!=[['f2','*','f','f']] or [r[0] for r in rows if 'f' in r[2:]]!=['f2']:raise RuntimeError('unexpected f wiring')
if [r[0] for r in rows if 'f2' in r[2:]]!=['f2_minus_one','f2_quotient']:raise RuntimeError('unexpected f2 wiring')
new=[[n,op,('F2' if a=='f2' else a),('F2' if b=='f2' else b)] for n,op,a,b in rows if n!='f2']
if len(new)!=75:raise RuntimeError('unexpected operation count')
known=set(g['witnesses']+g['fixed_numerals']);known.remove('f');known.add('F2');seen=set(known)
for n,op,a,b in new:
    if n in seen or any(isinstance(x,str) and x not in seen for x in (a,b)):raise RuntimeError('bad graph')
    seen.add(n)
live={'polynomial'}
for n,op,a,b in reversed(new):
    if n in live:live.update(x for x in (a,b) if isinstance(x,str))
if not all(n in live for n,_,_,_ in new):raise RuntimeError('dead gate')
ops={'+':operator.add,'-':operator.sub,'*':operator.mul}
def evaluate(rows,values):
    d=values.copy()
    for n,op,a,b in rows:d[n]=ops[op](d[a] if isinstance(a,str) else a,d[b] if isinstance(b,str) else b)
    return d
rng=random.Random(247531)
for _ in range(200):
    v={n:rng.randrange(1,5) for n in g['witnesses']};v.update({n:rng.randrange(0,5) for n in g['fixed_numerals']})
    w=v.copy();w['F2']=v['f']**2;del w['f']
    a=evaluate(rows,v);b=evaluate(new,w)
    if any(a[n]!=b[n] for n in ('A0','M','W','Na','Lt','polynomial')):raise RuntimeError('forward map mismatch')
q=3;Y=27;U=Y*Y;X=2*q;a=(X+1)*Y;H=4*a+3;D=a*a+H;R=((q-1)*(q-1)+1)*(q*q-1)+4020579;Lt=(1+2)*(q-1-1)-1-1*(q-1)
if (q,Y,U,X,a,H,D,R,Lt)!=(3,27,729,6,189,759,36480,4020619,0):raise RuntimeError('witness core mismatch')
print(json.dumps({'status':'PASS','live_modified_rows':75,'forward_map_finite_cases':200,'source_graph_sha256':hashlib.sha256(raw).hexdigest(),'scope':'Structural and finite forward-map checks; universal proof is mathematical, no Lean.'},sort_keys=True))
