#!/usr/bin/env python3
"""Independent structural and finite transport tests for freeing X."""
import hashlib,json,operator,random,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('requires python3 -I -S without -O')
root=Path(__file__).resolve().parents[2];p=root/'research/p64-qcube76-independent-y-candidate/graph.json';raw=p.read_bytes()
if hashlib.sha256(raw).hexdigest()!='196ef3bdf6805c7ed7d44c278359e32c0f658634db357cc19f0e87464ed6b11c':raise RuntimeError('graph drift')
g=json.loads(raw);rows=g['source'];xrows=[r for r in rows if r[0]=='X'];uses=[r[0] for r in rows if 'X' in r[2:]]
if xrows!=[['X','*','w','q']] or uses!=['E','b0']:raise RuntimeError('unexpected X wiring')
new=[[n,op,('w' if a=='X' else a),('w' if b=='X' else b)] for n,op,a,b in rows if n!='X']
if len(new)!=75:raise RuntimeError('unexpected operation count')
known=set(g['witnesses']+g['fixed_numerals']);seen=set(known)
for n,op,a,b in new:
    if n in seen or any(isinstance(x,str) and x not in seen for x in (a,b)):raise RuntimeError('bad graph')
    seen.add(n)
live={'polynomial'}
for n,op,a,b in reversed(new):
    if n in live:live.update(x for x in (a,b) if isinstance(x,str))
if not all(n in live for n,_,_,_ in new):raise RuntimeError('dead gate')
ops={'+':operator.add,'-':operator.sub,'*':operator.mul}
def evalrows(rows,values):
    d=values.copy()
    for n,op,a,b in rows:d[n]=ops[op](d[a] if isinstance(a,str) else a,d[b] if isinstance(b,str) else b)
    return d
rng=random.Random(92727)
for i in range(200):
    v={n:rng.randrange(1,5) for n in g['witnesses']};v.update({n:rng.randrange(0,5) for n in g['fixed_numerals']})
    v.update(beta=3,F=1,alpha=1)
    q=v['beta']*v['J']+1;C=q-v['F']-v['alpha']
    w=v.copy();w['w']=q*v['w'];w['z']=v['z']+v['w']*C
    if min(w[n] for n in g['witnesses'])<=0:raise RuntimeError('map positivity')
    a=evalrows(rows,v);b=evalrows(new,w)
    if any(a[n]!=b[n] for n in ('A0','M','W','Na','Lt','polynomial')):raise RuntimeError('transport map mismatch')
# Explicit small factors and transport for the symbolic witness.
v={'beta':2,'K0':1,'MC':226403,'MF':0,'J':1,'F':1,'alpha':1,'z':4,'s':1,'w':8}
q=v['beta']*v['J']+1;Y=q**3*v['s'];U=Y*Y;X=v['w'];a=(X+1)*Y;H=4*a+3
R=((q-1)*(q-v['F'])+v['alpha'])*(q*q-1)+(v['MC']+q*v['MF'])*v['J']
Lt=(v['K0']+v['w'])*(q-v['F']-v['alpha'])-v['F']-v['z']*(q-1)
if (q,Y,U,X,a,H,R,Lt)!=(3,27,729,8,243,975,226443,0):raise RuntimeError('witness core mismatch')
print(json.dumps({'status':'PASS','modified_live_rows':75,'forward_map_finite_cases':200,'specified_small_core':[q,Y,U,X,a,H,R,Lt],'source_graph_sha256':hashlib.sha256(raw).hexdigest(),'scope':'Independent structural and finite checks, not a universal proof or Lean theorem.'},sort_keys=True))
