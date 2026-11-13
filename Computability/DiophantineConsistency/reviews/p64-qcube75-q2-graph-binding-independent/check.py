#!/usr/bin/env python3
"""Independent direct evaluation of the q²-modified graph at small tuples."""
import hashlib,json,operator,random,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('requires python -I -S without -O')
root=Path(__file__).resolve().parents[2]
graph=root/'research/p64-qcube76-independent-y-candidate/graph.json'
binding=root/'research/p64-qcube75-q2-graph-binding'
pins={graph:'196ef3bdf6805c7ed7d44c278359e32c0f658634db357cc19f0e87464ed6b11c'}
for path,h in pins.items():
    if hashlib.sha256(path.read_bytes()).hexdigest()!=h:raise RuntimeError('graph hash')
data=json.loads(graph.read_text());rows=data['source'];q3=[r for r in rows if r[0]=='q3'];uses=[r[0] for r in rows if 'q3' in r[2:]]
if q3!=[['q3','*','q2','q']] or uses!=['Y']:raise RuntimeError('q3 wiring')
rows=[(['Y','*','q2','s'] if r[0]=='Y' else r) for r in rows if r[0]!='q3']
if len(rows)!=75 or len({r[0] for r in rows})!=75:raise RuntimeError('wrong row count')
seen=set(data['witnesses']+data['fixed_numerals']); names=set();ops={'+':operator.add,'-':operator.sub,'*':operator.mul}
for n,o,x,y in rows:
    if n in seen or o not in ops or any(isinstance(v,str) and v not in seen for v in (x,y)):raise RuntimeError('invalid topological order')
    seen.add(n);names.add(n)
live={'polynomial'}
for n,o,x,y in reversed(rows):
    if n in live:live.update(v for v in (x,y) if isinstance(v,str))
if not names<=live:raise RuntimeError('dead gate')
rng=random.Random(573120)
for _ in range(100):
    d={n:rng.randrange(1,5) for n in data['witnesses']};d.update({n:rng.randrange(0,5) for n in data['fixed_numerals']})
    for n,o,x,y in rows:d[n]=ops[o](d[x] if isinstance(x,str) else x,d[y] if isinstance(y,str) else y)
    q=d['beta']*d['J']+1;Y=q*q*d['s'];U=Y*Y;X=d['w']*q;k=d['eta']+d['zeta'];ell=X*U*k;c=k*Y+d['eta'];a=(X+1)*Y;H=4*a+3;D=a*a+H
    R=((q-1)*(q-d['F'])+d['alpha'])*(q*q-1)+(d['MC']+q*d['MF'])*d['J']
    Ds=U*(X+a*c)+H*(U*d['gamma']-(k-R-1))
    V=d['f']**2*(c*d['T']-R)-c;I=d['i']*c*c
    A=d['t']**2-ell*(ell+k);M=Ds*Ds-U*U*(D*c*c+1);W=I*I-D*(d['f']**2-1)
    Lt=(d['K0']+d['w'])*(q-d['F']-d['alpha'])-d['F']-d['z']*(q-1)
    Na=D*(d['f']**2-1)*(V*V-d['y']**2)+d['y']**2
    want={'q':q,'Y':Y,'U':U,'X':X,'k':k,'ell':ell,'c':c,'a':a,'H':H,'Delta':D,'R':R,'Dstar':Ds,'V':V,'I':I,'A0':A,'M':M,'W':W,'Lt':Lt,'Na':Na,'polynomial':(A*Na-1)**2+M*M+W*W+Lt*Lt}
    if any(d[n]!=v for n,v in want.items()):raise RuntimeError('direct formula discrepancy')
print(json.dumps({'status':'PASS','cases':100,'live_operations':len(names),'graph_hash':pins[graph],'scope':'Independent finite direct gate/formula comparisons, not a universal proof or Lean check.'},sort_keys=True))
