#!/usr/bin/env python3
"""First-factor diagnostic only; not a full graph zero."""
import hashlib,json,math,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
p=Path(__file__).resolve().parent.parent/'ordinary12-absorb88-probe/graph-dag.json'
assert hashlib.sha256(p.read_bytes()).hexdigest()=='84a9a529636d6cadcf0f0c673c0728aa7b6fcbc0e2f2ac562a377553de831b25'
g=json.loads(p.read_text());v={i:i for i in range(5)}
v.update({name:1 for name in g['witnesses']+g['fixed_numerals']})
v.update(beta=3,MC=0,MF=0,K0=2,F=3,alpha=19,r=32237)
for name,op,x,y in g['source']:
    a,b=v[x],v[y]
    v[name]=a+b if op=='+' else a-b if op=='-' else a*b
b=v['qm'];q=v['q'];L=v['K0']+v['w'];G=v['G'];a=G%b;t=(G-a)//b
assert (b,q,L,G,v['Bt'],v['ell'],v['k'],v['Z'],v['A0'])==(3,4,3,22,-228,32768,2,98307,0)
assert math.gcd(b,L+1)==1 and v['Bt']%b==0 and (a,t)==(1,7) and t>b
assert v['A1']!=0 and v['N']!=0
for F in range(1,q):
    for alpha in range(1,q):
        if (F+alpha)*L+F<q*L:
            assert alpha+b*(q-F)!=G
print(json.dumps({'status':'PASS','b':b,'q':q,'L':L,'G':G,'remainder':a,'quotient':t,'Bt':v['Bt'],'A0':v['A0'],'A1':v['A1'],'N':v['N'],'scope':'first residual only; other residuals nonzero; not a graph zero'},sort_keys=True))
