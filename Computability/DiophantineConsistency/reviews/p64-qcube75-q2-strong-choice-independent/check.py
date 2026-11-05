#!/usr/bin/env python3
"""Independent Pell-pair and sign review of a specific q²-scale strong witness."""
import hashlib,json,math,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
here=Path(__file__).resolve().parent;research=here.parents[1]/'research'
author=research/'p64-qcube75-q2-strong-choice-obstruction'
parent=research/'p64-qcube75-q2-partial-obstruction'
pins={author/'check.py':'6ee6ea877ff2808a06da0aee1c9ff9a13ee7576b3872706a01fc390bb359977a',author/'result.json':'699b52c7a2661a1c668b77656ed35fbe7e2a6d35a36a9a1bf7d6e2eb134c57bd',parent/'check.py':'dd83f9710cba71d35a25f233181474beda4544774c8889928c48838ff7b0ac6c',parent/'result.json':'9e5bf77ccc96c4ba16c1779fe4c029d65544bbc58cd9fd0f01b912d0e970abb3'}
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
for p,h in pins.items():
    if sha(p)!=h:raise RuntimeError('input hash changed: '+str(p))
def norm_power(a,b,D,n,mod=None):
    if (a*a-D*b*b-1)%(mod or (1<<20))!=0:raise RuntimeError('not norm one')
    x,y=1,0
    for bit in bin(n)[2:]:
        x,y=2*x*x-1,2*x*y
        if mod:x,y=x%mod,y%mod
        if bit=='1':x,y=a*x+D*b*y,b*x+a*y
        if mod:x,y=x%mod,y%mod
        if max(x.bit_length(),y.bit_length())>10000:raise RuntimeError('operand limit')
    return x,y
p=223;n=12386;D=n*n-1
g,c=norm_power(n,1,D,322)
if c.bit_length()!=4686 or g*g-D*c*c!=1:raise RuntimeError('main norm mismatch')
f,L=norm_power(g%p,c%p,D%p,c,p);I=D*L%p
if (c%p,g%p,D%p,f,L,I)!=(19,68,145,0,42,69):raise RuntimeError('strong witness residues')
if (I*I-D*(f*f-1))%p:raise RuntimeError('strong residue')
# Iterate Pell pairs, not the author's second-order scalar recurrence.
x,y,j=1,0,0;seen=set();odd=set();h=(I*I-1)%p
while (x,y,j%2) not in seen:
    seen.add((x,y,j%2))
    if j%2:odd.add((x*pow(I,-1,p))%p)
    x,y=(I*x+h*y)%p,(x+I*y)%p;j+=1
    if len(seen)>2*p*p:raise RuntimeError('orbit bound')
if (x,y,j%2)!=(1,0,0) or len(seen)!=32:raise RuntimeError('pair cycle')
signed=odd|{(-a)%p for a in odd};expected={1,47,86,101,122,137,176,222}
if signed!=expected or (-c)%p in signed:raise RuntimeError('signed residue obstruction')
# Verify the proposed descent map on bounded genuine positive Pell solutions.
sanity=0
for b in range(2,16):
    for yy in range(1,3001):
        xx=math.isqrt((b*b-1)*yy*yy+1)
        if xx*xx-(b*b-1)*yy*yy!=1:continue
        xp=b*xx-(b*b-1)*yy; yp=b*yy-xx
        if xp<=0 or not (0<=yp<yy) or xp*xp-(b*b-1)*yp*yp!=1:
            raise RuntimeError('bounded descent sanity failed')
        sanity+=1
result={'status':'PASS_SPECIFIC_WITNESS_REVIEW','script_sha256':sha(Path(__file__)),
        'author_script_sha256':pins[author/'check.py'],'author_result_sha256':pins[author/'result.json'],
        'prime':p,'c_bits':c.bit_length(),'residues':{'c':c%p,'g':g%p,'D':D%p,'f':f,'L':L,'I':I},
        'pair_cycle':len(seen),'signed_V_residues':sorted(signed),'required_V_residue':(-c)%p,
        'bounded_descent_solutions_checked':sanity,
        'scope':'One specified symbolic strong Pell witness only; no arbitrary-witness or full-graph equivalence claim; no Lean.'}
out=here/'result.json'; payload=json.dumps(result,indent=2,sort_keys=True)+'\n'
if sys.argv[1:]==['--write']:
    with out.open('x') as o:o.write(payload)
elif sys.argv[1:]:raise SystemExit('usage: python3 -I -S -B check.py [--write]')
elif out.read_text()!=payload:raise SystemExit('result differs')
print(json.dumps(result,sort_keys=True))
