#!/usr/bin/env python3
"""Finite residue certificate against one symbolic strong Pell witness."""
import hashlib,json,math,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('Use python3 -I -S -B without optimization')
def require(x,s):
    if not x:raise RuntimeError(s)
def mul(x,y,d,m=None):
    a,b=x;c,e=y
    out=(a*c+d*b*e,a*e+b*c)
    return tuple(z%m for z in out) if m else out
def power(x,e,d,m=None):
    out=(1,0)
    while e:
        if e&1:out=mul(out,x,d,m)
        e//=2
        if e:x=mul(x,x,d,m)
    return out
p=223; n=12386; D=n*n-1
require(p>2 and all(p%d for d in range(2,math.isqrt(p)+1)), 'p not prime')
g,c=power((n,1),322,D)
require(c>1 and c.bit_length()==4686 and g*g-D*c*c==1,'main tuple')
# c is only 4686 bits as an exponent, so modular binary powering is small.
f,L=power((g%p,c%p),c,D%p,p)
I=D*L%p
require((c%p,g%p,D%p,f,L,I)==(19,68,145,0,42,69),'residues')
require(I!=0 and (I*I-(D*(f*f-1)))%p==0,'strong norm mod p')
a0,a1=1,I;j=1;seen=set();Vres=set();inv=pow(I,-1,p)
while (a0,a1,j%2) not in seen:
    seen.add((a0,a1,j%2))
    if j%2:Vres.add(a1*inv%p)
    a0,a1=a1,(2*I*a1-a0)%p
    j+=1
    require(len(seen)<=2*p*p,'unexpected cycle length')
require((a0,a1,j%2)==(1,I,1),'did not return to initial state')
require(len(seen)==32,'unexpected cycle length')
expected={1,47,86,101,122,137,176,222}
require(Vres==expected and {(-v)%p for v in Vres}==Vres,'residue set')
required=(-c)%p
require(required not in Vres,'unexpected matching residue')
result={'status':'PASS_OBSTRUCTION_TO_CHOSEN_STRONG_WITNESS','script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'prime':p,'main_exponent':322,'c_bits':c.bit_length(),
        'residues':{'c':c%p,'g':g%p,'Delta':D%p,'f':f,'L':L,'I':I},
        'pell_recurrence_cycle_length':len(seen),'possible_V_residues':sorted(Vres),'required_V_residue':required,
        'scope':'This single symbolic strong-norm witness cannot meet the auxiliary unit for any T,y. No claim about other strong witnesses or full-graph existence.'}
print(json.dumps(result,indent=2,sort_keys=True))
