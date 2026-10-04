#!/usr/bin/env python3
"""Data-only rational-lattice extension of the inherited group target floor."""
import argparse
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path

PINS={
 'matrix193_integral_target_floor.py':'47e726064a68e520835370827618a80ae4c460c52826e52846901b18a15040bd',
 'matrix193_integral_target_floor.json':'3d2bab17b0058311ea43162e4d6f6bae3a29d65b6f5034c2934d1167cd407a84',
 'matrix193_integral_target_floor.md':'ffbc7ec62eadaa323448b567722d1b8c0def4c5bd470eece020b53ed9bd42f30',
 'matrix193_gamma1_recode.json':'9cdd0274625c847aa77f5907ba6554ee16f37895f5c026b3d776595330676668',
 'matrix193_gamma1_recode.md':'6349644283548af96f4a9582ee32d959a123c81bf1c2f902c45874ae45c96742'}
I=(1,0,0,1);T=(1,1,0,1);U=(1,0,5,1);V=(-9,5,-20,11)
D=(0,3,65,0);A5=(1,0,0,5);D5=(0,15,13,0);J=(0,1,1,0);E=(1,0,0,-1)

def need(x,label):
 if not x:raise ValueError(label)
def sha(x):return hashlib.sha256(x).hexdigest()
def pairs(xs):
 d={}
 for k,v in xs:
  need(k not in d,'duplicate JSON key');d[k]=v
 return d
def loads(b):return json.loads(b,object_pairs_hook=pairs,parse_constant=lambda x:(_ for _ in ()).throw(ValueError(x)))
def exact(a,b):
 if type(a) is not type(b):return False
 if isinstance(a,dict):return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if isinstance(a,list):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b
def mul(a,b):return (a[0]*b[0]+a[1]*b[2],a[0]*b[1]+a[1]*b[3],a[2]*b[0]+a[3]*b[2],a[2]*b[1]+a[3]*b[3])
def inv(a):
 d=a[0]*a[3]-a[1]*a[2];need(d!=0,'nonsingular')
 return tuple(F(x,d) for x in (a[3],-a[1],-a[2],a[0]))
def conj(a,s):return mul(mul(inv(s),a),s)
def integral(a):return all(F(x).denominator==1 for x in a)
def ints(a):
 need(integral(a),'integer serialization');return [int(x) for x in a]
def power(a,n):
 if n<0:return power(inv(a),-n)
 b=I
 for _ in range(n):b=mul(b,a)
 return b

def verify(root):
 raw={}
 for name,pin in PINS.items():
  b=(root/name).read_bytes();need(sha(b)==pin,'pin '+name);raw[name]=b
 old=loads(raw['matrix193_integral_target_floor.json'])
 parent=loads(raw['matrix193_gamma1_recode.json'])
 need(old['status']=='PASS' and old['source_sha256']==PINS['matrix193_integral_target_floor.py'],'inherited receipt')
 code={k:tuple(v) for k,v in parent['packet']['letters'].items()}
 # Normal group is V H' V^-1; all actual twenty generators preserve both lattices.
 normal={k:conj(v,inv(V)) for k,v in code.items()}
 need(mul(normal['0'],normal['1'])==T and inv(normal['1'])==U,'actual T and U')
 W=mul(power(T,3),power(U,-2));W1=conj(W,U)
 need(W1==(-14,3,65,-14) and conj(D,A5)==D5,'two rational frames')
 full_integrality=0
 for basis in (I,A5):
  for g in normal.values():
   z=conj(g,basis);need(integral(z),'all actual generators integral');full_integrality+=1
 T5=conj(T,A5);U5=conj(U,A5)
 need(T5==(1,5,0,1) and U5==(1,0,1,1),'second-frame parabolics')
 # Bounded independent triangular-matrix checks corroborate, but do not replace,
 # the unrestricted lattice proof. Include nonintegral q and n explicitly.
 qs=sorted({F(p,d) for d in range(1,13) for p in range(d)})
 ns=sorted({F(p,d) for d in range(1,13) for p in range(1,25)})
 lattice_count=0;survivors=[]
 for q in qs:
  for n in ns:
   s=(1,q,0,n);tc=conj(T,s);uc=conj(U,s)
   need(tc==(1,n,0,1),'symbolic T coordinates')
   j=5*q/n
   need(uc==(1-j,-j*q,5/n,1+j),'symbolic U coordinates')
   direct=integral(tc) and integral(uc)
   criterion=all(F(x).denominator==1 for x in (n,5/n,j,j*q))
   need(direct==criterion,'exact lattice criterion')
   if direct:
    need(q==0 and n in (1,5),'only two bounded normalized lattices')
    survivors.append({'q':[q.numerator,q.denominator],'n':[n.numerator,n.denominator]})
   lattice_count+=1
 need(len(survivors)==2,'both invariant lattices sampled')
 divisors=[d for d in range(1,196) if 195%d==0]
 moduli={(1,-1):3,(1,1):5,(3,-1):9,(3,1):4,(5,-1):4,(5,1):3,
         (13,-1):3,(15,1):4,(39,-1):5,(39,1):4,(65,-1):4,(65,1):3,
         (195,-1):25,(195,1):4}
 certs=[]
 for (c,sign),mod in sorted(moduli.items()):
  image=sorted({(13*p*p-15*r*r)%mod for p in range(mod) for r in range(mod)})
  need(sign*c%mod not in image,'unrestricted modular exclusion')
  certs.append(dict(c=c,sign=sign,modulus=mod,image=image,excluded=sign*c%mod))
 need({(c,e) for c in divisors for e in (-1,1)}-set(moduli)=={(13,1),(15,-1)},'complete survivor list')
 # The norm-one classification is proved in the note. Check its families and
 # lower stabilizers without claiming the finite examples prove completeness.
 fundamental=(14,15,13,14);W5=conj(W1,A5)
 need(fundamental==tuple(-x for x in inv(W5)),'fundamental in signed inherited group')
 units=[];collisions=0
 for exponent in range(-8,9):
  C=power(fundamental,exponent);z=C[0];h=F(C[1],15)
  need(C==(z,15*h,13*h,z) and z*z-195*h*h==1,'Pell centralizer')
  for swap in (False,True):
   for flip in (False,True):
    K=J if swap else I
    if flip:K=mul(K,E)
    S=mul(C,K);newD=conj(D5,S)
    need(newD[0]==newD[3]==0,'all survivor frame examples')
    parabolic=T5 if swap else U5
    group_word=mul(mul(C,parabolic),inv(C));collision=conj(group_word,S)
    need(collision[:2]==(1,0) and collision!=I and integral(collision),'whole-group lower collision')
    collisions+=1
  units.append(dict(exponent=exponent,z=int(z),h=int(h)))
 # Lower shear identity for all divisor/sign choices of the two-gate case.
 shears=[]
 for v in divisors:
  for sign in (-1,1):
   u=sign*v;w=195//v-v;M=(u,v,w,-u);L=(1,0,-sign,1)
   need(conj(M,L)==(0,v,195//v,0),'two-gate lower shear')
   shears.append(dict(u=u,v=v,w=w))
 return dict(status='PASS',source_sha256=sha(Path(__file__).read_bytes()),pins=PINS,
  actual_upper_integrality_checks=full_integrality,lattice_examples=lattice_count,lattice_survivors=survivors,
  second_frame=dict(D=ints(D5),T=ints(T5),U=ints(U5),fundamental_unit=list(fundamental)),
  modular_exclusions=certs,surviving_determinants=[-15,13],unit_examples=units,lower_collision_examples=collisions,
  lower_shear_examples=shears,
  scope='Rational basis changes keeping the inherited whole group integral; all-value generic first-row targets with only independent chi and psi. Three-gate floor, not a semigroup-only or universal Diophantine lower bound.',
  predecessor_code_executed=False,new_universal_Diophantine_bound=False)

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',type=Path,required=True)
 g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path)
 ns=ap.parse_args();out=verify(ns.root)
 if ns.expect:need(exact(out,loads(ns.expect.read_bytes())),'type-exact receipt')
 else:ns.output.write_text(json.dumps(out,sort_keys=True,indent=2,allow_nan=False)+'\n')
 print('PASS: two rational invariant lattices, second-frame classification, scoped three-gate floor')
if __name__=='__main__':main()
