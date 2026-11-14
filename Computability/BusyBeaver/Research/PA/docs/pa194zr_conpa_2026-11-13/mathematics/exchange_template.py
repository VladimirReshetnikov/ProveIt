#!/usr/bin/env python3
"""Independent finite K/S/MP certificate for the antecedent exchange schema.

K and S are derived uniformly from the retained restricted rho8 basis in
PA196/Logic/ImplicationBasis.lean. This checker verifies the finite pure
implication template; it does not replace that inherited basis theorem or
construct a full PA derivation of the eventual machine endpoint.
"""
import json
from pathlib import Path

def I(a,b):return ('I',a,b)
def K(a,b):return ('K',a,b)
def S(a,b,c):return ('S',a,b,c)
def H(a):return ('H',a)
def formula(d):
 k,*v=d
 if k=='K':a,b=v;return I(a,I(b,a))
 if k=='S':a,b,c=v;return I(I(a,I(b,c)),I(I(a,b),I(a,c)))
 if k=='H':return v[0]
 if k=='MP':
  minor,major=v;fm,fg=formula(minor),formula(major)
  assert isinstance(fg,tuple) and fg[0]=='I' and fg[1]==fm
  return fg[2]
 raise AssertionError(k)
def MP(minor,major):
 out=('MP',minor,major);formula(out);return out
def identity(a):return MP(K(a,a),MP(K(a,I(a,a)),S(a,I(a,a),a)))
def deduction(h,d):
 f=formula(d)
 if f==h:return identity(h)
 if d[0]!='MP':return MP(d,K(f,h))
 minor,major=d[1:];p=formula(minor)
 return MP(deduction(h,minor),MP(deduction(h,major),S(h,p,f)))
def check(d,allowed=frozenset()):
 k,*v=d
 if k=='H':assert v[0]in allowed
 if k=='MP':
  check(v[0],allowed);check(v[1],allowed)
 formula(d)
def nodes(d,out=None):
 if out is None:out=set()
 if d in out:return out
 out.add(d)
 if d[0]=='MP':nodes(d[1],out);nodes(d[2],out)
 return out
def numeric_formula(f,assignment):
 if isinstance(f,str):return assignment[f]
 _,a,b=f;a=numeric_formula(a,assignment);b=numeric_formula(b,assignment)
 return 2*(a+b)*(a+b+1)+4*b

def main():
 p,q,r='P','Q','R';f=I(p,I(q,r))
 d=MP(H(q),MP(H(p),H(f)))
 check(d,{p,q,f})
 for h in[p,q,f]:d=deduction(h,d)
 check(d)
 assert formula(d)==I(I(p,I(q,r)),I(q,I(p,r)))
 nd=nodes(d)
 # Numerical codes may alias at I(0,0)=0; MP still checks literally.
 runs=0
 for pv in range(3):
  for qv in range(3):
   for rv in range(3):
    subst={'P':pv,'Q':qv,'R':rv}
    for n in nd:
     if n[0]=='MP':
      minor,major=n[1:];a=numeric_formula(formula(minor),subst)
      c=numeric_formula(formula(n),subst)
      assert numeric_formula(formula(major),subst)==2*(a+c)*(a+c+1)+4*c
    runs+=1
 report={'status':'PASS','unique_proof_DAG_nodes':len(nd),
  'K_instances':sum(n[0]=='K'for n in nd),'S_instances':sum(n[0]=='S'for n in nd),
  'MP_nodes':sum(n[0]=='MP'for n in nd),'remaining_assumptions':0,
  'schema':'(P -> (Q -> R)) -> (Q -> (P -> R))',
  'numeric_alias_instantiations':runs,
  'scope':'Pure finite K/S/MP exchange certificate; K,S suppliers inherited from unchanged restricted rho8.'}
 print(json.dumps(report,indent=2))
 (Path(__file__).parent/'exchange_template_receipt.json').write_text(json.dumps(report,indent=2)+'\n')
if __name__=='__main__':
 if not __debug__:raise RuntimeError('Assertions must be enabled')
 main()
