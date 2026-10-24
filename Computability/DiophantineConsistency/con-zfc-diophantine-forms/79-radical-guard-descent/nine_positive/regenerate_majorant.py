#!/usr/bin/env python3
"""Reconstruct the654 coefficients by rational square-root recursion.
Only finite coefficient arithmetic is used; no numerical radicals or search.
SymPy is used only for the independently verifiable expanded identities.
"""
from pathlib import Path
import json,math
from sympy.polys.rings import ring
from sympy import QQ
R=Path(__file__).resolve().parent

def main():
 r,A,C,i,Z=ring('A,C,i,Z',QQ)
 J=4*A-5;D=(A*A-1)*C*C+1;e=i*J*C;E=e*D*C
 F=(A*A-1)*E*E+1;G=A+F*(C*D+1-A);H=C+F*Z
 Q=D*F*((G*G-1)*H*H+1)
 qd={}
 for (a,c,ii,z),co in Q.items():qd.setdefault(a,{})[(c,ii,z)]=co
 def add(x,y):
  out=x.copy()
  for p,v in y.items():out[p]=out.get(p,0)+v
  return {p:v for p,v in out.items()if v}
 def mul(x,y):
  out={}
  for p,v in x.items():
   for q,w in y.items():
    u=tuple(a+b for a,b in zip(p,q));out[u]=out.get(u,0)+v*w
  return {p:v for p,v in out.items()if v}
 coeffs={23:{(24,5,1):QQ(1024)}}
 for k in range(1,24):
  rhs=qd.get(46-k,{}).copy()
  for ell in range(1,k):rhs=add(rhs,{p:-v for p,v in mul(coeffs[23-ell],coeffs[23-k+ell]).items()})
  coeffs[23-k]={tuple(e-f for e,f in zip(p,(24,5,1))):v/2048 for p,v in rhs.items()}
 terms={(a,c+7,ii,z):co*65536 for a,part in coeffs.items()for (c,ii,z),co in part.items()}
 if len(terms)!=654 or any(min(e)<0 or co.denominator!=1 for e,co in terms.items()):raise ValueError('ordinary integer polynomial check')
 P=r.from_dict(terms);Defect=P*P-(65536*C**7)**2*Q
 shiftedP=P.compose(A,A+3).compose(C,C+1)
 shiftedR=Defect.compose(A,A+3).compose(C,C+1).compose(i,i+1).compose(Z,Z+1)
 if len(shiftedP)!=1816 or len(shiftedR)!=32637 or any(v<=0 for v in shiftedP.values()) or any(v<=0 for v in shiftedR.values()):raise ValueError('positive certificate failed')
 literal=json.loads((R/'data/radical.json').read_text())
 if r.from_dict({tuple(e):QQ(v)for e,v in literal['T_terms']})!=P:raise ValueError('P table mismatch')
 if r.from_dict({tuple(e):QQ(v)for e,v in literal['defect_terms']})!=Defect:raise ValueError('defect table mismatch')
 for name,poly in [('P_shifted',shiftedP),('defect_shifted',shiftedR)]:
  (R/'certificates'/f'{name}.json').write_text(json.dumps({'variables':['Aminus3','Cminus1','i' if name=='P_shifted' else 'iminus1','Z' if name=='P_shifted' else 'Zminus1'],'terms':[[list(e),int(v)]for e,v in sorted(poly.items())]},separators=(',',':'))+'\n')
 receipt={'status':'PASS','P_terms':len(P),'radicand_terms':len(Q),'defect_terms':len(Defect),'P_degrees':P.degrees(),'defect_degrees':Defect.degrees(),'positive_P_certificate_terms':len(shiftedP),'positive_defect_certificate_terms':len(shiftedR),'positive_defect_constant':int(shiftedR.get((0,0,0,0),0))}
 (R/'certificates/majorant_regeneration.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
if __name__=='__main__':main()
