#!/usr/bin/env python3
"""Independent exact symbolic checks of the auxiliary-gap root elimination."""
from pathlib import Path
import json
from sparse_poly import Poly

Q,d,b,v,e,f,P4,V0=(Poly.var(n) for n in ('Q','d','b','v','e','f','P4','V0'))
S=Q-1
r=b+S*e
p=d*v*v
A=p+r*r-Q*S*e*e-1
B=2*v*r
V=v*f-b
N=Q*(V*V-(V+e)**2)+(V+e)**2
assert A==p+b*b+S*e*(2*b-e)-1
assert d*B*B==4*p*r*r
assert A-B*f-(N-1)==v*v*(d-f*f)
assert P4*(A+1)-1-P4*B*f-(P4*N-1)==P4*v*v*(d-f*f)
assert (A+1).substitute({'v':Poly(0)})==Q*b*b-S*(e-b)**2
assert Q*(V0*V0-(V0+e)**2)+(V0+e)**2==V0*V0-S*e*(2*V0+e)

result={
 'status':'PASS',
 'arithmetic':'exact multivariate integer polynomial dictionaries',
 'random_sampling_used':False,
 'checks':[
  'exact cancellation in the root coefficient A',
  'norm cross term d*B^2 = 4*p*r^2',
  'root remainder, including explicit factor d-f^2',
  'outer root remainder, including explicit factor d-f^2',
  'T=0 reduction to Q*b^2-(Q-1)*(e-b)^2',
  'gap15 auxiliary polynomial identity',
 ],
 'proof_review':{
  'r_nonzero':'0<b<Q-1 implies b+(Q-1)*e is nonzero for every integer e',
  'T_nonzero':'T=0 gives the excluded auxiliary norm with 2<b<Q',
  'rational_root':'nonzero B and A^2=dB^2 imply A/B is an integer',
  'degree219':'A has leading term 2Qbe, degree85; K degree170; P4 degree49',
  'weighted_degree434':'weights A169, K338, P4 96',
 },
 'scope':'identity checks and independent ordinary proof review; not a formal verification of inherited Pell/compiler theorems',
}
dest=Path(__file__).resolve().parent/'gap_independent_review.json'
dest.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
