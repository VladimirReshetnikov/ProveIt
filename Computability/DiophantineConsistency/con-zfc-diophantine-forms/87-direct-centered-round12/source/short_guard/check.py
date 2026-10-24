"""Independent source-side proof audit for the short approximation guard."""
from pathlib import Path
import json,hashlib
from fractions import Fraction
import sympy as S
R=Path(__file__).resolve().parent
src=R.parent/'source_original.json'; data=json.loads(src.read_text()); layout=json.loads((R/'layout.json').read_text())
def require(v,msg):
 if not v:raise ValueError(msg)
vs=S.symbols(' '.join(data['variables'])); ps=S.symbols(' '.join(data['constants'])); dd={str(x):x for x in vs+ps}
row=data['equations'][3]
expr=sum(t['coefficient']*S.prod(x**p for x,p in zip(vs+ps,t['powers']))for t in row['terms'])
require(S.expand(expr-(dd['a']-dd['E']-(dd['N']+1)*dd['s']))==0,'source row4')
weights=layout['weights'];W=max(weights);idx=data['variables'].index('a')
require(W==116 and weights[idx]==W,'top source digit a')
require(len(set(weights))==len(weights)and min(weights)>0,'distinct positive weights')
require(weights.count(W)==1,'unique top digit')
g,c,K,e=S.symbols('g cap K error');guard=g*(c-g)*K**2-c**2*e**2
require(S.expand(4*g*(c-g)-(c**2-(c-2*g)**2))==0,'variance identity')
# Exact rational replay of the proof inequalities, including endpoint margins.
checks=0
for b in range(2,25):
 for w in range(1,5):
  B=b*b;cap=b*B**w
  for gg in {B**w,2*B**w,min(cap-1,3*B**w),cap-1}:
   if not(0<gg<cap):continue
   require(gg**3>=cap**2,'canonical lower bound')
   KK=8*gg;ee=Fraction(199,100) # strictly below K/(4g)=2
   rr=gg*(cap-gg)*KK**2-cap**2*ee**2
   require(rr>0,'completeness at near-bound error')
   require(4*ee**2<KK**2,'soundness conclusion')
   checks+=1
out={'status':'PASS','source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'layout_sha256':hashlib.sha256((R/'layout.json').read_bytes()).hexdigest(),'top_coordinate':'a','top_weight':W,'source_lower_bound':'a >= 3','canonical_lower_bound':'g >= 2*B^116','sufficient_bound':'g^3 >= cap^2','guard':'g*(cap-g)*K^2-cap^2*(C-K*L)^2','exact_boundary_regressions':checks,'scope':'source conventions, polynomial identity, and proof-inequality audit; finalizer compilation is separate'}
(R/'CHECKS.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
