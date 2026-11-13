#!/usr/bin/env python3
from pathlib import Path
from itertools import product
import hashlib,json
P=Path(__file__).resolve().parent;D=P.parents[1]
paths=[P/'FiveUnitModFour.lean',D/'research/ordinary14-five-unit-model-facts-draft/FiveUnitFacts.lean',D/'Lean/DiophantineConsistency/ArithmeticAdaptiveFactorUnits2011.lean']
s=paths[0].read_text()
for k in ('(hm : 2≤m)','(hq : pairResidue q=','(hr : pairResidue r=','(ht : pairResidue t=','main_bad u a c d','aux_bad a f v y','strong_bad a f i','five_positive_of_direct_first'):
 assert k in s,k
counts={'main':0,'aux':0,'strong':0}
for u,a,c,d in product(range(4),repeat=4):
 assert (1+d*d-u*u*(1+(a*a+4*a+3)*c*c))%4!=3;counts['main']+=1
for a,f,v,y in product(range(4),repeat=4):
 Q=(a*a+4*a+3)*(f*f-1)
 assert (Q*v*v+(1-Q)*y*y)%4!=3;counts['aux']+=1
for a,f,i in product(range(4),repeat=3):
 assert (1+i*i-(a*a+4*a+3)*(f*f-1))%4!=3;counts['strong']+=1
print(json.dumps({'scope':'exhaustive mod-four finite controls and source checks; no Lean or graph binding','files':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},'cases':counts},sort_keys=True,indent=2))
