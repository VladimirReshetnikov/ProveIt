from itertools import product
import json
from pathlib import Path

def test(n):
    D=n-1
    for tab in product(range(n),repeat=n*n):
        if any(tab[D*n+b]==D for b in range(n-1)): continue
        imp=lambda a,b:tab[a*n+b]
        if any(imp(imp(imp(p,q),q),imp(imp(q,p),imp(r,p)))!=D for p,q,r in product(range(n),repeat=3)):continue
        badK=[(p,q) for p,q in product(range(n),repeat=2) if imp(p,imp(q,p))!=D]
        badI=[p for p in range(n) if imp(p,p)!=D]
        badS=[(p,q,r) for p,q,r in product(range(n),repeat=3) if imp(imp(p,imp(q,r)),imp(imp(p,q),imp(p,r)))!=D]
        if badK or badI or badS:
            return dict(n=n,designated=D,table=tab,badK=badK,badI=badI,badS=badS)
    return None
r=[test(n) for n in [2,3]]
print(json.dumps(r,indent=2))
open(Path(__file__).with_suffix('.json'),'w').write(json.dumps(r,indent=2)+'\n')
