#!/usr/bin/env python3
"""Check proved (not necessarily least) periods modulo prime powers."""
import json
from pathlib import Path
import sympy as s
P=Path(__file__).parent
cases=[(int(p),1) for p in s.primerange(2,50)]+[(p,r) for p in [2,3,5,7] for r in [2,3]]
checks=[]
for p,r in cases:
    modulus=p**r; period=(p-1)*p**(r-1); stop=3*period+r
    row=[1]; seq=[1]
    for n in range(1,stop+1):
        row=[0]+[(k*((row[k] if k<len(row) else 0)+row[k-1]))%modulus for k in range(1,min(n,p*r-1)+1)]
        seq.append(sum(v*pow(k,n,modulus) for k,v in enumerate(row))%modulus)
    for n in range(r,stop-period+1):assert seq[n+period]==seq[n]
    checks.append({'p':p,'r':r,'period':period,'first_n':r,'last_n_tested':stop-period,'checked':stop-period-r+1})
(P/'congruence_results.json').write_text(json.dumps(checks,indent=2)+'\n')
print('PASS:',sum(c['checked'] for c in checks),'congruences in',len(checks),'prime-power cases')
