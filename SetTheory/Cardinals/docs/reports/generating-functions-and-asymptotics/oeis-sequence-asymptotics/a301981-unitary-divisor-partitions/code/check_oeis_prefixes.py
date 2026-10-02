"""Independent finite-binomial check against the inspected OEIS prefixes."""
from pathlib import Path
from math import comb, gcd
import json
base=Path(__file__).resolve().parents[1]
expected=json.loads((base/'data/oeis-prefixes.json').read_text())
def usigma(n):
    return sum(d for d in range(1,n+1) if n%d==0 and gcd(d,n//d)==1)
def coefficients(N,distinct):
    a=[1]+[0]*N
    for k in range(1,N+1):
        b=usigma(k); result=[0]*(N+1)
        for j in range(N//k+1):
            coefficient=(comb(b,j) if j<=b else 0) if distinct else comb(b+j-1,j)
            for n in range(j*k,N+1): result[n]+=coefficient*a[n-j*k]
        a=result
    return a
out={}
for seq,record in expected.items():
    result=coefficients(record['num_terms']-1,record['distinct_colors'])
    assert result==record['terms'],seq
    out[seq]={'num_terms':len(result),'exact_match':True}
print(json.dumps(out,indent=2))
