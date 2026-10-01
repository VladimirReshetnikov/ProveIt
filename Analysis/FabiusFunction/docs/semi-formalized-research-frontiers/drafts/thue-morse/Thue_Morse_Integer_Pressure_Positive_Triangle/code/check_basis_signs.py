"""Exploratory exact basis signs; this is not the universal theorem's proof."""
from pathlib import Path
import json
import sympy as s
from check_triangle import matrix_jets
DATA=Path(__file__).resolve().parents[1]/'data'
rows=[]
for m in range(2,10):
    ix,h,_=matrix_jets(m,2*m-2,True);d=len(ix)
    V=s.Matrix(d,d,lambda k,r:2*s.Rational(s.binomial(2*m,m+2*ix[k]-ix[r]),4**m)if abs(2*ix[k]-ix[r])<=m else 0)
    cols=[]
    for j in range(d):
        w=(V-s.Rational(1,2**j)*s.eye(d)).nullspace()[0]
        norm=sum(w[k]*(2*ix[k])**j for k in range(d))
        assert norm!=0
        cols.append(w*((-1)**j*s.factorial(j)/norm))
    W=s.Matrix.hstack(*cols);inv=W.inv()
    for r in range(1,m):
        n=2*r;g=inv*h[n]
        coeff=[s.factor(s.S.NegativeOne**((n-j)//2)*g[j])if j%2==0 else s.S.Zero for j in range(d)]
        assert all(g[j]==0 for j in range(1,d,2))
        assert all(v>=0 for v in coeff)
        rows.append({'m':m,'r':r,'negative_basis_degrees':[],'coefficients':list(map(str,coeff))})
reference=json.loads((DATA/'exploratory_basis_signs.json').read_text())['rows']
assert rows==reference
print('36 exact exploratory basis responses match; no universal basis-positivity claim')
