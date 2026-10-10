"""Exact rational principal-lattice bounds, uniform over all even weights.

The infinite tails use the written layer-cake/integral bounds. CM
conjugation and the rational modular polynomial are separate analytic and
arithmetic inputs to the all-CM nonvanishing theorem.
"""
from pathlib import Path
from fractions import Fraction as Q
import json

B=Path(__file__).resolve().parents[1]
N=10;M=20
tail_n=Q(2,3*N**3)+Q(2,N**2)
tail_m=Q(4*N,3)/(Q(M)-Q(N,2))**3
rows=[]
for d,upper in [(7,Q(33,20)),(8,Q(11,8))]:
    def norm(m,n):return m*m-m*n+2*n*n if d==7 else m*m+2*n*n
    assert all(norm(m,n)>=2 for n in range(1,N+1) for m in range(-M,M+1))
    finite=2*sum((Q(1,norm(m,n)**2) for n in range(1,N+1)
                  for m in range(-M,M+1)),Q(0))
    bound=finite+tail_n+tail_m
    assert bound<upper<2
    rows.append(dict(discriminant=-d,finite_lattice_sum=str(finite),
        n_tail_bound=str(tail_n),m_tail_bound=str(tail_m),total_bound=str(bound),
        asserted_upper=str(upper),principal_lower_bound=str(2-upper),passed=True))
report=dict(status='PASS',arithmetic='Exact Python integers and fractions',
    n_cutoff=N,m_cutoff=M,rows=rows,uniform_principal_lower_bound='7/20',
    scope='Finite lattice sums and the displayed rational infinite-tail bounds. Uniformity in the discriminant and weight, and CM Galois propagation, are proved in the manuscript.')
(B/'verification/CM-nonvanishing.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print(json.dumps({**report,'rows':[{k:v for k,v in r.items() if k not in ['finite_lattice_sum','total_bound']} for r in rows]},indent=2))
