from pathlib import Path
import json
import sympy as s
from independent_audit import residuals,FIELDS
ans=[]
for N in (1,2,3):
    rows=[];variables=[]
    for i in range(N):
        row={f:s.Symbol(f'{f}_{i}') for f in FIELDS}
        row['t']=list(s.symbols(f't_{i}_0:5'))
        row['pointers']=[list(s.symbols(f'delta_{i}_{k}_0:{N}')) for k in range(3)]
        rows.append(row);variables+=list(row[f] for f in FIELDS)+row['t']+sum(row['pointers'],[])
    p,n,o=s.symbols('p n o')
    rs=residuals(rows,p,n,o)
    assert len(variables)==3*N*N+19*N and len(rs)==23*N+3
    degrees=[s.Poly(r,*variables,p,n,o).total_degree() for r in rs]
    # Square each residual separately; summing exact rational coefficients permits no hidden degree assumptions.
    P=s.Poly(sum(s.expand(r*r) for r in rs),*variables,p,n,o)
    assert max(degrees)==2 and P.total_degree()==4
    ans.append({'N':N,'witnesses':len(variables),'residuals':len(rs),'max_residual_degree':max(degrees),'expanded_SOS_degree':P.total_degree(),'expanded_monomials':len(P.terms())})
Path(__file__).with_name('symbolic_receipt.json').write_text(json.dumps(ans,indent=2)+'\n')
print(json.dumps(ans,indent=2))
