#!/usr/bin/env python3
"""Independent integer-Hermite verification of selected exact coefficient depths.
The source rows are constructed by coefficient_depth.setup. Unlike its
p-local incremental elimination, this uses SymPy's integer column HNF.
"""
from coefficient_depth import setup,vp,wq
from fractions import Fraction
from math import lcm
import json
from sympy import Matrix
from sympy.matrices.normalforms import hermite_normal_form

def compute(p,N,target):
    D,H=setup(p,N); rows=[]; max_den_power=0
    indices=list(range(target%(p*p-1),N+1,p*p-1))
    for m in indices:
        for name,h in H:
            row=[h[n]*D[n][m] if n<=m else Fraction(0) for n in indices]
            if not any(row):continue
            den=lcm(*(x.denominator for x in row)); den_power=vp(den,p)
            max_den_power=max(max_den_power,den_power)
            rows.append(([int(x*den) for x in row],den_power))
    scaled=[[p**(max_den_power-k)*x for x in row] for row,k in rows]
    d=len(indices)
    # A triangular source submatrix has determinant of valuation M.
    # Its adjugate proves p^M Z_p^d is already in the p-local lattice.
    # Adding p^M I and reducing all entries modulo p^M therefore preserves
    # that lattice while removing irrelevant odd-prime denominators.
    M=sum(min(vp(row[j],p) for row in scaled if row[j] and not any(row[j+1:])) for j in range(d))
    modulus=p**M
    columns=[[x%modulus for x in row] for row in scaled]
    columns.extend([[modulus if i==j else 0 for i in range(d)] for j in range(d)])
    mat=Matrix([[row[i] for row in columns] for i in range(d)])
    HNF=hermite_normal_form(mat,D=modulus**d)
    assert HNF.shape==(len(indices),len(indices))
    pivots={n:vp(int(HNF[i,i]),p)-max_den_power for i,n in enumerate(indices)}
    return {'p':p,'q':p*p,'cutoff':N,'target':target,'raw_nonzero_rows':len(rows),'scaled_denominator_power':max_den_power,'leading_ideal_valuation':pivots[target],'optimal_leading_valuation':-wq(target,p*p),'meets_target':pivots[target]==-wq(target,p*p),'method':'integer column Hermite normal form after per-row p-adic-unit denominator clearing','all_pivot_valuations':pivots,'saturation_bound_power':M}

if __name__=='__main__':
    examples=[(2,3,6),(2,5,8),(2,7,16),(2,12,30),(3,8,16)]
    results=[]
    for p,n,s in examples:
        pair=[compute(p,N,n) for N in (s-1,s)]
        assert pair[0]['leading_ideal_valuation']>pair[0]['optimal_leading_valuation']
        assert pair[1]['leading_ideal_valuation']==pair[1]['optimal_leading_valuation']
        results.append({'p':p,'n':n,'s0':s,'checks':pair})
    print(json.dumps({'certificate':'Five exact s0 values, proved by obstruction below and attainment at cutoff','results':results},indent=2))
