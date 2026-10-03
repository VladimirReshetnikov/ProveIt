"""A fully specialized 17-witness quartic for x'=1 and two Euler steps."""
from pathlib import Path
import json
import sympy as sp


def main():
    R,H,D = sp.symbols('R H D')
    A,G,r,h,d,tlo,thi = sp.symbols('A G r h d tlo thi')
    X = (sp.Integer(0),) + sp.symbols('X1:3')
    U = sp.symbols('U0:2')
    S = sp.symbols('S0:2')
    lm = sp.symbols('lm0:2')
    lp = sp.symbols('lp0:2')
    residuals = [A-D*H, G-R*A+D, R-1-r, H-1-h, D-1-d]
    for i in range(2):
        residuals.extend([H*(X[i+1]-X[i])+U[i]-D, U[i]+S[i]+1-H,
                          G-H*i-H*X[i]-1-lm[i], G-H*i+H*X[i]-1-lp[i]])
    residuals.extend([10*X[2]-9*D-20-1-tlo, 11*D-10*X[2]-20-1-thi])
    values = {R:2,H:2,D:100,A:200,G:300,r:1,h:1,d:99,tlo:79,thi:79,
              X[1]:50,X[2]:100,U[0]:0,U[1]:0,S[0]:1,S[1]:1,
              lm[0]:299,lp[0]:299,lm[1]:197,lp[1]:397}
    assert all(p.subs(values) == 0 for p in residuals)
    P = sp.expand(sum(p*p for p in residuals))
    degree = sp.Poly(P, *sorted(P.free_symbols, key=str)).total_degree()
    witnesses = {str(k):v for k,v in values.items() if k not in (R,H,D)}
    assert degree == 4 and len(witnesses) == 17 and len(residuals) == 15
    out = Path(__file__).resolve().parents[1] / 'results'
    result = {'parameters':{'R':2,'H':2,'D':100}, 'witness':witnesses,
              'witness_count':17, 'equation_count':15, 'degree':4,
              'residuals':[str(p) for p in residuals], 'all_residuals_zero':True}
    (out/'specialized_constant_quartic.json').write_text(json.dumps(result,indent=2)+'\n')
    (out/'specialized_constant_expanded.txt').write_text(str(P)+'\n')
    print(json.dumps(result,indent=2))

if __name__ == '__main__':
    main()
