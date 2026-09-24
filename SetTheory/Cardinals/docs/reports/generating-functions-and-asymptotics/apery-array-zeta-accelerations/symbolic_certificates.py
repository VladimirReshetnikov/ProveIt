#!/usr/bin/env python3
"""Optional symbolic checks; requires SymPy. All printed residuals must be zero."""
import sympy as sp

m, n, j = sp.symbols('m n j')
rm=(m-j)/(m+j)
rn3=(n-j)/(n+j)
rn2=(n-j)/n
s=(m+n)*(m*m+m*n+n*n)
q=n*n+(m+n)**2

delta3=j**4/((m+j)*(n+j))-(m-j)*(n-j)
delta2=j**3/(m+j)-(m-j)*(n-j)

residuals={
    'zeta3_telescoper':m**3+n**3*rm*rn3-s*rm-2*(m+n)*delta3,
    'zeta2_second_telescoper':m*m+2*n*n*rm*rn2-q*rm-2*delta2,
    'zeta2_first_telescoper':2*n*n-m*m*rm*rn2-q*rn2-2*(m+n)/n*delta2,
    'zeta3_diagonal_recurrence':6*(2*n+1)*(3*n*n+3*n+1)-(n+1)**3-n**3
                               -(34*n**3+51*n*n+27*n+5),
    'zeta2_diagonal_recurrence':5*(n*n+(2*n+1)**2)+(n+1)**2-4*n*n
                               -2*(11*n*n+11*n+3),
}
for name, residual in residuals.items():
    answer=sp.factor(residual)
    print(f'{name}: {answer}')
    assert answer == 0
print(f'PASS: {len(residuals)} symbolic identities; SymPy {sp.__version__}')
