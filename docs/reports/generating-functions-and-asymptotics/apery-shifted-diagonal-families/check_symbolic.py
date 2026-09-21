#!/usr/bin/env python3
"""Optional exact symbolic verification; requires SymPy. No numerical input."""
from pathlib import Path
import sympy as s

n, m, j = s.symbols('n m j')
b = (n-j)/(n+j)
c = (m-j)/(m+j)
a = b*c
W = (n*n*m*m-(n*n+m*m)*j*j)/((n+j)*(m+j))
f3 = (n+m)*(n*n+n*m+m*m)
g3 = (n-m)*(n*n-n*m+m*m)
b2 = b
c2 = (m-j)/m
a2 = b2*c2
V = (m*n*n-n*n*j-m*j*j)/(n+j)
f2 = n*n+2*n*m+2*m*m
g2 = n*n-2*n*m+2*m*m
identities = {
    'T linear corner identity': (n+m)*(c-b)-(n-m)*(a-1),
    'T quadratic corner identity': (n*n-n*m+m*m)*(a+1)-(n*n+n*m+m*m)*(b+c)+4*W,
    'T conjugate product': f3*g3-(n**6-m**6),
    'U first contiguity residual': f2*b2-n*n-2*m*m*a2-2*V,
    'U second contiguity residual': f2*c2-2*m*m+n*n*a2-2*(n+m)/m*V,
    'U conjugate product': f2*g2-(n**4+4*m**4),
    'T row coefficient': f3.subs(n,n+1)+g3-(2*n+1)*(n*n+n+2*m*m+2*m+1),
}
lines=['UNIFORM SYMBOLIC CERTIFICATES', 'Exact rational-function identities, verified by SymPy.', '']
for name, expr in identities.items():
    result=s.factor(expr)
    if result != 0:
        raise AssertionError((name,result))
    lines.append(name + ': residual = 0')
lines.append('PASS')
text='\n'.join(lines)+'\n'
Path(__file__).with_name('symbolic_report.txt').write_text(text)
print(text)
