"""Floating-point illustrations, kept separate from exact certificates."""
from __future__ import annotations
from pathlib import Path
import csv
import math
import numpy as np
from scipy.optimize import brentq
from scipy.sparse import coo_matrix
from scipy.sparse.linalg import eigs
from model import component

ROOT = Path(__file__).resolve().parents[1]

def normalized_catalan_blocks(m: int) -> np.ndarray:
    """b[k] = C_(k-1)/4**k, with b[0]=0, without huge integers."""
    b = np.zeros(m+1)
    b[1] = .25
    if m > 1:
        k = np.arange(1,m,dtype=float)
        b[2:] = .25*np.cumprod((2*k-1)/(2*(k+1)))
    return b

def block_coefficients(b: np.ndarray, d: int) -> np.ndarray:
    """c_(k,d)/4**k, using the exact-formula consecutive-j ratio."""
    m = len(b)-1
    c = np.zeros(m+1)
    c[1] = .25
    h = np.zeros(m+1)
    h[2:] = b[1:m]/4
    c += h
    for j in range(1,d):
        new = np.zeros(m+1)
        k = np.arange(j+2,m+1,dtype=float)
        new[j+2:] = h[j+2:] * ((j+1)/j) * (k-j-1)/(2*k-j-3)
        h = new
        c += h
    return c

def tilt_root(b: np.ndarray, m: int) -> float:
    k = np.arange(1,len(b),dtype=float)
    coeff = b[1:]
    def f(t: float) -> float:
        return float(np.sum(coeff*np.exp(t*k/m)))-1.0
    hi = 1.0
    while f(hi) < 0:
        hi *= 2
    return brentq(f,0,hi,xtol=3e-13)

def rate(m: int, kind: str) -> float:
    states, edges = component(m,kind)
    n = len(states)
    row = np.array([e[0] for e in edges])
    col = np.array([e[1] for e in edges])
    deg = np.array([e[2] for e in edges])
    coef = np.array([float(e[3]) for e in edges])
    def f(x: float) -> float:
        A = coo_matrix((coef*x**deg,(row,col)),shape=(n,n)).tocsr()
        if n <= 3:
            rho = max(abs(np.linalg.eigvals(A.toarray())))
        else:
            rho = float(eigs(A,k=1,which='LR',v0=np.ones(n),
                             return_eigenvectors=False,tol=2e-11)[0].real)
        return rho-1
    return 1/brentq(f,.25,1.2,xtol=3e-13)

def main() -> None:
    ms = sorted(set([10,20,50,100,200,500,1000,10000,100000,1000000]
                    + [int(v) for v in np.geomspace(20,1000000,55)]))
    rows = []
    for m in ms:
        d = min(m-1,math.ceil(math.log2(m)))
        b = normalized_catalan_blocks(m)
        t = tilt_root(b,m)
        block = block_coefficients(b,d)[:m-d+1]
        s = tilt_root(block,m)
        beta = 4*math.exp(-t/m)
        lower = 4*math.exp(-s/m)
        L = .5*math.log(m)
        z = math.log(L)+math.log(2*math.sqrt(math.pi))
        P = [z-1.5,-z*z/2+2.5*z-33/8,z**3/3-3*z*z+43*z/4-15]
        approximations = [L+z]
        for j,p in enumerate(P,1):
            approximations.append(approximations[-1]+p/L**j)
        row = {'m':m,'d':d,'t':t,'beta':beta,'block_lower':lower,
               'E_lower':m*(4-beta)-2*math.log(m)-4*math.log(math.log(m)),
               'E_upper':m*(4-lower)-2*math.log(m)-4*math.log(math.log(m)),
               'corridor_width':beta-lower}
        for j,a in enumerate(approximations):
            row[f't_approx_{j}'] = a
        rows.append(row)
    with (ROOT/'data'/'scalar_numerics.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
    component_rows=[]
    for m in [2,3,4,5,10,20,30,50]:
        u,v=rate(m,'U'),rate(m,'V')
        b=normalized_catalan_blocks(m)
        beta=4*math.exp(-tilt_root(b,m)/m)
        assert max(u,v) < beta
        component_rows.append({'m':m,'lambda_U':u,'lambda_V':v,
                               'alpha':max(u,v),'beta':beta})
    with (ROOT/'data'/'component_numerics.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(component_rows[0]));w.writeheader();w.writerows(component_rows)
    print('Numerical component comparisons (not interval certificates):')
    for row in component_rows:
        print(row)
    print('Selected scalar results:')
    for row in rows:
        if row['m'] in [100,1000,10000,100000,1000000]:
            print(row)

if __name__=='__main__':
    main()
