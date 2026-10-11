"""Independent Mellin-series and coordinate-quadrature cubic check."""
import json
import time
from pathlib import Path
import mpmath as mp
import sympy as sp

mp.mp.dps = 65

def diagonal_tornheim(s, cutoff=1, terms=72, tail=150):
    """Meromorphic T(s,s,s), using Jonquiere at 0 and an exponential tail.

    The two summations are absolutely convergent for cutoff < 2*pi.
    Numeric truncation here is diagnostic, not an interval certificate.
    """
    b = mp.mpf(cutoff)
    g = mp.gamma(1-s)
    z = [mp.zeta(s-k)*(-1)**k/mp.factorial(k) for k in range(terms)]
    singular = g*g*b**(3*s-2)/(3*s-2)
    mixed = 2*g*mp.fsum(z[k]*b**(2*s+k-1)/(2*s+k-1)
                        for k in range(terms))
    regular = mp.fsum(mp.fsum(z[j]*z[k-j] for j in range(k+1))
                      *b**(s+k)/(s+k) for k in range(terms))
    upper = mp.fsum(mp.gammainc(s,n*b,mp.inf)*n**(-s)
                    *mp.fsum(mp.mpf(m*(n-m))**(-s) for m in range(1,n))
                    for n in range(2,tail+1))
    return (singular+mixed+regular+upper)/mp.gamma(s)

def derivative_from_values(vals, nodes, order, h):
    weights = sp.finite_diff_weights(order, nodes, 0)[-1][-1]
    return mp.fsum(mp.mpf(str(w.p))/int(w.q)*vals[n]
                   for n,w in zip(nodes,weights))/h**order

def cubic_coordinate_value(split=mp.mpf('0.25'), terms=120):
    # psi(x)=-1/x + sum c[k]*x**k; evaluate subtraction stably near 0.
    c = [-mp.euler] + [(-1)**(k+1)*mp.zeta(k+1) for k in range(1,terms)]
    cube = {}
    v = {-1:mp.mpf(-1), **dict(enumerate(c))}
    for a,va in v.items():
        for b,vb in v.items():
            if a+b > terms: continue
            for d,vd in v.items():
                e = a+b+d
                if e <= terms-3: cube[e] = cube.get(e,0)+va*vb*vd
    small = mp.fsum(coef*(mp.log(split) if e==-1 else split**(e+1)/(e+1))
                    for e,coef in cube.items())
    return small+mp.quad(lambda x:mp.digamma(x)**3,[split,mp.mpf('0.5'),1])

if __name__ == '__main__':
    started=time.time()
    h=mp.mpf('0.0001')
    nodes=list(range(-7,8))
    vals={0:mp.mpf(1)/3}
    for n in nodes:
        if n:
            vals[n]=diagonal_tornheim(n*h)
            print('evaluated',n,'elapsed',round(time.time()-started,1),flush=True)
    ts=[mp.mpf(1)/3]+[derivative_from_values(vals,nodes,k,h) for k in range(1,4)]
    L=mp.log(2*mp.pi);g=mp.euler
    zpp=mp.diff(mp.zeta,0,2);zppp=mp.diff(mp.zeta,0,3)
    z2=mp.zeta(2);z2p=mp.diff(mp.zeta,2)
    formula=(-ts[3]-8*zppp-12*(g+L)*zpp-L**3-6*g*L**2
             +5*g**3+6*g*mp.stieltjes(1)-mp.mpf('1.5')*g*z2
             +mp.mpf('1.5')*(z2+z2p))
    direct=cubic_coordinate_value()
    result={
        'precision_digits':mp.mp.dps,'method':'independent truncated Mellin series and coordinate quadrature; not certified',
        'T_derivatives':[mp.nstr(v,55) for v in ts],
        'T1_residual':mp.nstr(ts[1]-L,8),
        'T2_residual':mp.nstr(ts[2]-(L*L-4*zpp),8),
        'cubic_formula':mp.nstr(formula,55),
        'cubic_coordinate':mp.nstr(direct,55),
        'cubic_residual':mp.nstr(formula-direct,8),
        'elapsed_seconds':time.time()-started,
    }
    print(json.dumps(result,indent=2))
    (Path(__file__).resolve().parents[1]/'results'/'cubic_results.json').write_text(json.dumps(result,indent=2))
