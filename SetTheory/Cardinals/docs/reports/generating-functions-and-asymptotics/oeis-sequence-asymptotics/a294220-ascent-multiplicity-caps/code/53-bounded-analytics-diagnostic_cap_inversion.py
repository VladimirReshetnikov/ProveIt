"""Optional mpmath diagnostics for the continuous cap inverse.

This is numerical quadrature, NOT an interval certificate or a proof.
R denotes n=cap+1, not word length. The integration stops at 100*R;
no rigorous bound is attached to the omitted tail or arithmetic error.
No exact integer-cap decision is certified by these approximate values.
"""
try:
    import mpmath as m
except ImportError as exc:
    raise SystemExit("Optional cap-inversion diagnostics require mpmath.") from exc
m.mp.dps=85
print("Non-certified cap-inversion diagnostics; mpmath", m.__version__, "; dps=85; finite quadrature cutoff=100*R")
A=m.zeta(2);lam=m.log(2);C0=1/(2*A*A)
for R in map(m.mpf,['20.3','30.7','50.1','100.4']):
    L0=R*m.power(2,-R-1)
    def diff(x):
        if not x:return m.mpf(0)
        E=m.exp(x)*m.gammainc(R,x,m.inf)/m.gamma(R)
        return (m.log(E)/(E-1)-x/m.expm1(x))/L0
    cuts=[0,R/3,R/2,2*R/3,m.mpf('.9')*R,R,2*R,5*R,10*R,100*R]
    Delta=L0*m.quad(diff,cuts)
    eps=Delta/(A*(A+Delta))
    x=-m.lambertw(-lam*eps/C0,-1)/lam
    shift=R-x
    lead=4/(m.sqrt(m.pi)*lam*m.sqrt(x))*(m.mpf(8)/9)**x
    print('R =',R,' epsilon =',m.nstr(eps,28))
    print('  W root =',m.nstr(x,32),' estimated shift =',m.nstr(shift,25))
    print('  shift / leading correction =',m.nstr(shift/lead,25))
    print('  x*(ratio-1) =',m.nstr(x*(shift/lead-1),20),' limit =',m.nstr(1/lam-m.mpf(31)/8,20))
