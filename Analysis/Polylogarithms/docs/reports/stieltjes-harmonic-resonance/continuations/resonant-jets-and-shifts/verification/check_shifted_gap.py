"""Independent quadrature checks for shifted inverse-color double identities.

The numerical checks are diagnostics, not proofs or certified enclosures.
Only mpmath is required.  The default rational inner shifts use a finite
root-of-unity filter for Lerch Phi, avoiding the double-sum formula under test.
"""
import json
import math
from pathlib import Path
import mpmath as mp

mp.mp.dps = 60


def phi(z, s, u):
    if s == 1:
        return mp.hyp2f1(1, u, u + 1, z) / u
    return mp.lerchphi(z, s, u)


def phi_rational(z, s, p, q):
    if s == 1:
        return mp.hyp2f1(1, mp.mpf(p)/q, 1+mp.mpf(p)/q, z)/(mp.mpf(p)/q)
    if abs(z) < mp.mpf('1e-12'):
        return mp.fsum(z**n / (n + mp.mpf(p)/q)**s for n in range(12))
    omega = mp.exp(2j*mp.pi/q)
    root = z**(mp.mpf(1)/q)
    return q**(s-1) * z**(-mp.mpf(p)/q) * mp.fsum(
        omega**(-p*j)*mp.polylog(s, omega**j*root) for j in range(q))


def gap_integral(a, b, z, u, pv, qv):
    # y=-log t: M=z/(a-1)! int_0^infty exp(-(u+1)y)y^(a-1)
    #             Phi(exp(-y),b,v)/(1-z exp(-y)) dy.
    def kernel(y):
        if y == 0:
            return mp.mpf(0)  # single endpoint, irrelevant for quadrature
        t = mp.exp(-y)
        return z*mp.exp(-(u+1)*y)*y**(a-1)*phi_rational(t,b,pv,qv)/(1-z*t)
    return mp.quad(kernel, [0, mp.mpf('0.2'), 1, 4, mp.inf])/mp.factorial(a-1)


def cotjet(j, u):
    if j == 1:
        return mp.pi*mp.cot(mp.pi*u)
    return mp.zeta(j,u)+(-1)**j*mp.zeta(j,1-u)


def master_rhs(a,b,z,u,v):
    w=a+b
    shift=1+u-v
    s1=mp.fsum((-1)**b*math.comb(w-r-1,b-1)*cotjet(r,u)*phi(z,w-r,shift)
               for r in range(1,a+1))
    s2=mp.fsum((-1)**(b-r)*math.comb(w-r-1,a-1)*cotjet(r,v)*phi(z,w-r,shift)
               for r in range(1,b+1))
    return z*(s1+s2-(-1)**b*phi(z,a,u)*phi(z,b,1-v))


def main():
    reports=[]
    cases=[
        (1,1,mp.mpc('.3','.2'),1,3,2,5),
        (2,1,mp.mpc('-.4','.1'),1,3,1,2),
        (2,2,mp.mpc('.2','.15'),1,2,1,2),
        (3,2,mp.mpc('-.25','.1'),1,3,1,2),
    ]
    for a,b,z,pu,qu,pv,qv in cases:
        u=mp.mpf(pu)/qu
        v=mp.mpf(pv)/qv
        left=gap_integral(a,b,z,u,pv,qv)+(-1)**(a+b)*gap_integral(b,a,z,1-v,qu-pu,qu)
        right=master_rhs(a,b,z,u,v)
        residual=abs(left-right)
        row={'a':a,'b':b,'z':str(z),'u':str(u),'v':str(v),
             'left':mp.nstr(left,45),'right':mp.nstr(right,45),
             'absolute_residual':mp.nstr(residual,8)}
        reports.append(row)
        print(json.dumps(row),flush=True)
        assert residual < mp.mpf('1e-45')
    z=mp.mpf('.37')
    root=mp.sqrt(z)
    chi2=(mp.polylog(2,root)-mp.polylog(2,-root))/2
    chi3=(mp.polylog(3,root)-mp.polylog(3,-root))/2
    for a,right in [(1,2*mp.atanh(root)**2),
                    (2,mp.pi**2*mp.polylog(2,z)-8*chi2**2),
                    (3,32*chi3**2-3*mp.pi**2*mp.polylog(4,z))]:
        left=gap_integral(a,a,z,mp.mpf('.5'),1,2)
        residual=abs(left-right)
        row={'diagonal_half_order':a,'absolute_residual':mp.nstr(residual,8)}
        reports.append(row)
        print(json.dumps(row),flush=True)
        assert residual<mp.mpf('1e-45')
    primitive=mp.mpf(7)/2*mp.zeta(3)-2*mp.pi*mp.catalan
    primitive_quad=-4*mp.quad(lambda t: mp.atan(t)**2/t if t else 0,[0,1])
    residual=abs(primitive-primitive_quad)
    reports.append({'alternating_primitive_residual':mp.nstr(residual,8)})
    assert residual<mp.mpf('1e-45')
    (Path(__file__).resolve().parent.parent/'results'/'shifted_gap_checks.json').write_text(json.dumps(reports,indent=2)+'\n')


if __name__=='__main__':
    main()
