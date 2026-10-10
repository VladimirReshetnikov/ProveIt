"""Independent numerical checks for periodic Hurwitz jet correlations.

Numerical diagnostics only; the theorem proofs are analytic, not numerical.
"""
import json
from pathlib import Path
import mpmath as mp

mp.mp.dps = 45

def split_integral(fun, a):
    # Integrate the two analytic pieces with endpoint singularities isolated.
    return (mp.quad(lambda x: fun(x, x+a), [0, (1-a)/2, 1-a])
            + mp.quad(lambda v: fun(v+1-a, v), [0, a/2, a]))

def kernel(s,t,a):
    z=mp.exp(2j*mp.pi*a)
    return (mp.gamma(1-s)*mp.gamma(1-t)*(2*mp.pi)**(s+t-2)
            *(mp.exp(0.5j*mp.pi*(t-s))*mp.polylog(2-s-t,z)
              +mp.exp(0.5j*mp.pi*(s-t))*mp.polylog(2-s-t,1/z)))

def g_cov(a):
    A=mp.euler+mp.log(2*mp.pi)
    z=mp.exp(2j*mp.pi*a)
    # Generic polylog implementations subtract gamma/zeta poles near an
    # integer order. The automatic infinitesimal differentiation step can
    # lose most digits. Use a resolved, fourth-order symmetric stencil.
    with mp.workdps(110):
        h=mp.mpf('1e-12')
        vals={j:mp.polylog(2+j*h,z) for j in [-2,-1,0,1,2]}
        d1=(vals[-2]-8*vals[-1]+8*vals[1]-vals[2])/(12*h)
        d2=(-vals[2]+16*vals[1]-30*vals[0]+16*vals[-1]-vals[-2])/(12*h*h)
        ans=mp.re((d2-2*A*d1+(A*A+mp.pi**2/4)*vals[0])/(2*mp.pi**2))
    return +ans

def g_cov_hurwitz(a):
    q=lambda s: mp.zeta(s,a)+mp.zeta(s,1-a)
    B2=a*a-a+mp.mpf(1)/6
    return -mp.diff(q,-1,2)/2-mp.diff(q,-1)+(1+mp.pi**2/6)*B2

def structure_series(a, terms=100):
    L=-mp.log(a)
    return (a*(L*L+2*L+2+mp.pi**2/3)
            +(2*mp.stieltjes(1)-mp.pi**2/3)*a*a
            -mp.fsum(2*a**(2*j)/(j*(2*j-1))
                     *(mp.harmonic(2*j-2)*mp.zeta(2*j-1)+mp.diff(mp.zeta,2*j-1))
                     for j in range(2,terms+1)))

def residual(lhs,rhs):
    return mp.nstr(abs(lhs-rhs),8)

records = []
def record(tag,lhs,rhs):
    kind = 'asymptotic' if ('cusp' in tag) else 'identity'
    if kind == 'identity':
        assert abs(lhs-rhs) < mp.mpf('1e-29'), (tag, abs(lhs-rhs))
    obj = {'check':tag,'kind':kind,'lhs':mp.nstr(lhs,30),
           'rhs':mp.nstr(rhs,30),'absolute_error':residual(lhs,rhs)}
    records.append(obj)
    print(json.dumps(obj),flush=True)

for s,t,a in [(mp.mpf('-.3'),mp.mpf('-.7'),mp.mpf('.23')),
              (mp.mpf('.37'),mp.mpf('.26'),mp.mpf('.31')),
              (mp.mpc('-.4','.2'),mp.mpc('.15','-.1'),mp.mpf('.4'))]:
    lhs=split_integral(lambda x,y: mp.zeta(s,x)*mp.zeta(t,y),a)
    record('Hurwitz correlation '+str((s,t,a)),lhs,kernel(s,t,a))

for a in [mp.mpf('.125'),mp.mpf('.3'),mp.mpf('.5')]:
    lhs=split_integral(lambda x,y: mp.loggamma(x)*mp.loggamma(y),a)
    record('logGamma correlation '+str(a),lhs,mp.log(2*mp.pi)**2/4+g_cov(a))
    record('Hurwitz versus polylog covariance '+str(a),g_cov_hurwitz(a),g_cov(a))

A=mp.euler+mp.log(2*mp.pi)
C0=(mp.diff(mp.zeta,2,2)-2*A*mp.diff(mp.zeta,2)
    +(A*A+mp.pi**2/4)*mp.zeta(2))/(2*mp.pi**2)
smooth=(mp.diff(mp.zeta,0,2)-2*A*mp.diff(mp.zeta,0)
        +(A*A+mp.pi**2/4)*mp.zeta(0))
for a in [mp.mpf('1e-2'),mp.mpf('1e-4'),mp.mpf('1e-7')]:
    L=-mp.log(a)
    exact=2*(C0-g_cov_hurwitz(a))
    leading=a*(L*L+2*L+2+mp.pi**2/3)
    record('logGamma cusp including quadratic '+str(a),exact,leading+2*smooth*a*a)
    print(json.dumps({'check':'quadratic_scaled_error '+str(a),
                      'ratio':mp.nstr((exact-leading)/(a*a),30),
                      'limit':mp.nstr(2*smooth,30)}),flush=True)

for a in [mp.mpf('.125'),mp.mpf('.3'),mp.mpf('.5')]:
    record('convergent odd-zeta structure series '+str(a),
           2*(C0-g_cov_hurwitz(a)),structure_series(a))

def F(s,t):
    return (mp.gamma(1-s)*mp.gamma(1-t)/mp.gamma(2-s-t)
            *mp.cos(mp.pi*(s-t)/2)/mp.cos(mp.pi*(s+t)/2))

for r,m,a in [(1,2,mp.mpf('.03')),(2,2,mp.mpf('.01'))]:
    even=lambda s,t: -F(s,t)*(mp.zeta(s+t-1,a)+mp.zeta(s+t-1,1-a))/2
    diagonal=lambda s,t: (2*mp.gamma(1-s)*mp.gamma(1-t)
                         *(2*mp.pi)**(s+t-2)
                         *mp.cos(mp.pi*(s-t)/2)*mp.zeta(2-s-t))
    exact=2*mp.diff(lambda s,t: diagonal(s,t)-even(s,t),(0,0),(r,m))
    L=-mp.log(a)
    lead=a*mp.diff(lambda s,t: F(s,t)*mp.exp(L*(s+t)),(0,0),(r,m))
    quadratic=2*a*a*mp.diff(lambda s,t: mp.gamma(1-s)*mp.gamma(1-t)
                            *(2*mp.pi)**(s+t)*mp.cos(mp.pi*(s-t)/2)
                            *mp.zeta(-s-t),(0,0),(r,m))
    record('mixed jets cusp '+str((r,m,a)),exact,lead+quadratic)


out = Path(__file__).resolve().parents[1] / 'data' / 'gamma_calculus_checks.jsonl'
out.write_text(''.join(json.dumps(row)+'\n' for row in records))
print('All identity diagnostics passed; asymptotic differences recorded separately.')
