"""Independent high-precision diagnostics; no interval certification.

Run --part 1, --part 2, --part 3 separately or omit --part for all.
Series use a finite head plus mpmath Euler--Maclaurin tail (sumem).
The tolerance is an assertion threshold, not a proven error bound.
"""
from __future__ import annotations
from pathlib import Path
import argparse, json, platform
import mpmath as mp
ROOT=Path(__file__).resolve().parents[1]
mp.mp.dps=40
records=[]
def series(f,head=100):
    return mp.fsum(f(n) for n in range(head))+mp.sumem(f,[head,mp.inf])
def record(name,lhs,rhs,parameters=None,method='finite head + Euler--Maclaurin tail'):
    err=abs(lhs-rhs)/max(1,abs(rhs))
    item={'name':name,'parameters':parameters or {},'method':method,
          'lhs':mp.nstr(lhs,39),'rhs':mp.nstr(rhs,39),
          'scaled_residual':mp.nstr(err,12),'tolerance':'1e-28',
          'pass':bool(err<mp.mpf('1e-28'))}
    records.append(item)
    print(name,mp.nstr(err,6),flush=True)
    if not item['pass']: raise AssertionError(item)

def part1():
    L=mp.log(2); z=mp.zeta
    H=lambda n:mp.digamma(n+1)+mp.euler
    H3=lambda n:z(3)-z(3,n+1)
    rhs1=mp.mpf(45)/32*z(4)-mp.mpf(7)/4*L*z(3)
    rhs2=(31*z(5)-45*L*z(4)+28*L**2*z(3)-7*z(2)*z(3))/8
    rhs3=(-14*L**3*z(3)+mp.mpf(21)/2*L*z(2)*z(3)
        -mp.mpf(21)/4*z(3)**2+mp.mpf(135)/4*L**2*z(4)
        -mp.mpf(93)/2*L*z(5)+mp.mpf(945)/64*z(6))
    rhs4=(14*L**4*z(3)-21*L**2*z(2)*z(3)+21*L*z(3)**2
        -45*L**3*z(4)+93*L**2*z(5)-mp.mpf(945)/16*L*z(6)
        -mp.mpf(39)/2*z(3)*z(4)-mp.mpf(93)/4*z(2)*z(5)
        +mp.mpf(1143)/16*z(7))
    for name,f,r in [('linear',lambda n:H(n),rhs1),
                     ('quadratic',lambda n:H(n)**2,rhs2),
                     ('cubic',lambda n:2*H(n)**3+H3(n),rhs3),
                     ('quartic',lambda n:H(n)**4+2*H(n)*H3(n),rhs4)]:
        record('half_center_'+name,series(lambda n:f(n)/(2*n+1)**3),r)
    def f(x):
        if x==0 or x==1:return mp.mpf(0)
        return mp.log(x)**2*(mp.polylog(2,x*x)+mp.log1p(-x*x)**2)/(2*(1-x*x))
    record('dilogarithmic_integral',mp.quad(f,[0,mp.mpf('.5'),mp.mpf('.9'),1]),rhs2,
           method='independent tanh--sinh quadrature')

def part2():
    for astr in ['0.5','0.75','1','1.25']:
        a=mp.mpf(astr); ps=mp.digamma
        for k in [1,2]:
            lhs=series(lambda n:(ps(n+1)+ps(n+2*a))/(n+a)**(2*k+1))
            rhs=((mp.mpf(2*k+1)/2)*mp.zeta(2*k+2,a)
              +2*ps(a)*mp.zeta(2*k+1,a)
              -sum(mp.zeta(2*j+1,a)*mp.zeta(2*k-2*j+1,a) for j in range(1,k)))
            record('general_linear',lhs,rhs,{'a':astr,'k':k})
        lhs=series(lambda n:((ps(n+1)+ps(n+2*a))**2
                             +mp.polygamma(1,n+1)-mp.polygamma(1,n+2*a))/(n+a)**3)
        rhs=(-mp.polygamma(4,a)/6+ps(a)*mp.polygamma(3,a)
              -(2*ps(a)**2+mp.zeta(2)-mp.polygamma(1,a))*mp.polygamma(2,a))
        record('general_quadratic',lhs,rhs,{'a':astr})

def part3():
    for astr in ['0.5','0.75','1.25']:
        a=mp.mpf(astr)
        lhs=series(lambda n:(2*mp.log(n+a)-mp.digamma(n+1)-mp.digamma(n+2*a))/(n+a))
        rhs=mp.digamma(a)**2-mp.polygamma(1,a)/2+mp.zeta(2)/2+2*mp.stieltjes(1,a)
        record('stieltjes_boundary',lhs,rhs,{'a':astr})
        v=a/3
        lhs=series(lambda n:mp.atanh(v/(n+a))-v/(n+a))
        rhs=v*mp.digamma(a)-(mp.loggamma(a+v)-mp.loggamma(a-v))/2
        record('gamma_primitive',lhs,rhs,{'a':astr,'v':'a/3'})
    for u,t in [(mp.mpf('.25'),mp.mpf('.4')),(mp.mpf('-.25'),mp.mpf('.3'))]:
        def P(n):
            return mp.gamma(n+1-u)/mp.gamma(n+1+u)*mp.gamma(1+u)/mp.gamma(1-u)
        def G(t):
            return (mp.gamma(1+u)**2*mp.gamma((1+t)/2)*mp.gamma((1-t)/2)
                   /mp.gamma((1+t)/2+u)/mp.gamma((1-t)/2+u))
        lhs=series(lambda n:t*t*P(n)/((2*n+1)*((2*n+1)**2-t*t)))
        record('normalized_resolvent',lhs,(G(t)-G(0))/(4*u),
               {'u':str(u),'t':str(t)})
    for k in [1,2,3]:
        lhs=series(lambda n:mp.mpf(1)/((n+1)*(n+2)*(2*n+3)**(2*k+1)))
        rhs=4*k+3-4*mp.log(2)-4*sum((1-mp.mpf(2)**(-2*j-1))*mp.zeta(2*j+1) for j in range(1,k+1))
        record('revived_zero_rational_sum',lhs,rhs,{'k':k})

def main():
    parser=argparse.ArgumentParser(); parser.add_argument('--part',type=int,choices=[1,2,3])
    args=parser.parse_args()
    chosen=[args.part] if args.part else [1,2,3]
    for part in chosen:
        records.clear(); globals()[f'part{part}']()
        report={'status':'PASS','part':part,'dps':mp.mp.dps,
          'python':platform.python_version(),'mpmath':mp.__version__,
          'certified_error_bounds':False,'records':records.copy()}
        (ROOT/'results'/f'numerical_part{part}.json').write_text(json.dumps(report,indent=2)+'\n')
    files=[ROOT/'results'/f'numerical_part{i}.json' for i in [1,2,3]]
    if all(p.exists() for p in files):
        reports=[json.loads(p.read_text()) for p in files]
        combined=[r for data in reports for r in data['records']]
        out={'status':'PASS','dps':mp.mp.dps,'certified_error_bounds':False,
             'total_checks':len(combined),
             'maximum_scaled_residual':str(max(mp.mpf(r['scaled_residual']) for r in combined)),
             'records':combined}
        (ROOT/'results'/'numerical_checks.json').write_text(json.dumps(out,indent=2)+'\n')
if __name__=='__main__': main()
