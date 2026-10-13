"""Independent ordinary quadrature for absolute Stieltjes reconstruction.

The integrands are evaluated directly with digamma. Small-x Taylor tails
and large-x Bernoulli tails are integrated separately. Results are checked
against mpmath.stieltjes and explicit alternating/confluent values; neither
the Mellin germ nor the reconstruction formula is used to integrate.
These are precision/truncation diagnostics, not interval certificates.
"""
import argparse
import hashlib
import json
from functools import lru_cache
from math import comb, factorial
from pathlib import Path
import platform
import sys
import time
import mpmath as mp

HERE=Path(__file__).resolve()
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--precision',type=int,default=60)
parser.add_argument('--cutoff',type=int,default=64)
parser.add_argument('--small-order',type=int,default=48)
parser.add_argument('--tail-order',type=int,default=100)
parser.add_argument('--output',type=Path,default=HERE.with_suffix('.json'))
args=parser.parse_args()
if min(args.precision,args.cutoff,args.small_order,args.tail_order)<16:
    parser.error('All precision and truncation parameters must be at least16')
mp.mp.dps=args.precision
started=time.monotonic()
records=[]
cases=[]
tolerance=mp.power(10,18-args.precision)
meta={'digest_mode':'lf-normalized',
      'script_sha256':hashlib.sha256(HERE.read_bytes().replace(b'\r\n',b'\n')).hexdigest(),
      'source_sha256':{},'source_note':'Direct digamma evaluation; no repository evaluator is imported.',
      'python_version':platform.python_version(),'mpmath_version':mp.__version__,
      'optimization_level':sys.flags.optimize,'dps':args.precision,
      'settings':{'cutoff':args.cutoff,'small_order':args.small_order,'tail_order':args.tail_order},
      'scaled_tolerance':mp.nstr(tolerance,8)}

def save(status):
    result={**meta,'status':status,'count':len(records),'comparisons':records,'cases':cases,
            'max_abs_error':mp.nstr(max((mp.mpf(x['abs_error']) for x in records),default=mp.mpf(0)),14),
            'elapsed_seconds':round(time.monotonic()-started,3),
            'scope':'Ordinary digamma quadrature plus truncated endpoint expansions; diagnostic, not interval certification.'}
    args.output.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    return result

def check(name,lhs,rhs):
    error=abs(lhs-rhs)
    row={'name':name,'lhs':mp.nstr(lhs,args.precision+4),'rhs':mp.nstr(rhs,args.precision+4),
         'abs_error':mp.nstr(error,14)}
    records.append(row)
    print(name,mp.nstr(error,8),flush=True)
    if not error<tolerance*max(1,abs(rhs)):
        save('FAIL')
        raise RuntimeError(f'Quadrature comparison failed: {row}')
    save('running')

def moments(fn,a,beta_min,beta_max,small,large,max_log,u0=0):
    """Integrate x^(u0-1)*log^j(x)*fn(x), sharing direct evaluations.

    small/large are lists (power, coefficient) for x^power/x^-power.
    Bounds keep all scaled small arguments <a/cutoff and all scaled
    large arguments >cutoff*max(1,a).
    """
    eps=a/(args.cutoff*beta_max)
    stop=args.cutoff*max(1,a)/beta_min
    lo,hi=mp.log(eps),mp.log(stop)
    nodes=[lo]+[mp.mpf(t) for t in [-2,-1,0,1,2] if lo<t<hi]+[hi]
    @lru_cache(maxsize=None)
    def base(t):
        return mp.exp(u0*t)*fn(mp.exp(t))
    out=[]
    for j in range(max_log+1):
        core=mp.quad(lambda t:t**j*base(t),nodes)
        left=mp.mpf(0)
        for power,c in small:
            rate=power+u0
            if rate<=0:
                if c!=0:
                    raise RuntimeError('Nonintegrable small-x coefficient')
                continue
            left+=c*eps**rate*mp.fsum((-1)**h*comb(j,h)*factorial(h)*lo**(j-h)/rate**(h+1)
                                      for h in range(j+1))
        right=mp.mpf(0)
        for power,c in large:
            rate=power-u0
            if rate<=0:
                if abs(c)>tolerance:
                    raise RuntimeError('Nonintegrable large-x coefficient')
                continue
            right+=c*stop**(-rate)*mp.fsum(comb(j,h)*factorial(h)*hi**(j-h)/rate**(h+1)
                                          for h in range(j+1))
        out.append(core+left+right)
    return out

@lru_cache(maxsize=None)
def gammas(a):
    return tuple(mp.stieltjes(n,a) for n in range(3))

save('running')
for scale_pair in [(2,2),(2,3)]:
    L,M=map(mp.log,scale_pair)
    p=L*M
    A=mp.pi**2/6+(L**2+M**2)/24
    betas=[mp.exp((L+M)/2),mp.exp((M-L)/2),mp.exp((L-M)/2),mp.exp(-(L+M)/2)]
    weights=[-1,1,1,-1]
    for tag,a in [('1',mp.mpf(1)),('1/3',mp.mpf(1)/3),('sqrt2',mp.sqrt(2))]:
        def fn(x):
            return mp.fsum(w*mp.digamma(a+b*x) for w,b in zip(weights,betas))
        def scale_sum(n):
            return -4*mp.sinh(n*L/2)*mp.sinh(n*M/2)
        small=[(n,(-1)**(n+1)*mp.zeta(n+1,a)*scale_sum(n)) for n in range(1,args.small_order+1)]
        large=[(n,(-1)**(n+1)*mp.bernpoly(n,a)*scale_sum(n)/n) for n in range(1,args.tail_order+1)]
        N=moments(fn,a,min(betas),max(betas),small,large,3)
        label=f'a={tag}, scales={scale_pair}'
        cases.append({'name':label,'moments':[mp.nstr(v,args.precision+4) for v in N]})
        check(label+' constant anchor',N[0],-p)
        reconstructed=[N[1]/p,N[2]/(2*p)+A,N[3]/(3*p)-2*A*N[1]/p]
        for n,(lhs,rhs) in enumerate(zip(reconstructed,gammas(a))):
            check(label+f' gamma{n}',lhs,rhs)

# Colored endpoint at omega=-1,a=1, with the positive logarithm L=log2.
L=mp.log(2)
def alt(x):
    return (mp.digamma((x+2)/2)-mp.digamma((x+1)/2))/2
def eta(s):
    return mp.log(2) if s==1 else (1-mp.power(2,1-s))*mp.zeta(s)
def tail_A(k):
    return mp.power(2,k)*(mp.bernpoly(k+1,1)-mp.bernpoly(k+1,mp.mpf('.5')))/(k+1)
b=mp.sqrt(2)
small=[(n,(-1)**n*eta(n+1)*2*mp.sinh(n*L/2)) for n in range(1,args.small_order+1)]
large=[(n,(-1)**n*tail_A(n-1)*2*mp.sinh(n*L/2)) for n in range(1,args.tail_order+1)]
T=moments(lambda x:alt(b*x)-alt(x/b),mp.mpf(1),1/b,b,small,large,2)
cases.append({'name':'alternating centered endpoint','moments':[mp.nstr(v,args.precision+4) for v in T]})
expected=[-L**2,L**2*mp.euler-L**3/2,
          2*L**2*mp.stieltjes(1)+L**3*mp.euler-mp.pi**2*L**2/3-5*L**4/12]
for j,(lhs,rhs) in enumerate(zip(T,expected)):
    check(f'alternating centered log degree{j}',lhs,rhs)

# A repeated root at a positive integer moment, distinct from the endpoint.
# D(s)=(1-2^-s)^2, H=alt(x)-alt(x/2)+alt(x/4)/4.
small=[(n,(-1)**n*eta(n+1)*(1-mp.power(2,-n)+mp.power(2,-2*n-2)))
       for n in range(args.small_order+1)]
large=[(n,(-1)**(n-1)*tail_A(n-1)*(1-mp.power(2,n-1))**2)
       for n in range(1,args.tail_order+1)]
T=moments(lambda x:alt(x)-alt(x/2)+alt(x/4)/4,mp.mpf(1),mp.mpf('.25'),mp.mpf(1),small,large,1,u0=1)
cases.append({'name':'alternating double-root positive moment','moments':[mp.nstr(v,args.precision+4) for v in T]})
check('alternating double-root ordinary moment',T[0],mp.mpf(0))
check('alternating double-root first log moment',T[1],-L**2/2)
result=save('PASS')
print('PASS',result['count'],'comparisons; max error',result['max_abs_error'],flush=True)
