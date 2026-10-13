"""Independent ordinary principal-character log-moment diagnostics.

Direct digamma quadrature with a separately generated Bernoulli tail.
Truncation is not an interval enclosure. No identity RHS is used by the
quadrature. Run twice with changed precision, cutoff and tail order.
"""
import argparse
import hashlib
import json
import math
from pathlib import Path
import platform
import sys
import time
import mpmath as mp

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--dps',type=int,default=50)
parser.add_argument('--cutoff',type=int,default=32)
parser.add_argument('--tail-order',type=int,default=90)
parser.add_argument('--output',type=Path,required=True)
args=parser.parse_args()
if args.dps<30 or args.cutoff<16 or args.tail_order<20:
    parser.error('Require dps>=30, cutoff>=16, tail-order>=20')
mp.mp.dps=args.dps
started=time.monotonic()
rows=[]
controls=[]

def save(status):
    result={'status':status,'dps':args.dps,'cutoff_factor':args.cutoff,
            'tail_order':args.tail_order,'records':rows,'controls':controls,
            'maximum_absolute_error':mp.nstr(max([mp.mpf(r['absolute_error']) for r in rows] or [0]),12),
            'python_version':platform.python_version(),'mpmath_version':mp.__version__,
            'optimization_level':sys.flags.optimize,'digest_mode':'lf-normalized',
            'script_sha256':hashlib.sha256(Path(__file__).read_bytes().replace(b'\r\n',b'\n')).hexdigest(),
            'elapsed_seconds':round(time.monotonic()-started,3),
            'scope':'Direct ordinary digamma quadrature plus truncated Bernoulli tail; noninterval diagnostics.'}
    args.output.write_text(json.dumps(result,indent=2)+'\n',encoding='utf8')
    return result

save('running')

def ordinary(primes,j,c):
    terms=[(1,1)]
    for p in primes:
        terms=terms+[(h*p,-mu) for h,mu in terms]
    T=mp.mpf(args.cutoff)*math.prod(primes)
    def kernel(x):
        return mp.fsum(mp.mpf(mu)/h*(mp.log(x/h)-mp.digamma(1+x/h)) for h,mu in terms)
    def f(x):
        return (mp.log(x)-c)**j*kernel(x)
    core=mp.quad(lambda t:4*t**3*f(t**4),[0,1])
    core+=mp.quad(f,[1,8,T])
    tail=mp.mpf(0)
    for n in range(2,args.tail_order+1):
        if n%2:continue
        coeff=mp.bernoulli(n)/n*math.prod(1-p**(n-1) for p in primes)
        integral=T**(1-n)*mp.fsum(math.comb(j,i)*(mp.log(T)-c)**(j-i)*math.factorial(i)/mp.mpf(n-1)**(i+1) for i in range(j+1))
        tail+=coeff*integral
    return core+tail

for primes in [[2],[2,3],[2,3,5]]:
    r=len(primes)
    logs=[mp.log(p) for p in primes]
    A=(-1)**r*mp.fprod(logs)/2
    c=mp.fsum(logs)/2-mp.log(2*mp.pi)
    b2=5*mp.pi**2/24-mp.euler**2/2-mp.stieltjes(1)+mp.fsum(l*l for l in logs)/24
    b3=mp.stieltjes(2)/2+mp.euler*mp.stieltjes(1)+(mp.euler**3-mp.zeta(3))/3
    coefficients={r-1:A*math.factorial(r-1),r:mp.mpf(0),
                  r+1:A*math.factorial(r+1)*b2,r+2:A*math.factorial(r+2)*b3}
    for j in range(r+3):
        rhs=coefficients.get(j,mp.mpf(0))
        lhs=ordinary(primes,j,c)
        error=abs(lhs-rhs)
        passed=bool(error<mp.power(10,12-args.dps)*max(1,abs(rhs)))
        rows.append({'primes':primes,'degree':j,'centering':mp.nstr(c,args.dps),
                     'lhs':mp.nstr(lhs,args.dps+4),'rhs':mp.nstr(rhs,args.dps+4),
                     'absolute_error':mp.nstr(error,12),'passed':passed})
        print(primes,j,mp.nstr(error,8),flush=True)
        save('running' if passed else 'FAIL')
        if not passed:raise RuntimeError('Principal logarithmic quadrature failed')
    # These changes affect a known nonzero first moment or the centered zero.
    controls.append({'primes':primes,'reversed_global_sign_rejected':bool(abs(2*A*math.factorial(r-1))>mp.mpf('.1')),
                     'omitted_center_rejected':bool(abs(r*A*math.factorial(r-1)*c)>mp.mpf('.01'))})
if not all(all(v for k,v in a.items() if k!='primes') for a in controls):
    save('FAIL');raise RuntimeError('Principal logarithmic negative control failed')
result=save('PASS')
print('PASS',len(rows),'ordinary integrals; max',result['maximum_absolute_error'],flush=True)
