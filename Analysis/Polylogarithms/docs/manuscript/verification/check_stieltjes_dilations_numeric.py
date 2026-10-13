"""Independent ordinary quadrature diagnostics for finite dilations.

The scalar kernel comes from the preserved report's Euler--Maclaurin
evaluator, not from the claimed moment formula. Infinite tails are
integrated from their independently generated Bernoulli expansion.
These high-precision diagnostics are not interval certificates.
"""
import sys
sys.dont_write_bytecode=True
import importlib.util
import json
import argparse
import hashlib
import platform
import time
from pathlib import Path
import mpmath as mp

HERE=Path(__file__).resolve()
ROOT=next(p for p in HERE.parents if (p/'.git').exists())
SOURCE=ROOT/'Analysis/Polylogarithms/docs/reports/stieltjes-correlation-calculus/continuations/balanced-stieltjes-moments/code/balanced.py'
def digest(path):
    return hashlib.sha256(path.read_bytes().replace(b'\r\n',b'\n')).hexdigest()

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--precision','--dps',dest='precision',type=int,default=60)
parser.add_argument('--em-n',type=int,default=72)
parser.add_argument('--em-r',type=int,default=52)
parser.add_argument('--tail-order',type=int,default=100)
parser.add_argument('--cutoff',type=int,default=64,
                    help='Integration cutoff divided by the maximum dilation scale')
parser.add_argument('--output',type=Path,default=HERE.with_suffix('.json'))
args=parser.parse_args()
if args.precision<30 or args.em_n<1 or args.em_r<1 or args.tail_order<4 or args.cutoff<9:
    parser.error('Require precision>=30, em-n>=1, em-r>=1, tail-order>=4, cutoff>=9')
started=time.monotonic()
meta={'digest_mode':'lf-normalized','script_sha256':digest(HERE),
      'source_sha256':{SOURCE.relative_to(ROOT).as_posix():digest(SOURCE)},
      'source_note':'The listed preserved scalar evaluator is imported read-only with bytecode writing disabled.',
      'python_version':platform.python_version(),'mpmath_version':mp.__version__,
      'optimization_level':sys.flags.optimize,
      'dps':args.precision,
      'settings':{'EM_n':args.em_n,'EM_r':args.em_r,'tail_order':args.tail_order,
                  'cutoff_per_max_scale':args.cutoff}}
spec=importlib.util.spec_from_file_location('source_balanced_dilation',SOURCE)
if spec is None or spec.loader is None:
    raise RuntimeError(f'Cannot load scalar evaluator from {SOURCE}')
bal=importlib.util.module_from_spec(spec)
spec.loader.exec_module(bal)

mp.mp.dps=args.precision
comparison_tolerance=mp.power(10,16-args.precision)
cancellation_tolerance=mp.power(10,10-args.precision)
meta['comparison_scaled_tolerance']=mp.nstr(comparison_tolerance,8)
meta['cancellation_absolute_tolerance']=mp.nstr(cancellation_tolerance,8)
results=[]

def write_receipt(status):
    receipt={**meta,'status':status,'comparisons':results,'count':len(results),
             'max_abs_error':mp.nstr(max((mp.mpf(r['abs_error']) for r in results),default=mp.mpf(0)),12),
             'elapsed_seconds':round(time.monotonic()-started,3),
             'scope':'Ordinary numerical quadrature plus truncated Euler--Maclaurin tail; not certified intervals.'}
    args.output.write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
    return receipt

write_receipt('running')

def ordinary(q,k,a,terms):
    a=mp.mpf(a)
    terms=[(mp.mpf(c),mp.mpf(h)) for c,h in terms]
    # c is the Dirichlet-polynomial coefficient: kernel weight is c/h.
    cutoff=mp.mpf(args.cutoff)*max(h for c,h in terms)
    kernel=bal.Kernel(q,n=args.em_n,r=args.em_r)
    if q==0:
        scalar=lambda x: mp.log(x)-mp.digamma(x+a)
    else:
        scalar=lambda x: kernel(x,a)
    def f(x):
        return x**k*mp.fsum(c/h*scalar(x/h) for c,h in terms)
    core=mp.quad(lambda t: 4*t**3*f(t**4),[0,1])
    core+=mp.quad(f,[1,8,cutoff])
    tail=mp.mpf(0)
    for power in range(q+1,args.tail_order+1):
        coeff=bal.tail_coefficient(power,q,a)*mp.fsum(c*h**(power-1) for c,h in terms)
        if power<=k+1:
            if not abs(coeff)<cancellation_tolerance:
                write_receipt('FAIL')
                raise RuntimeError(f'Uncancelled divergent tail: q={q}, k={k}, a={a}, power={power}, coefficient={coeff}')
        else:
            tail+=coeff*cutoff**(k+1-power)/(power-k-1)
    return core+tail

def add(name,q,k,a,terms,rhs):
    lhs=ordinary(q,k,a,terms)
    error=abs(lhs-rhs)
    row={'name':name,'q':q,'weight':k,'a':str(a),
         'lhs':mp.nstr(lhs,args.precision+4),'rhs':mp.nstr(rhs,args.precision+4),'abs_error':mp.nstr(error,12)}
    results.append(row)
    print(name,mp.nstr(error,8),flush=True)
    if not error<comparison_tolerance*max(1,abs(rhs)):
        write_receipt('FAIL')
        raise RuntimeError(f'Quadrature comparison failed: {row}')
    write_receipt('running')

U=[(1,1),('-1.5',2),('.5',4)]
V=[(1,1),('-.75',2),('.125',4)]
add('digamma U unweighted',0,0,1,U,-mp.log(2)/4)
add('digamma U first moment',0,1,1,U,-mp.log(2)/12)
add('digamma U zeta3 moment',0,2,1,U,-3*mp.zeta(3)/(4*mp.pi**2))
add('digamma U shifted unweighted',0,0,mp.mpf('1.3'),U,(mp.mpf('.5')-mp.mpf('1.3'))*mp.log(2)/2)
add('digamma U shifted first',0,1,mp.mpf('1.3'),U,-mp.bernpoly(2,mp.mpf('1.3'))*mp.log(2)/2)
add('principal modulus6 zero',0,0,1,[(1,1),(-1,2),(-1,3),(1,6)],mp.mpf(0))
add('index1 V first moment',1,1,1,V,mp.log(2)/24)
add('index1 V vanishing moment',1,2,1,V,mp.mpf(0))
add('index2 one dilation zero',2,2,1,[(1,1),('-.25',2)],mp.mpf(0))
add('index2 one dilation shifted',2,2,mp.mpf('1.3'),[(1,1),('-.25',2)],-mp.bernpoly(3,mp.mpf('1.3'))*mp.log(2)/3)
add('principal modulus2 index2',2,2,1,[(1,1),(-1,2)],3*mp.zeta(3)/(4*mp.pi**2))

receipt=write_receipt('PASS')
print('PASS',len(results),'comparisons; maximum error',receipt['max_abs_error'],flush=True)
