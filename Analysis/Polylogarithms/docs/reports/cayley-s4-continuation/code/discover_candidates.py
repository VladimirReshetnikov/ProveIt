#!/usr/bin/env python3
"""Optional numerical discovery replay. NOT a proof or interval algorithm.

Requires mpmath. For rigorous residual enclosures run certified_euler.py.
A returned integer vector is only a candidate, and a failed search is not
an independence certificate. The p=8, 110-digit candidate is known false.
"""
from __future__ import annotations
import argparse,json,time
from pathlib import Path

def values(p:int,dps:int)->dict:
    import mpmath as m
    m.mp.dps=dps
    def beta(s):
        return (m.zeta(s,m.mpf(1)/4)-m.zeta(s,m.mpf(3)/4))/4**s
    cuts=[m.mpf(0),m.mpf(1)/4,m.mpf(1)/2,m.mpf(1)]
    result={f'S{p}':-m.quad(lambda x:(-m.log(x))**(p-1)*m.log1p(x*x)/(1+x*x),cuts)/m.factorial(p-1)}
    for b in range(1,p//2+1):
        a=p+1-b
        if b==1:
            g=-m.quad(lambda x:(-m.log(x))**(a-2)*m.log1p(x*x)*m.atan(x)/x,cuts)/(2*m.factorial(a-2))
        else:
            g=m.im(m.quad(lambda x:(-m.log(x))**(a-1)*m.j*m.polylog(b,m.j*x)/(1-m.j*x),cuts))/m.factorial(a-1)
        result[f'g{a}{b}']=g
    result[f'pi{p+1}']=m.pi**(p+1)
    result[f'beta{p}L']=beta(p)*m.log(2)
    for j in range(1,p//2):
        result[f'beta{2*j}z{p+1-2*j}']=beta(2*j)*m.zeta(p+1-2*j)
    return result

def main():
    import mpmath as m
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--p',type=int,choices=[6,8],default=6)
    ap.add_argument('--dps',type=int,default=110)
    ap.add_argument('--tol',default='1e-95')
    ap.add_argument('--maxcoeff',type=int,default=10**12)
    ap.add_argument('--maxsteps',type=int,default=10000)
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--no-search',action='store_true')
    args=ap.parse_args()
    if args.dps<40:raise SystemExit('At least 40 working decimal digits are required')
    vals=values(args.p,args.dps)
    vec=None if args.no_search else m.pslq(m.matrix(list(vals.values())),
               tol=m.mpf(args.tol),maxcoeff=args.maxcoeff,maxsteps=args.maxsteps)
    out={'status':'exploratory floating-point output; not a proof',
         'parameters':{k:str(v) for k,v in vars(args).items()},
         'mpmath_version':m.__version__,
         'basis':list(vals),'values':{k:m.nstr(v,args.dps) for k,v in vals.items()},
         'candidate':None if vec is None else [int(c) for c in vec]}
    if vec is not None:out['working_precision_residual']=m.nstr(m.fsum(c*v for c,v in zip(vec,vals.values())),30)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(out,indent=2)+'\n')
    print('basis:',out['basis']);print('candidate:',out['candidate'])
    print('Use exact rational enclosures before retaining any candidate.')
if __name__=='__main__':main()
