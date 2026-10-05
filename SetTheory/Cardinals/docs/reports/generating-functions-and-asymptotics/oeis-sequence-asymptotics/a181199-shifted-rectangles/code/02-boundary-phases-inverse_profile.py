"""Invert a truncated rare-count profile; not an integer-threshold certificate.

The target is an exact R_m(n), so the output illustrates how closely the
continuous profile recovers the input index. It does not certify ceil(root).
"""
from __future__ import annotations
import argparse, json
from math import factorial, prod
from pathlib import Path
import mpmath as mp
from tableaux import count
ROOT=Path(__file__).resolve().parents[1]

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--index',type=int,default=60)
    ap.add_argument('--height',type=int,default=5,choices=(3,4,5))
    ap.add_argument('--digits',type=int,default=70)
    args=ap.parse_args()
    if args.index<10 or args.digits<30:
        ap.error('Use index>=10 and digits>=30 for these asymptotic diagnostics')
    mp.mp.dps=args.digits;m=args.height;n=args.index;r=m-2
    b=[mp.mpf(s.split('/')[0])/mp.mpf(s.split('/')[1]) if '/' in s else mp.mpf(s)
       for s in json.loads((ROOT/f'data/coefficients_m{m}.json').read_text())['b']]
    K=mp.sqrt(mp.mpf(m)/2)*(2*mp.pi)**(-mp.mpf(r)/2)*4**(-mp.mpf(r*(r-1))/2)*9**(-mp.mpf(r))*prod(factorial(j) for j in range(r))
    lam=m*mp.log(m)-mp.log(4);beta=mp.mpf(r*r)/2
    target=count(m,n,True); a=mp.log(mp.mpf(target)/K)
    argument=-lam/beta*mp.exp(-a/beta)
    if argument < -1/mp.e:
        raise ValueError('Target is below the minimum of the leading continuous profile')
    x0=-beta/lam*mp.lambertw(argument,-1).real
    x2=x0-b[1]/(lam*x0)-((b[2]-b[1]**2/2)/lam+beta*b[1]/lam**2)/x0**2
    def logprofile(x):
        correction=sum(b[j]/x**j for j in range(len(b)))
        if correction<=0: raise ValueError('Truncated profile is not positive here')
        return mp.log(K)+lam*x-beta*mp.log(x)+mp.log(correction)
    root=mp.findroot(lambda x:logprofile(x)-mp.log(target),(x0,x2))
    result={'height':m,'input_index':n,'target_R':str(target),
            'lambert_core':mp.nstr(x0,35),'inverse_two_corrections':mp.nstr(x2,35),
            'cubic_profile_inverse':mp.nstr(root,35),
            'profile_index_error':mp.nstr(root-n,35),
            'log_residual':mp.nstr(logprofile(root)-mp.log(target),10),
            'status':'Numerical profile inversion only; not a certified inverse of the integer sequence.'}
    text=json.dumps(result,indent=2)+'\n';print(text,end='')
    (ROOT/f'data/inverse_m{m}_n{n}.json').write_text(text)
if __name__=='__main__':main()
