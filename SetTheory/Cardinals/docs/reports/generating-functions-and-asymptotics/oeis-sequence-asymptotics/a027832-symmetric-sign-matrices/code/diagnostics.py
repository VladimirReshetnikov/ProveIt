#!/usr/bin/env python3
"""NONCERTIFIED binary-floating diagnostics; no asymptotic remainder bounds."""
from __future__ import annotations
import sys
sys.dont_write_bytecode = True
import argparse
import math
from common import emit, integer, new_file_path, require
from exact_counts import _Counter


def capped_moments(b,r,k):
    integer(b,1,2000,'binomial order')
    integer(k,0,b,'binomial cap')
    require(isinstance(r,(int,float)) and not isinstance(r,bool) and 0<r<1 and math.isfinite(r),
            'binomial parameter must be finite and strictly between zero and one')
    logs=[math.lgamma(b+1)-math.lgamma(d+1)-math.lgamma(b-d+1)+d*math.log(r)+(b-d)*math.log1p(-r)
          for d in range(b+1)]
    mx=max(logs);total=sum(math.exp(z-mx) for z in logs)
    cmx=max(logs[:k+1]);weights=[math.exp(z-cmx) for z in logs[:k+1]]
    cap=sum(weights);q=[w/cap for w in weights]
    mu=sum(d*w for d,w in enumerate(q));var=sum((d-mu)**2*w for d,w in enumerate(q))
    logS=cmx-mx+math.log(cap)-math.log(total)
    return {'logS':logS,'S':math.exp(logS),'mean':mu,'variance':var,'max_atom':max(q)}


def fixed_saddle(M,k):
    integer(M,8,2001,'saddle graph order')
    integer(k,0,M-1,'saddle cap')
    require(k==(M-1)//2,'saddle diagnostic is restricted to k=floor((M-1)/2)')
    def fun(L):
        r=.5-L/(2*math.sqrt(M));p=r*r/(r*r+(1-r)**2)
        moments=capped_moments(M-1,r,k)
        return moments['mean']-(M-1)*p,(r,p,moments)
    lo,hi=0.,1.
    require(fun(lo)[0]<0<fun(hi)[0],'floating saddle not bracketed')
    for _ in range(70):
        mid=(lo+hi)/2
        if fun(mid)[0]>0:hi=mid
        else:lo=mid
    L=(lo+hi)/2;residual,data=fun(L);r,p,moments=data
    require(abs(residual)<1e-9*M,'floating saddle residual check failed')
    return {'M':M,'k':k,'L':L,'r':r,'p':p,'S':moments['S'],'logS':moments['logS'],
            'one_over_S':1/moments['S'],'variance_over_M':moments['variance']/M,
            'mean_shift_over_sqrt_M':((M-1)*r-moments['mean'])/math.sqrt(M),
            'max_atom':moments['max_atom'],'residual':residual}


def diagnostics(max_M=1001):
    integer(max_M,21,2001,'largest saddle graph order')
    ell=.5060544689891807632361983064420960067
    Phi=.5*(1+math.erf(ell/math.sqrt(2)))
    q=Phi*math.exp(-ell*ell/2)
    Z0=math.exp(5*ell*ell/4-ell**4/2)/math.sqrt(1+2*ell*ell)
    J=-4*ell*ell/(1+2*ell*ell)
    counter=_Counter();leading=[];critical=[]
    for n in range(1,18):
        M=n+1;k=n//2
        U=counter.count(tuple([k]*n+[n]));B=counter.count(tuple([k]*M))
        log_model=math.comb(M,2)*math.log(2)+n*math.log(q)+math.log(Z0)-ell*ell/2
        if n%2==0:log_model+=ell*math.sqrt(n)+J/4
        leading.append({'n':n,'exact_over_leading_model':math.exp(math.log(U)-log_model),
                        'one_free_over_all_capped':U/B,'transfer_ratio_times_Phi':U*Phi/B})
        if M>=8:
            saddle=fixed_saddle(M,k)
            theta=k-M/2+1
            for f in sorted({1,math.isqrt(M),min(M,2*math.isqrt(M))}):
                mixed=counter.count(tuple([k]*(M-f)+[M-1]*f))
                logratio=math.log(mixed)-math.log(B)
                correction=ell*ell*f*f/(2*(1+2*ell*ell)*M)
                log_implicit=-f*saddle['logS']+correction
                log_explicit=-f*math.log(Phi)-2*theta*ell*f/((1+2*ell*ell)*math.sqrt(M))+correction
                critical.append({'M':M,'k':k,'f':f,'f_over_sqrt_M':f/math.sqrt(M),
                                 'exact_over_S_based_model':math.exp(logratio-log_implicit),
                                 'exact_over_explicit_Phi_model':math.exp(logratio-log_explicit)})
    orders=sorted({M for M in (20,21,50,51,100,101,500,501,1000,1001,max_M-1,max_M) if M<=max_M})
    saddles=[fixed_saddle(M,(M-1)//2) for M in orders]
    return {'status':'NONCERTIFIED_FLOATING_DIAGNOSTICS','arithmetic':'Python binary64 float and platform libm',
            'leading_model_rows':leading,'critical_window_rows':critical,'saddle_rows':saddles,
            'scope':'Numerical illustrations only. Neither floating saddle residuals nor small-order ratios certify the critical-window theorem, its error, onset, an inverse threshold, or all-order expansions.'}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-M',type=int,default=1001)
    parser.add_argument('--output')
    args=parser.parse_args()
    integer(args.max_M,21,2001,'largest saddle graph order')
    if args.output is not None:new_file_path(args.output)
    emit(diagnostics(args.max_M),args.output)


if __name__=='__main__':
    try:main()
    except (ValueError,RuntimeError,OSError,ArithmeticError) as exc:raise SystemExit(str(exc))
