#!/usr/bin/env python3
"""Optional high-precision diagnostics, never interval or onset certificates.
Uses exact integer counts, and mpmath workdps preserves caller precision.
"""
import argparse
import json
from colored_trees import counts, diagonal, marked_prefix


def run(tv=False):
    try:
        import mpmath as mp
    except ImportError as exc:
        raise RuntimeError('Optional diagnostics require mpmath') from exc
    before=mp.mp.dps
    with mp.workdps(80):
        a=mp.exp(-1)
        text=lambda x:mp.nstr(x,32)
        cross=[]; inverse=[]; tvrows=[]
        for N in (80,160,320,640):
            for num,den in ((1,2),(1,1),(2,1)):
                q=N*num//den;alpha=mp.mpf(q)/N
                all_,ident,zero,B=[counts(N,q,kind)[-1] for kind in ('all','identity','zero','B')]
                ratio=mp.mpf(ident)/all_
                leading=mp.exp(-a*a/alpha)
                first=leading*(1-(a*a/alpha+a**4/alpha**2)/N)
                gap=mp.mpf(zero-ident)/all_;defect=mp.mpf(all_-B)/all_
                cross.append({'N':N,'q':q,'p':text(ratio),'N2_first_relative_residual':text(N*N*(ratio/first-1)),
                              'N_gap':text(N*gap),'gap_limit':text(leading*a**4/alpha**2),
                              'N_B_defect':text(N*defect),'B_defect_limit':text((a**3+a**4)/alpha**2)})
        for sig in (1,-1):
            K=mp.exp(1+sig*a*a/2)/mp.sqrt(2*mp.pi)
            ell1=-mp.mpf(19)/12+sig*a*a+a**3/3-(a**4 if sig==-1 else 0)
            ell2=(mp.mpf(5)/6+2*a*a/3+5*a**3/6+a**4/2-5*a**5/6 if sig==1 else
                  mp.mpf(5)/6-2*a*a/3+5*a**3/6-3*a**4+5*a**5/6-3*a**6)
            for n in (40,80,160,320):
                y=mp.log(diagonal(n,'all' if sig==1 else 'identity'))
                L=y-mp.log(K);X=L/mp.lambertw(mp.e*L);h=mp.log(X)+2
                delta=mp.mpf('1.5')*mp.log(X)/h
                explicit=X+delta-(delta*delta/2-mp.mpf('1.5')*delta+ell1)/(X*h)
                logf=lambda x:mp.log(K)+x+(x-mp.mpf('1.5'))*mp.log(x)+ell1/x+ell2/x**2
                smooth=mp.findroot(lambda x:logf(x)-y,(n-mp.mpf('.1'),n+mp.mpf('.1')))
                inverse.append({'kind':'all' if sig==1 else 'identity','n':n,'explicit_minus_n':text(explicit-n),'smooth_minus_n':text(smooth-n)})
        if tv:
            for N in (40,80,160,320):
                for num,den in ((1,2),(1,1),(2,1)):
                    q=N*num//den;alpha=mp.mpf(q)/N;lam=a*a/alpha;K=16
                    prefix,total=marked_prefix(N,q,K)
                    po=[mp.exp(-lam)]
                    for k in range(1,160): po.append(po[-1]*lam/k)
                    H=lambda k:-lam+(1+(2-mp.e)*lam)*k-2*k*(k-1)+mp.e/lam*k*(k-1)*(k-2)
                    correction=[p*H(k) for k,p in enumerate(po)]
                    comparison=[p+c/N for p,c in zip(po,correction)]
                    actual=[mp.mpf(v)/total for v in prefix]
                    actualtail=mp.mpf(total-sum(prefix))/total
                    potail=sum(po[K+1:]);abstail=sum(abs(v) for v in comparison[K+1:])
                    head=sum(abs(v-p) for v,p in zip(actual,po))/2
                    l1head=sum(abs(v-p) for v,p in zip(actual,comparison))
                    C=sum(abs(c) for c in correction)/2
                    low=head+abs(actualtail-potail)/2;high=head+(actualtail+potail)/2
                    tvrows.append({'N':N,'q':q,'C':text(C),'N_TV_bracket':[text(N*low),text(N*high)],
                                   'N2_TV_residual_bracket':[text(N*N*(low-C/N)),text(N*N*(high-C/N))],
                                   'N2_signed_l1_bracket':[text(N*N*(l1head+max(actualtail-abstail,0))),text(N*N*(l1head+actualtail+abstail))],
                                   'actual_tail_above_16':text(actualtail)})
    if mp.mp.dps!=before:
        raise ArithmeticError('global mpmath precision changed')
    return {'scope':'High precision diagnostics only, not rigorous numerical enclosures or effective onsets',
            'precision_digits':80,'mpmath_global_precision':'preserved','crossovers_and_defects':cross,'diagonal_inverses':inverse,
            'TV_note':'Exact marked coefficients through degree 16 and exact omitted probability mass. Numerical brackets use Poisson sums through 159; omitted terms are negligible at this precision, not interval-certified.',
            'TV_diagnostics':tvrows}


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--tv',action='store_true')
    print(json.dumps(run(p.parse_args().tv),indent=2,sort_keys=True))
