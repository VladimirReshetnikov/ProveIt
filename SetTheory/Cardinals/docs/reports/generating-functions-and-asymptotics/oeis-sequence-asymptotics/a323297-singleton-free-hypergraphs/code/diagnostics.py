#!/usr/bin/env python3
"""NONCERTIFIED floating diagnostics from exact counts and exact raw moments.

No decimal here is an interval enclosure, asymptotic proof, or onset certificate.
Poisson sums are truncated; their displayed masses are diagnostic, not tail bounds.
"""
from __future__ import annotations
import sys
sys.dont_write_bytecode=True
import argparse
import mpmath as mp
from common import emit, integer, new_file_path, require
from exact_counts import MAX_N, assembly_counts, marked_totals


def cumulants(r,max_order=6,isolates=True,tetrahedra=True):
    integer(max_order,0,12,'maximum cumulant order')
    require(type(isolates) is bool and type(tetrahedra) is bool,'model flags must be booleans')
    require(type(r) in (int,float,mp.mpf),'r must be a finite real numeric value')
    r=mp.mpf(r);require(mp.isfinite(r) and 0<r<=20,'r must be in (0,20]')
    H=r*r*mp.exp(r)/2;poly=[1];values=[]
    for order in range(max_order+1):
        values.append(H*sum(c*r**j for j,c in enumerate(poly))+int(isolates)*r
                      -2**order*r*r/2-3**order*r**3/3+int(tetrahedra)*mp.mpf(5)*4**order*r**4/24)
        nxt=[0]*(len(poly)+1)
        for j,c in enumerate(poly):nxt[j]+=(j+2)*c;nxt[j+1]+=c
        poly=nxt
    return tuple(values)


def saddle(n,precision=60,isolates=True):
    integer(n,32,MAX_N,'n');integer(precision,30,100,'working precision')
    require(type(isolates) is bool,'isolates must be a boolean')
    with mp.workdps(precision):
        lo=mp.mpf('0.0001');hi=mp.log(n+2)+2
        for unused in range(4*precision+32):
            mid=(lo+hi)/2
            if cumulants(mid,1,isolates)[1]<n:lo=mid
            else:hi=mid
        return +(lo+hi)/2


def diagnostics(n=MAX_N,precision=60):
    integer(n,32,MAX_N,'n');integer(precision,30,100,'working precision')
    points=sorted({32,min(80,n),min(160,n),min(320,n),n})
    counts={i:assembly_counts(n,i) for i in (True,False)}
    no_tetra=assembly_counts(n,True,False);ordinary=assembly_counts(n,False,False)
    moments={i:marked_totals(n,i) for i in (True,False)}
    with mp.workdps(precision):
        fmt=lambda value:mp.nstr(value,22,strip_zeros=False)
        phi=mp.exp(-mp.mpf('0.5'))/mp.sqrt(2*mp.pi)
        coefficient_rows=[];marked_rows=[];exceptional_rows=[]
        for size in points:
            for isolates in (True,False):
                r=saddle(size,precision,isolates);C,nn,b,k3,k4,k5,k6=cumulants(r,6,isolates)
                e1=k4/(8*b*b)-5*k3*k3/(24*b**3)
                e2=-k6/(48*b**3)+7*k3*k5/(48*b**4)+35*k4*k4/(384*b**4)-35*k3*k3*k4/(64*b**5)+385*k3**4/(1152*b**6)
                A=counts[isolates][size]
                factor=mp.exp(mp.log(A)-mp.loggamma(size+1)-C+size*mp.log(r)+mp.log(2*mp.pi*b)/2)
                coefficient_rows.append({'n':size,'model':'A323297' if isolates else 'A323296','r':fmt(r),
                    'relative_factor':fmt(factor),'scaled_errors_J0_J1_J2':[fmt((factor-x)/(r/size)**(j+1)) for j,x in enumerate((1,1+e1,1+e1+e2))]})
                a,k,kk,dd,dd2,kd=moments[isolates][size]
                EK=mp.mpf(k)/a;VK=mp.mpf(kk)/a-EK*EK;ED=mp.mpf(dd)/a;VD=mp.mpf(dd2)/a-ED*ED
                covariance=mp.mpf(kd)/a-EK*ED
                d=int(isolates)*r+r**4/4;tau=int(isolates)*r+r**4/3;eta=int(isolates)*r+r**4
                V=C-size*size/b;T=tau-eta*eta/b;G=d-size*eta/b
                mean_predict=d+eta*k3/(2*b*b)-(int(isolates)*r+4*r**4)/(2*b)
                marked_rows.append({'n':size,'model':'A323297' if isolates else 'A323296',
                    'mean_K_minus_C':fmt(EK-C),'variance_K_over_V':fmt(VK/V),
                    'mean_defect_remainder_scaled_n2_r5':fmt((ED-mean_predict)*size*size/r**5),
                    'variance_defect_remainder_scaled_n_r4':fmt((VD-T)*size/r**4),
                    'covariance_K_defect_over_G':fmt(covariance/G),
                    'correlation_K_defect':fmt(covariance/mp.sqrt(VK*VD))})
                if not isolates:continue
                lam=5*r**4/24;mu=r+4*lam;v=r+16*lam
                cutoff=int(mp.ceil(mu+20*mp.sqrt(v)+100))
                require(cutoff<=5000,'Poisson diagnostic cutoff exceeds 5000')
                q=[mp.exp(-r-lam)]
                for w in range(1,cutoff+1):q.append((r*q[w-1]+(4*lam*q[w-4] if w>=4 else 0))/w)
                tv=mp.mpf(0);l1=mp.mpf(0);conditioned_mass=mp.mpf(0);falling_r=mp.mpf(1)
                for w,qw in enumerate(q):
                    h=mp.exp(r+lam)*falling_r*ordinary[size-w]/A if w<=size else mp.mpf(0)
                    delta=w-mu;approx=1+(v-delta*delta)/(2*b)+k3*delta/(2*b*b)
                    tv+=qw*abs(h-1)/2;l1+=qw*abs(h-approx);conditioned_mass+=qw*h
                    if w<size:falling_r*=mp.mpf(size-w)/r
                del_tetra=-lam-25*r**8/(72*b)+5*r**4/(3*b)-5*r**4*k3/(12*b*b)
                del_iso=-r+(r-r*r)/(2*b)-r*k3/(2*b*b)
                exceptional_rows.append({'n':size,'poisson_cutoff_W':cutoff,
                    'truncated_Q_mass':fmt(sum(q)),'truncated_conditioned_mass':fmt(conditioned_mass),
                    'truncated_TV':fmt(tv),'TV_over_phi1_v_b':fmt(tv/(phi*v/b)),
                    'TV_over_leading_r3_n':fmt(tv/((mp.mpf(10)/3)*phi*r**3/size)),
                    'likelihood_L1_remainder_scaled_n2_r6':fmt(l1*size*size/r**6),
                    'log_no_tetrahedra_error_scaled_n2_r11':fmt((mp.log(no_tetra[size])-mp.log(A)-del_tetra)*size*size/r**11),
                    'log_no_isolates_error_scaled_n2_r2':fmt((mp.log(counts[False][size])-mp.log(A)-del_iso)*size*size/r**2)})
        return {'status':'NONCERTIFIED','working_decimal_digits':precision,'max_n':n,
            'coefficient_diagnostics':coefficient_rows,'marked_moment_diagnostics':marked_rows,
            'exceptional_likelihood_and_deletion_diagnostics':exceptional_rows,
            'scope':'Exact input counts; floating roots, ratios, cumulants and truncated Poisson sums. No intervals, certified tail bounds, error constants, effective onset, inverse integer thresholds, or proof of asymptotics.'}


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--n',type=int,default=MAX_N)
    parser.add_argument('--precision',type=int,default=60);parser.add_argument('--output');args=parser.parse_args()
    if args.output is not None:new_file_path(args.output)
    emit(diagnostics(args.n,args.precision),args.output)

if __name__=='__main__':
    try:main()
    except (ValueError,RuntimeError,OSError,ArithmeticError) as exc:raise SystemExit(str(exc))
