#!/usr/bin/env python3
"""Bounded exact search after deleting the raw-track aggregate slack bound.

No general soundness, equivalence, or improved certificate is claimed.
The unfinished q6561 exploratory sweep is deliberately not in this receipt.
"""
from pathlib import Path
import json
from explore_native_ternary_ripple import central_valuation


def search(registers,max_exponent):
    candidates=positive_splits=geometries=derived_sums=0
    parameter_ranges=[];found=[]
    for ell in range(2,max_exponent+1):
        q=3**ell;J=(q-1)//2;scale=q**6
        for m in range(1,ell//registers+1):
            if ell%m:continue
            R=3**m;W=R**registers;H=(q-1)//(R-1)
            if (2*J+H)%3:continue
            T=(2*J+H)//3;flag_sum=2*J+H
            geometries+=1
            parameter_ranges.append(dict(q_exponent=ell,block_exponent=m,q=q,R=R,W=W,
                                         counter_blocks=ell//m,max_x=(R-1)//2))
            # P's parity is H's, independently of either track splitting.
            # Only even P is used for the fixed-plus positive kernel converse.
            if H%2:continue
            for x in range(1,(R-1)//2+1):
                I=2*x;modulus=(W-1)//2
                assert (flag_sum-I)%2==0
                first=((flag_sum-I)//2)%modulus
                if first==0:first=modulus
                for kp in range(first,flag_sum,modulus):
                    km=flag_sum-kp;delta=kp-km
                    numerator=-W*delta-I
                    assert numerator%(W-1)==0
                    A=numerator//(W-1);S=2*J+A
                    # This is exactly the region excluded by the removed
                    # positive alpha: S+alpha=q+J permits S<=3J.
                    if S<=3*J:continue
                    derived_sums+=1
                    P0=kp+T*(q+q**3)+S*(q**3+q**4)+q**5*km
                    step=q**3+q**4-q-q*q
                    for f0 in range(1,S):
                        f1=S-f0;P=P0-step*f0;positive_splits+=1
                        assert P%2==0
                        if not (27<=P<2*scale and scale<P*P):continue
                        candidates+=1
                        valuation=central_valuation(P)
                        if valuation<6*ell:continue
                        z=dict(x=x,q=q,Jrep=J,R=R,W=W,H=H,T=T,v=q//W,alphaI=R-I,
                               F0=f0,F1=f1,G0=f0+T,G1=f1+T,FKplus=kp,FKminus=km)
                        assert min(z.values())>0
                        assert q==W*z['v'] and H*(R-1)==q-1
                        assert kp+km==2*J+H==3*T
                        assert W*(A+delta)==A-I and I+z['alphaI']==R
                        assert P==sum(z[n]*q**i for i,n in enumerate(
                            ['FKplus','G0','F0','G1','F1','FKminus']))
                        found.append(dict(outer=z,packed=P,scale=scale,valuation=valuation,
                                          aggregate=S,removed_bound_rhs=3*J))
    return dict(registers=registers,q_exponents=[2,max_exponent],
                geometries=geometries,parameter_ranges=parameter_ranges,
                time_derived_bad_bound_sums=derived_sums,positive_track_splits=positive_splits,
                even_indices_in_general_kernel_window=candidates,counterexamples=found)


def verify():
    runs=[search(1,6),search(2,7),search(3,7)]
    assert runs[0]['even_indices_in_general_kernel_window']==1007353
    assert sum(z['even_indices_in_general_kernel_window'] for z in runs[1:])==209589
    found=sum(len(z['counterexamples']) for z in runs)
    return dict(status='BOUNDED_SEARCH_NO_COUNTEREXAMPLE' if not found else 'COUNTEREXAMPLE_FOUND',
                runs=runs,total_indices_tested=sum(z['even_indices_in_general_kernel_window'] for z in runs),
                scope='Finite search only. Assumes canonical power-three q,R,W geometry; examines all positive x with2x<R, complementary flags, exact time-derived aggregates above3J, and positive track splits in the recorded ranges. No native-field or old safe-packing-window filter is imposed. Exact central-binomial valuation is tested only for even r=P with27<=r<2D0,D0<r^2, the sufficient positive fixed-plus kernel interface. Does not establish any universal alpha-bound deletion or exclude odd-index/noncanonical geometry aliases.',
                uncompleted_larger_run='A separate exploratory q6561 sweep was interrupted and supplies no evidence in this receipt.')


if __name__=='__main__':
    result=verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status']);print(result['total_indices_tested'])
    for row in result['runs']:
        print(row['registers'],row['even_indices_in_general_kernel_window'],len(row['counterexamples']))
