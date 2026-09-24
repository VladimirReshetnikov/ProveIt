#!/usr/bin/env python3
"""Scoped carry boundary for combining complemented guards and zero fusion."""
from pathlib import Path
import json


def boolean(n):
    if n<0:return False
    while n:
        n,d=divmod(n,3)
        if d>1:return False
    return True


def paid_counter_alias(x):
    R=27;W=R**3
    path=[0,1,2,3,4,5]+[3,1,2,3,4,5]*x+[0]
    u=len(path)-1;q=R**u;J=(q-1)//2;H=(q-1)//(R-1);g=(R-3)//6
    values=[2*x,0,0];A0=A1=Kp=Km=Z0=0
    for b,state in enumerate(path[:-1]):
        lane=b%3;assert state%3==lane
        n=values[lane];assert 0<=n<R//3
        if state==1:assert n==0;Z0+=R**b
        a0=a1=0;v=n;weight=1
        while v:
            v,d=divmod(v,3)
            if d==2:a0+=weight;a1+=weight
            elif d==1:
                if b%2:a1+=weight
                else:a0+=weight
            weight*=3
        assert a0+a1==n and boolean(a0) and boolean(a1)
        A0+=a0*R**b;A1+=a1*R**b
        step=1 if state<3 else -1
        if step==1:Kp+=R**b
        else:Km+=R**b
        values[lane]+=step;assert min(values)>=0
    assert values==[0,0,0] and min(A0,A1,Kp,Km,Z0)>0
    D0=H-Z0;D=H+q*Z0;gap=g*D;Z=H-D
    fields=[Kp,gap-A0,A0,gap-A1,A1,Km,Z,D]
    low=sum(value*q**i for i,value in enumerate(fields))
    expected=[Kp,g*H-A0,A0+g*Z0,g*H-A1,A1+g*Z0,Km,0,D0]
    chunks=[low//q**i%q for i in range(8)]
    assert chunks==expected and all(boolean(v) and 0<=v<q for v in chunks)
    assert low//q**8==Z0 and Z<0 and D>q
    assert Kp+Km==H and 6*gap==(R-3)*D
    assert W*(A0+A1+Kp-Km)==A0+A1-2*x and 0<2*x<R
    assert (W-1)*(A0+A1)<W*H
    assert low==Kp+q*((q-1)*(A0+q*q*A1)+(q*q+1)*gap)+q**5*Km+q**6*(H+(q-1)*D)
    assert 0<low<q**9 and 2*low<q**12-1
    return dict(x=x,R=R,u=u,q=q,H=H,A0=A0,A1=A1,Kp=Kp,Km=Km,
                honest_zero_word=Z0,raw_D=D,raw_gap=gap,raw_zero_word=Z,
                normalized_eight=chunks,carry_into_program=Z0,
                exact_time_holds=True,paid_input_bound_holds=True,
                preliminary_packed_lower_bound_holds=True,
                scope='A full raw counter history and all eight counter masks, with paid input and gap/sign sources. The four program fields and routing equation are deliberately not asserted.')


def verify():
    pairs=negative=weakpasses=0
    for q in range(9,500,2):
        J=(q-1)//2
        for H in sorted({1,max(1,J//8),max(1,J//4)}):
            for D in range(1,q):
                pair=H+(q-1)*D
                high,low=divmod(pair,q)
                if D>H:
                    assert low==q+H-D and high==D-1
                    assert low>J or high>J
                    negative+=1
                if low<=J and high<=J:
                    assert D<=H and low==H-D and high==D
                    weakpasses+=1
                pairs+=1
    guard_cases=0
    for R,u in ((9,3),(9,4),(27,3)):
        q=R**u;J=(q-1)//2;H=(q-1)//(R-1);W=R**3;g=(R-3)//6
        Abound=(W*H-1)//(W-1)
        assert Abound+g<q
        for D in range(1,q):
            gap=g*D;t0=gap%q;k=gap//q
            assert k<g
            for A in sorted({1,max(1,Abound//2),Abound}):
                low=(gap-A)%q;carry=(gap-A)//q
                if t0<A:assert low>J
                else:
                    assert carry==k and A+carry<q
                guard_cases+=1
    # A real local high-D carry alias survives all eight counter masks.
    # It fails the mandatory input bound, so it is not a full counterexample.
    R=9;u=4;q=R**u;J=(q-1)//2;H=(q-1)//(R-1);W=R**3
    D=q+H;gap=D;A0=A1=R;Kp=1;Km=H-1;A=A0+A1
    low=Kp+q*((q-1)*(A0+q*q*A1)+(q*q+1)*gap)+q**5*Km+q**6*(H+(q-1)*D)
    chunks=[low//q**i%q for i in range(8)]
    assert chunks==[1,H-R,R+1,H-R,R+1,H-1,0,H-1]
    assert all(boolean(v) for v in chunks) and low//q**8==1
    assert Kp+Km==H and 6*gap==(R-3)*D
    numerator=A-W*(A+Kp-Km);assert numerator%2==0
    x=numerator//2;assert x>0 and W*(A+Kp-Km)==A-2*x and 2*x>=R
    return dict(status='PASS_SCOPED_COMPLEMENTED_GUARD_ZERO_BOUND',
                pair_range_cases=pairs,negative_zero_cases_rejected=negative,
                weak_digit_cap_pairs=weakpasses,conditional_guard_cases=guard_cases,
                local_high_D_alias=dict(R=R,u=u,q=q,H=H,D=D,gap=gap,A0=A0,A1=A1,
                    Kp=Kp,Km=Km,x=x,zero_word=H-D,normalized_low_eight=chunks,
                    carry_into_program=1,input_bound_fails=True),
                paid_counter_aliases=[paid_counter_alias(x) for x in (1,2)],
                proof='../1980/EXPLORATION_COMPLEMENTED_GUARD_ZERO_BOUND.md',
                scope='Conditional D<q sufficiency, a local high-D alias, and a general honest-counter alias preserving the paid input. The actual103 combination with its full program constraints remains open; no operation reduction is certified.')


if __name__=='__main__':
    result=verify();Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
    print(result['status']);print({k:v for k,v in result.items() if k not in ('proof','scope')})
