#!/usr/bin/env python3
"""Necessary index parity from the two signed half-parameter congruences."""
from pathlib import Path
from math import gcd
import hashlib
import json
import sys

OUT=Path(__file__).with_suffix('.json')
ROOT=Path(__file__).resolve().parents[2]


def pell(A,n):
    D=A*A-1;pair=(1,0);power=(A,1)
    while n:
        if n&1:
            x,y=pair;u,v=power;pair=(x*u+D*y*v,x*v+y*u)
        n//=2
        if n:
            x,y=power;power=(x*x+D*y*y,2*x*y)
    return pair


def q_mod(T,h,modulus):
    """Q_0=1,Q_1=4T-3,Q_(h+2)=(4T-2)Q_(h+1)-Q_h."""
    if h==0:return 1%modulus
    def mul(a,b):
        return tuple(sum(a[2*i+k]*b[2*k+j] for k in range(2))%modulus
                     for i in range(2) for j in range(2))
    matrix=((4*T-2)%modulus,(-1)%modulus,1,0)
    result=(1,0,0,1);power=h-1
    while power:
        if power&1:result=mul(result,matrix)
        power//=2
        if power:matrix=mul(matrix,matrix)
    return (result[0]*(4*T-3)+result[1])%modulus


def verify_polynomials_and_stepdown():
    identities=cases=0
    for A in range(2,10):
        for h in range(15):
            s=2*h+1
            for modulus in range(2,31):
                assert q_mod(1-A*A,h,modulus)==((-1)**h*pell(A,s)[1])%modulus
                assert q_mod(0,h,modulus)==((-1)**h*s)%modulus
                identities+=2
        for m in range(1,31):
            chi=[1,A]
            for _ in range(8*m-1):chi.append(2*A*chi[-1]-chi[-2])
            f=chi[m]
            for k in range(1,m+1):
                for n in range(8*m+1):
                    assert (chi[n]-chi[k])%f==0 if n%(4*m) in (k,4*m-k) else (chi[n]-chi[k])%f!=0
                    cases+=1
    return dict(polynomial_congruence_checks=identities,strong_stepdown_cases=cases,
                comparison_boundary_k_equals_m_included=True,all_m_parities_included=True)


def verify_modular_skeleton():
    records=[];sign_cases=minus=plus=noncanonical=0
    parameters=[(A,3) for A in range(2,6)]+[(2,5),(3,5),(2,7)]
    for A,p in parameters:
        d,c=pell(A,p);Delta=A*A-1;r=(p-1)//2
        assert c>2*p
        for multiplier in (1,2,3):
            m=multiplier*c*p;f,psim=pell(A,m);R=Delta*psim
            assert m%c==0 and m%p==0 and m>=2*p and f>2*c
            assert R%(c*c)==0 and R*R==Delta*(f*f-1)
            local_minus=local_plus=0;epsilons=set();tparities=set()
            for epsilon in (1,-1):
                for t in range(4):
                    s=epsilon*p+2*m*t
                    if s<=0:continue
                    h=(s-1)//2
                    uc=q_mod(R*R,h,c);uf=q_mod(R*R,h,f)
                    expect_c=(-1)**(r+m*t)*p%c
                    expect_f=(-1)**(r+(m+1)*t)*c%f
                    assert uc==expect_c and uf==expect_f
                    minus_ok=(uc+p)%c==0 and (uf+c)%f==0
                    plus_ok=(uc-p)%c==0 and (uf-c)%f==0
                    assert minus_ok==(r%2==1 and t%2==0)
                    assert plus_ok==(r%2==0 and t%2==0)
                    if minus_ok:assert p%4==3;minus+=1;local_minus+=1
                    if plus_ok:assert p%4==1;plus+=1;local_plus+=1
                    epsilons.add(epsilon);tparities.add(t%2);sign_cases+=1
                    noncanonical+=int(multiplier!=2 or s!=p)
            assert epsilons=={-1,1} and tparities=={0,1}
            records.append(dict(A=A,p=p,r=r,c=c,m=m,multiplier=multiplier,
                                f_bits=f.bit_length(),R_bits=R.bit_length(),
                                minus_compatible=local_minus,plus_compatible=local_plus))
    assert minus and plus
    return dict(cases=sign_cases,noncanonical_auxiliary_choices=noncanonical,
                minus_compatible=minus,plus_compatible=plus,
                both_epsilon_cases=True,both_t_parities=True,
                actual_norm_parameter_and_c_squared_divisibility_checked=True,examples=records)


def verify_materialized_auxiliaries():
    records=[]
    for A,p,multiplier,epsilon,t in ((2,3,1,1,0),(2,3,1,-1,2),(2,3,1,1,2),
                                    (2,3,2,-1,2),(2,5,1,1,0)):
        d,c=pell(A,p);Delta=A*A-1;m=multiplier*c*p
        f,psim=pell(A,m);R=Delta*psim;s=epsilon*p+2*m*t
        chi,y=pell(R,s);U,rem=divmod(chi,R);assert rem==0
        assert U>c>p and R%(c*c)==0
        assert R*R*(U*U-y*y)==1-y*y
        sigma=(-1)**((p-1)//2)
        j,rem=divmod(U-sigma*p,c);assert rem==0
        o,rem=divmod(U-sigma*c,f);assert rem==0
        assert min(j,o,y)>0 and U==j*c+sigma*p==o*f+sigma*c
        if sigma==1:assert (U+p)%c or (U+c)%f
        records.append(dict(A=A,p=p,m=m,s=s,epsilon=epsilon,t=t,
                            sign=sigma,U_bits=U.bit_length(),positive_exact_quotients=True))
    return records


def verify():
    paths=['Papers/1980/EXPLORATION_ODD_INDEX_PELL_SIGNS.md',
           'Papers/1980/HALF_PARAMETER_PELL_92_PROOF.md',
           'Papers/1980/PELL_RELAXED_AUXILIARY_PROOF.md',
           'Papers/1980/PELL_SIGNED_PROOF.md',
           'Papers/1980/FIXED_RAW_UNIVERSAL_78_PROOF.md']
    return dict(status='PASS_FIXED_MINUS_INDEX_PARITY_NECESSITY',
                identities_and_stepdown=verify_polynomials_and_stepdown(),
                modular_skeleton=verify_modular_skeleton(),
                materialized_auxiliaries=verify_materialized_auxiliaries(),
                necessity={'minus':'p=3 modulo4; r odd','plus':'p=1 modulo4; r even'},
                all_positive_kernel_solutions=True,requires_canonical_auxiliary_choice=False,
                changed_certificate_operations=0,smaller_complete_certificate=False,
                full_packed_kernel_tuples_materialized=False,proof_assistant_verified=False,
                dependency_sha256={p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in paths},
                proof='../1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md')


if __name__=='__main__':
    result=json.loads(json.dumps(verify()))
    if sys.argv[1:]==['--write']:
        OUT.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
    else:
        assert not sys.argv[1:]
        assert result==json.loads(OUT.read_text(encoding='utf-8'))
    print(result['status'],result['modular_skeleton']['cases'],'exact modular skeleton cases')
