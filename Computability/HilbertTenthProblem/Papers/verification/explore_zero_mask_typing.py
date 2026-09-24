#!/usr/bin/env python3
"""Exact scope check for typing zero events through their convolution mask."""
from pathlib import Path
import json


def boolean(n):
    if n<0:return False
    while n:
        n,d=divmod(n,3)
        if d==2:return False
    return True


def head_subset(n,R,u):
    for _ in range(u):
        n,d=divmod(n,R)
        if d not in (0,1):return False
    return n==0


def instance(m,u,Z):
    R=3**m;q=R**u;H=(q-1)//(R-1);J=(q-1)//2
    top=R//3*H;rep=(R-3)//6;T=top+rep*Z
    return dict(m=m,u=u,R=R,q=q,H=H,J=J,top=top,rep=rep,Z=Z,T=T,
                Zplus=Z+1,FT=J+T)


def verify():
    boolean_cases=nonnegative_cases=false_stronger=false_boolean=0;samples=[];boolean_samples=[]
    for m in range(2,5):
        for u in range(1,4):
            R=3**m;q=R**u;H=(q-1)//(R-1);J=(q-1)//2
            for bits in range(1<<(m*u)):
                Z=sum(((bits>>i)&1)*3**i for i in range(m*u))
                z=instance(m,u,Z);accept=boolean(z['T']) and z['T']<q
                if head_subset(Z,R,u):assert accept
                if m==2:assert accept==head_subset(Z,R,u)
                if accept:
                    assert 0<z['T']<=J
                    if not head_subset(Z,R,u):
                        false_boolean+=1
                        if len(boolean_samples)<8:boolean_samples.append(z)
                boolean_cases+=1
            for Z in range(H+1):
                z=instance(m,u,Z)
                if boolean(z['T']) and z['T']<=J and not head_subset(Z,R,u):
                    false_stronger+=1
                    if len(samples)<8:samples.append(z)
                nonnegative_cases+=1
    witness=instance(3,2,18)
    assert witness==dict(m=3,u=2,R=27,q=729,H=28,J=364,top=252,rep=4,Z=18,T=324,Zplus=19,FT=688)
    assert boolean(witness['T']) and not boolean(witness['Z'])
    assert 0<witness['T']<=witness['J'] and 0<=witness['Z']<=witness['H']
    assert not head_subset(witness['Z'],27,2)
    assert all(d in '12' for d in ternary(witness['FT']))
    family=[]
    for u in range(3,13):
        z=instance(3,u,120)
        assert z['T']==3+27**2+9*sum(27**j for j in range(2,u))
        assert boolean(z['Z']) and boolean(z['T']) and z['Z']<=z['H'] and z['T']<=z['J']
        assert not head_subset(z['Z'],27,u)
        assert all(d in '12' for d in ternary(z['FT']))
        assert all(d in '12' for d in ternary(z['J']+z['Z']))
        if u%2==0:assert all(z[name]%2==0 for name in ('H','J','Z','T'))
        family.append(z)
    general_cases=0;general_samples=[]
    for m in range(3,33):
        for u in sorted({m,m+1,6*((m+5)//6)}):
            Z=4*3**(m-2)*sum(3**(n*(m-1)) for n in range(m-1))
            z=instance(m,u,Z);D=m*(m-1)-1
            assert z['rep']*Z==2*3**D-2*3**(m-2)
            normalized=3**(m-2)+3**(m*(m-1))+sum(3**(m*j+m-1) for j in range(1,u) if j!=m-2)
            assert z['T']==normalized
            assert boolean(Z) and boolean(z['T']) and 0<Z<z['H'] and z['T']<=z['J']
            assert not head_subset(Z,z['R'],u)
            assert ternary(Z).count('1')==2*(m-1) and ternary(z['T']).count('1')==u
            if u%2==0:assert all(z[name]%2==0 for name in ('H','J','Z','T'))
            if m in (3,4,8,16) and u%6==0:general_samples.append(z)
            general_cases+=1
    return dict(status='PASS_BOOLEAN_AND_NONNEGATIVE_ZERO_TYPING_COUNTEREXAMPLES',
                boolean_Z_cases=boolean_cases,nonnegative_Z_with_scalar_bound_cases=nonnegative_cases,
                counterexamples_with_Boolean_Z=false_boolean,Boolean_counterexample_samples=boolean_samples,
                counterexamples_to_stronger_statement=false_stronger,exact_witness=witness,samples=samples,
                exact_Boolean_counterfamily=family,
                arbitrary_width_closed_formula_cases=general_cases,arbitrary_width_samples=general_samples,
                proof='../1980/EXPLORATION_ZERO_MASK_TYPING.md',
                scope='Standalone convolution typing only. Both Boolean-Z and nonnegative-Z reverse implications are false in variable widths; no full modified controller counterexample or new operation bound is claimed.')


def ternary(n):
    digits=[]
    while n:n,d=divmod(n,3);digits.append(str(d))
    return ''.join(reversed(digits)) or '0'


if __name__=='__main__':
    result=verify();Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status'])
    print({k:v for k,v in result.items() if k.endswith('_cases') or k=='counterexamples_to_stronger_statement'})
    print(result['exact_witness'])
