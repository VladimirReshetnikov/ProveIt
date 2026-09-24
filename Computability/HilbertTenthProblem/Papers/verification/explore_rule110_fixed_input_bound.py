#!/usr/bin/env python3
"""Finite corroboration of round39's decidable fixed-input characterization."""
from pathlib import Path
import json

import round39_1980_boolean_history_components as source


def rule(a,b,c):
    return (110 >> (4*a+2*b+c)) & 1


def evolve(state):
    return {i for i in range(min(state)-1,max(state)+1)
            if rule(int(i-1 in state),int(i in state),int(i+1 in state))}


def encode(state):
    assert state and min(state) >= 0
    return sum(4**i for i in state)


def valuation4(value):
    assert value > 0
    result=0
    while value % 4 == 0:
        value//=4
        result+=1
    return result


def pack_rows(rows,width):
    return sum(4**(j*width+i) for j,row in enumerate(rows) for i in row)


def auxiliary(rows,width):
    D=X=E=Z=0
    for j,row in enumerate(rows):
        for i in range(width):
            a,b,c=(int(i+d in row) for d in (-1,0,1))
            power=4**(j*width+i)
            D+=(b*c)*power
            X+=(b^c)*power
            E+=(a*b*c)*power
            Z+=(a^(b*c))*power
    return D,X,E,Z


def verify_outer(I,F,rows,final):
    height=len(rows)
    width=max(rows[0])+2
    W=4**width
    Q=W**height
    B=pack_rows(rows,width)
    Y=pack_rows(rows[1:]+[final],width)
    D,X,E,Z=auxiliary(rows,width)
    assert min(B,Y,D,X,E,Z) > 0
    hrow=(Q-1)//(W-1)
    fields=(B,D,X,E,Z,B+hrow)
    P=sum(field*Q**i for i,field in enumerate(fields))
    L=Q**8
    lam=(L-1)//3
    r=(L-P)*(L-1)+2*lam
    inputs=dict(I=I,F=F,q=2**(width*height),v=2**width,
                quot=2**(width*(height-1)),hrow=hrow,Bw=B,Cw=B//4,
                Yw=Y,Dw=D,Xw=X,Ew=E,Zw=Z,
                alpha=Q-(4*B+B+B//4),alphaI=W-I,lam=lam,r=r)
    assert min(inputs.values()) > 0
    env=dict(inputs)
    for name,op,left,right in source.OUTER:
        a=env[left] if isinstance(left,str) else left
        b=env[right] if isinstance(right,str) else right
        env[name]=a+b if op=='+' else a-b if op=='-' else a*b
    assert all(env[left] == env[right] for left,right in source.OUTER_EQUALITIES)
    n0=Q**6
    assert 0 < P < n0 and n0 < r < n0**3 and r%2 == 0
    threshold=(Q**12).bit_length()-1
    assert r.bit_count() == threshold
    assert env['n2'] == Q**12
    return len(source.OUTER_EQUALITIES)


def verify():
    words=front_steps=prefixes=positive=outer_tests=unique=0
    for word in range(1,2**11):
        initial={i for i in range(word.bit_length()) if (word>>i)&1}
        I=encode(initial)
        ell,k=min(initial),max(initial)
        assert ell == valuation4(I)
        state=set(initial)
        for j in range(ell+2):
            assert min(state) == ell-j and max(state) == k
            if j < ell:
                assert 0 not in state
            elif j == ell:
                assert 0 in state
            state=evolve(state)
            front_steps+=1
        state=set(initial)
        rows=[]
        seen_triple=False
        for t in range(1,ell+1):
            rows.append(set(state))
            seen_triple |= any({i-1,i,i+1} <= state for i in state)
            state=evolve(state)
            F=encode(state)
            assert t == valuation4(I)-valuation4(F)
            unique+=1
            D,X,E,Z=auxiliary(rows,k+2)
            assert (min(D,X,E,Z)>0) == seen_triple
            assert X>0 and Z>0
            prefixes+=1
            if seen_triple:
                outer_tests+=verify_outer(I,F,rows,state)
                positive+=1
        words+=1
    return dict(status='FINITE_CHARACTERIZATION_CHECKS_PASS',universality_status='DECIDABLE_FIXED_INPUT_RELATION',
                nonempty_input_words=words,maximum_input_digits=11,
                front_steps=front_steps,bounded_history_prefixes=prefixes,
                unique_height_checks=unique,positive_prefixes=positive,
                exact_outer_equalities_checked=outer_tests,
                full_arithmetic_reference='round39_1980_boolean_history_components.py:86 operations,21 source equations',
                scope='Finite front/height/auxiliary checks and all11 outer equations. The general proof supplies the retained Pell witnesses; no complete huge Pell tuple is numerically materialized.')


if __name__=='__main__':
    result=verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result,indent=2))
