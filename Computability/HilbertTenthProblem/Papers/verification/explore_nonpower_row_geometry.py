#!/usr/bin/env python3
"""Bounded search only: can the row square-root divisibility be omitted?"""
from itertools import product
from math import isqrt
from pathlib import Path
import json
import sympy as sp
from explore_aligned_boolean_tableaux import pack,digits,bitplane


def split(value):
    lo=hi=0;power=1
    while value:
        digit=value%4
        lo+=(digit%2)*power;hi+=(digit//2)*power
        value//=4;power*=4
    return lo,hi


def check_word(N,v,T):
    Q,W=4**N,v*v;H=(Q-1)//(W-1);B=T-H
    if B<=0 or B%4:return None
    C=B//4;X,D=split(B+C);Z,E=split(4*B+D);Y=X+D-E
    if min(X,D,Z,E,Y)<=0:return None
    # Q/W need not be an integer in this experiment.
    I=(C-W*Y)%Q
    if not 0<I<v:return None
    numerator=I+W*Y-C
    if numerator<=0 or numerator%Q:return None
    F=numerator//Q
    assert all(bitplane(z) for z in (D,X,E,Z,T)) and Y<Q and F<W
    P=D+Q*X+Q**2*E+Q**3*Z+Q**7*T
    L=Q**8;r=(L-P)*(L-1)+2*(L-1)//3
    assert 0<P<L and r.bit_count()==(Q**12).bit_length()-1
    return dict(N=N,v=v,Q=Q,W=W,H=H,B=B,C=C,T=T,D=D,X=X,E=E,Z=Z,
                Y=Y,I=I,F=F,alphaI=v-I,r_even=r%2==0)


def digit_search(N,v):
    """Exact finite automaton; merges states only with identical future data."""
    Q,W=4**N,v*v
    assert (Q-1)%(W-1)==0
    H=(Q-1)//(W-1); hd=digits(H,N)
    assert hd[0]==1
    # Bprev,Bcur,borrow,c_add1,c_add2,c_subY,c_time,positive_flags,B_nonzero.
    states={(0,0,0,0,0,0,I,0,False):(I,1) for I in range(1,v)}
    sizes=[len(states)]
    for pos in range(N):
        following={}
        for (prev,cur,borrow,c1,c2,c3,ct,flags,live),(I,T) in states.items():
            for bit in ((0,1) if pos+1<N else (0,)):
                if pos+1==N:
                    if borrow:continue
                    nxt,nb=0,0
                else:
                    raw=bit-hd[pos+1]-borrow;nxt,nb=raw%4,int(raw<0)
                a=cur+nxt+c1;x,d,nc1=a%2,(a%4)//2,a//4
                b=prev+d+c2;z,e,nc2=b%2,(b%4)//2,b//4
                c=x+d-e+c3;y,nc3=c%4,c//4
                temporal=W*y+ct
                if temporal%4!=nxt:continue
                nf=flags|(1 if x else 0)|(2 if d else 0)|(4 if e else 0)|(8 if z else 0)|(16 if y else 0)
                state=(cur,nxt,nb,nc1,nc2,nc3,temporal//4,nf,live or bool(cur))
                following.setdefault(state,(I,T+(bit*4**(pos+1) if pos+1<N else 0)))
        states=following;sizes.append(len(states))
        if not states:break
    witnesses=[]
    if len(sizes)==N+1:
        for (prev,cur,borrow,c1,c2,c3,F,flags,live),(I,T) in states.items():
            extra=prev+c2
            if extra%2:flags|=8
            if c1 or c3 or extra>=2 or flags!=31 or not live or F<=0:continue
            witness=check_word(N,v,T)
            assert witness and witness['I']==I and witness['F']==F
            witnesses.append(witness)
    return dict(N=N,v=v,state_counts=sizes,witnesses=witnesses)


def verify():
    brute=[];words=0
    for N in range(1,17):
        Q=4**N
        for divisor in sp.divisors(Q-1):
            v=isqrt(divisor+1)
            if v*v!=divisor+1 or v<2 or not(v&(v-1)):continue
            witnesses=[]
            for bits in product(range(2),repeat=N):
                words+=1
                witness=check_word(N,v,pack(bits))
                if witness:witnesses.append(witness)
            dp=digit_search(N,v)
            assert bool(dp['witnesses'])==bool(witnesses)
            brute.append(dict(N=N,v=v,Boolean_words=2**N,witnesses=witnesses))
    extended=[]
    for v,period in ((6,6),(14,6),(20,9),(118,12),(10,15)):
        for N in range(period,period*11,period):
            extended.append(digit_search(N,v))
    # Positive controls exercise reconstruction and the final state test.
    controls=[digit_search(N,v) for N,v in ((8,16),(12,16),(15,32),(20,32))]
    assert all(row['witnesses'] for row in controls)
    return dict(status='BOUNDED_NONPOWER_GEOMETRY_SEARCH_COMPLETE',
                general_redundancy_status='UNRESOLVED',brute_Boolean_words=words,
                brute_cases=brute,extended_digit_search=extended,
                positive_power_two_controls=controls,
                counterexamples_found=sum(len(row['witnesses']) for row in extended),
                scope='Finite exact search without q=v*quot. No general redundancy theorem and no81-operation certificate is claimed. Both odd and even packed words are searched; no astronomical Pell witnesses are constructed.')


if __name__=='__main__':
    result=verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status'],'words',result['brute_Boolean_words'],'counterexamples',result['counterexamples_found'])
    print('General geometry redundancy remains UNRESOLVED.')
