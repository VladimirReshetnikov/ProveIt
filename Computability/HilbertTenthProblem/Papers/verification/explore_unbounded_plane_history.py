#!/usr/bin/env python3
"""Finite audit of gapped five-plane packing without the ABC bound."""
from itertools import product
from pathlib import Path
import json
from explore_aligned_boolean_tableaux import pack,digits,bitplane,rule


def split(value,length):
    ds=digits(value,length)
    assert value<4**length
    return pack([d%2 for d in ds]),pack([d//2 for d in ds])


def evolve_unbounded(row):
    extended=row+[0]
    return [rule(extended[i-1] if i else 0,extended[i],
                 extended[i+1] if i+1<len(extended) else 0)
            for i in range(len(extended))]


def verify():
    enumerated=candidates=positive=accepted=overflow_z=extended_final=0
    interesting=[]
    for width in range(1,6):
        W,v=4**width,2**width
        for height in range(1,4):
            length=width*height; Q=W**height; H=(Q-1)//(W-1)
            for values in product(range(2),repeat=length):
                enumerated+=1; T=pack(values); B=T-H
                if B<=0 or B%4: continue
                candidates+=1; A,C=4*B,B//4
                X,D=split(B+C,length)
                # The possible digit above the tableau is essential here.
                Z,E=split(A+D,length+1)
                Y=X+D-E
                if min(X,D,Z,E,Y)<=0: continue
                positive+=1
                assert B+C==X+2*D and A+D==Z+2*E and Y+E==X+D
                assert 3*B<Q and D<Q and X<Q and E<Q and Z<2*Q and Y<Q
                I=C%W; raw=I+W*Y-C
                if I<=0 or I>=v or raw<=0 or raw%Q: continue
                F=raw//Q
                assert 0<F<W and bitplane(B) and bitplane(Y) and bitplane(I)
                rows=[digits((B//W**j)%W,width) for j in range(height)]
                successors=[evolve_unbounded(row) for row in rows]
                assert all(row[0]==0 for row in rows)
                assert all(rawrow[-1]==0 for rawrow in successors)
                assert Y==pack([bit for rawrow in successors for bit in rawrow[:-1]])
                assert all([0]+successors[j][:-2]==rows[j+1]
                           for j in range(height-1))
                assert all(successors[j][-2]==0 for j in range(height-1))
                assert 4*I==pack(rows[0])
                final=[0]+successors[-1][:-1]
                assert 4*F==pack(final)
                P=D+Q*X+Q**2*E+Q**3*Z+Q**7*T
                L,n0=Q**8,Q**6; r=(L-P)*(L-1)+2*(L-1)//3
                assert 0<P<L and n0*n0<r<Q**16<n0**3
                assert P%2==r%2==0 and r.bit_count()==(Q**12).bit_length()-1
                accepted+=1
                if Z>=Q: overflow_z+=1
                if 4*F>=W: extended_final+=1
                if (Z>=Q or 4*F>=W) and len(interesting)<8:
                    interesting.append(dict(width=width,height=height,Q=Q,W=W,
                         T=T,B=B,C=C,D=D,X=X,E=E,Z=Z,Y=Y,I=I,F=F,
                         Z_overflow=Z>=Q,final_extends=4*F>=W))
    canonical=[]
    for I in (1,4,5,16,17,21,64,277):
        for height in (3,4,8,16):
            width=max((4*I).bit_length()//2+height+1,I.bit_length()+1)
            W=4**width; Q=W**height; H=(Q-1)//(W-1)
            row=digits(4*I,width); rows=[]
            for unused in range(height):
                rows.append(row)
                raw=evolve_unbounded(row)
                assert raw[-2:]==[0,0]
                row=[0]+raw[:-2]
            B=pack([bit for row0 in rows for bit in row0]); C=B//4
            X,D=split(B+C,width*height)
            Z,E=split(4*B+D,width*height+1); Y=X+D-E; F=pack(row)//4
            assert min(B,C,D,X,E,Z,Y,F,2**width-I)>0
            assert I+W*Y==C+Q*F
            P=D+Q*X+Q**2*E+Q**3*Z+Q**7*(B+H)
            L=Q**8; r=(L-P)*(L-1)+2*(L-1)//3
            assert bitplane(P) and P%2==r%2==0 and Q**12<r<Q**16
            assert r.bit_count()==(Q**12).bit_length()-1
            canonical.append(dict(I=I,width=width,height=height))
    return dict(status='GAPPED_BOUND_FREE_COMPONENT_AUDIT_PASS',
                universality_status='NOT_ESTABLISHED',Boolean_T_words=enumerated,
                positive_B_candidates=candidates,positive_local_candidates=positive,
                accepted_histories=accepted,accepted_with_extra_Z_digit=overflow_z,
                accepted_with_extended_final=extended_final,
                edge_cases=interesting,canonical_positive_cases=len(canonical),
                canonical=canonical,
                scope='Finite decoding audit with no ABC bound, complete Z including its extra digit, and unbounded final moving step; exact packed popcount. This is not a universal certificate.')


if __name__=='__main__':
    result=verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({k:v for k,v in result.items() if k!='canonical'},indent=2))
