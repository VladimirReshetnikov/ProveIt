#!/usr/bin/env python3
"""Finite corroboration of five-plane decoding; B is not assumed Boolean."""
from itertools import product
from pathlib import Path
import json

from explore_aligned_boolean_tableaux import pack, digits, bitplane, local_planes
from explore_moving_frame_boolean_history import moving_step


def split(value,length):
    ds=digits(value,length)
    return pack([d%2 for d in ds]),pack([d//2 for d in ds])


def verify():
    enumerated=candidate=strong=accepted=weaker_accepted=0
    bad_weaker=[]
    for width in range(1,6):
        W,v=4**width,2**width
        for height in range(1,4):
            length=width*height
            Q=W**height
            H=(Q-1)//(W-1)
            for values in product(range(2),repeat=length):
                enumerated+=1
                T=pack(values)
                B=T-H
                if B<=0 or B%4 or 4*B+B+B//4>=Q:
                    continue
                candidate+=1
                A,C=4*B,B//4
                X,D=split(B+C,length)
                Z,E=split(A+D,length)
                Y=X+D-E
                if min(X,D,Z,E,Y)<=0:
                    continue
                assert B+C==X+2*D and A+D==Z+2*E and Y+E==X+D
                assert 4*Y<Q and all(0<p<Q for p in (T,D,X,E,Z,Y))
                I=C%W
                raw=I+W*Y-C
                if I<=0 or raw<=0 or raw%Q:
                    continue
                F=raw//Q
                assert F<W
                weaker_accepted+=1
                if not bitplane(B) and len(bad_weaker)<3:
                    bad_weaker.append(dict(width=width,height=height,B=B,T=T,I=I,F=F,v=v))
                if I>=v:
                    continue
                strong+=1
                assert width>=2 and I<W//4
                assert bitplane(B) and bitplane(Y)
                bs=digits(B,length)
                assert all(bs[j*width]==0 for j in range(height))
                assert all(bs[j*width+width-1]==0 for j in range(height))
                fields=(D,X,E,Z,T)
                P=sum(field*Q**j for j,field in enumerate(fields))
                assert 0<P<Q**5 and P%2==0
                L=Q**8
                r=(L-P)*(L-1)+2*(L-1)//3
                assert r%2==0 and r.bit_count()==(Q**12).bit_length()-1
                accepted+=1
    canonical=[]
    for I in (1,4,5,16,17,21,64,277):
        assert bitplane(I)
        for height in (3,4,8,16):
            k=(4*I).bit_length()//2-1
            width=max(k+height+2,I.bit_length()+1)
            W,v=4**width,2**width
            Q=W**height
            row=digits(4*I,width)
            rows=[]
            for unused in range(height):
                rows.append(row)
                row=moving_step(row)
            B=pack([bit for r0 in rows for bit in r0])
            A,C,D,X,E,Z,Y=local_planes(B,width*height)
            F=pack(row)//4
            H=(Q-1)//(W-1)
            assert min(B,C,D,X,E,Z,Y,F,v-I)>0
            assert I+W*Y==C+Q*F and A+B+C<Q
            fields=(D,X,E,Z,B+H)
            assert all(bitplane(p) and p<Q for p in fields)
            P=sum(field*Q**j for j,field in enumerate(fields))
            L=Q**8
            r=(L-P)*(L-1)+2*(L-1)//3
            assert 0<P<Q**5 and P%2==r%2==0
            assert r.bit_count()==(Q**12).bit_length()-1
            canonical.append(dict(I=I,height=height,width=width))
    return dict(status='FIVE_PLANE_COMPONENT_CHECKS_PASS',universality_status='NOT_CLAIMED',
                Boolean_T_words=enumerated,bounded_positive_B_candidates=candidate,
                positive_aligned_old_input_bound=weaker_accepted,
                positive_aligned_strong_input_bound=accepted,
                old_bound_nonBoolean_examples=bad_weaker,
                canonical_positive_cases=len(canonical),canonical_cases=canonical,
                scope='Finite masked-T enumeration without assuming B Boolean, plus canonical positive histories. Full proof is in EXPLORATION_FIVE_PLANE_MOVING_FRAME.md; no universal initial-condition or halt predicate is claimed.')


if __name__=='__main__':
    result=verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({k:v for k,v in result.items() if k!='canonical_cases'},indent=2))
