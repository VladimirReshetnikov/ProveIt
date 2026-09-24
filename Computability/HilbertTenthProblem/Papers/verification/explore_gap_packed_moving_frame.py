#!/usr/bin/env python3
"""Independent finite audit of the unpadded five-plane gap construction."""
from itertools import product
from pathlib import Path
import json

from explore_aligned_boolean_tableaux import pack,digits,bitplane,evolve
from explore_five_plane_moving_frame import split


def verify():
    words=candidates=aligned=extra_Z=final_extension=0
    examples=[]
    for width in range(1,6):
        W,v=4**width,2**width
        for height in range(1,4):
            N=width*height
            Q=W**height
            H=(Q-1)//(W-1)
            for values in product(range(2),repeat=N):
                words+=1
                T=pack(values)
                B=T-H
                if B<=0 or B%4:
                    continue
                candidates+=1
                A,C=4*B,B//4
                assert 3*B<Q
                X,D=split(B+C,N+1)
                Z,E=split(A+D,N+1)
                Y=X+D-E
                if min(D,X,E,Z,Y)<=0:
                    continue
                assert D<Q and X<Q and E<Q and Z<2*Q and Y<Q
                assert B+C==X+2*D and A+D==Z+2*E and Y+E==X+D
                R=D+Q*X+Q**2*E+Q**3*Z
                P=R+Q**7*T
                assert R<Q**7 and P//Q**7==T and P<Q**8
                assert bitplane(P)
                I=C%W
                numer=I+W*Y-C
                if not 0<I<v or numer<=0 or numer%Q:
                    continue
                F=numer//Q
                assert F<W
                aligned+=1
                assert bitplane(B) and bitplane(Y) and bitplane(F)
                ds=digits(B,N)
                rows=[ds[j*width:(j+1)*width] for j in range(height)]
                assert all(row[0]==0 for row in rows)
                for j,row in enumerate(rows):
                    raw=evolve(row)
                    assert pack(raw)==(Y//W**j)%W
                    if j+1<height:
                        assert 4*pack(raw)==pack(rows[j+1])
                    else:
                        assert pack(raw)==F
                assert pack(rows[0])==4*I
                assert P%2==D%2==0
                L=Q**8
                r=(L-P)*(L-1)+2*(L-1)//3
                assert Q**6<=r<Q**18 and r%2==0
                assert r.bit_count()==(Q**12).bit_length()-1
                extra_Z+=int(Z>=Q)
                final_extension+=int(4*F>=W)
                if (Z>=Q or 4*F>=W) and len(examples)<5:
                    examples.append(dict(width=width,height=height,I=I,F=F,
                                         B=B,Z=Z,Q=Q,physical_final=4*F,row_scale=W))
    return dict(status='UNPADDED_GAP_COMPONENT_CHECKS_PASS',universality_status='NOT_CLAIMED',
                Boolean_T_words=words,positive_B_candidates=candidates,
                positive_aligned_histories=aligned,extra_top_Z_cases=extra_Z,
                final_one_cell_extension_cases=final_extension,boundary_examples=examples,
                scope='Finite masked-T enumeration without an independent B/range bound; exact plane extraction, induction conclusion, temporal evolution and special-mask valuation. No universal input or halt theorem is claimed.')


if __name__=='__main__':
    result=verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result,indent=2))
