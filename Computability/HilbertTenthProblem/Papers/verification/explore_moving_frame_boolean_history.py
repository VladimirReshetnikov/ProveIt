#!/usr/bin/env python3
"""Focused finite moving-frame checks; not a universal-machine theorem."""
from itertools import product
from pathlib import Path
import json
from explore_aligned_boolean_tableaux import pack, digits, bitplane, evolve, local_planes


def moving_step(row):
    raw = evolve(row)
    assert raw[-1] == 0
    return [0] + raw[:-1]


def verify():
    proposed = bounded = aligned = positive_aligned = 0
    for width in range(2,6):
        W = 4**width
        for height in range(1,4):
            length, Q = width*height, W**height
            h = (Q-1)//(W-1)
            slots = [i for i in range(length) if i % width]
            for choices in product(range(2), repeat=len(slots)):
                proposed += 1
                values = [0]*length
                for slot, value in zip(slots, choices):
                    values[slot] = value
                B = pack(values)
                if not B or 4*B+B+B//4 >= Q:
                    continue
                bounded += 1
                A,C,D,X,E,Z,Y = local_planes(B, length)
                assert 4*Y < Q
                I, F = C % W, Y//W**(height-1)
                condition = I+W*Y == C+Q*F
                rows = [values[j*width:(j+1)*width] for j in range(height)]
                successors = [evolve(row) for row in rows]
                direct = all(successors[j][-1] == 0 and
                             [0]+successors[j][:-1] == rows[j+1]
                             for j in range(height-1))
                direct = direct and successors[-1][-1] == 0
                assert condition == direct
                if condition:
                    aligned += 1
                    assert all(row[-1] == 0 for row in rows)
                    assert pack(rows[0]) == 4*I and pack([0]+successors[-1][:-1]) == 4*F
                    assert 0 < I < W and 0 < F < W and bitplane(B+h)
                    assert Y == pack([bit for row in successors for bit in row])
                    if min(B,C,D,X,E,Z,Y) > 0:
                        positive_aligned += 1

    canonical = []
    fixed_initial = pack([1,1,1,0,1])
    for height in (1,2,3,4,8,16,32):
        width = 8+height
        row = digits(4*fixed_initial, width)
        rows = []
        leftmost = next(i for i,b in enumerate(row) if b)
        rightmost = max(i for i,b in enumerate(row) if b)
        for step in range(height):
            assert row[0] == row[-1] == 0
            assert next(i for i,b in enumerate(row) if b) == leftmost
            assert max(i for i,b in enumerate(row) if b) == rightmost+step
            rows.append(row)
            row = moving_step(row)
        W,Q = 4**width,4**(width*height)
        B = pack([bit for row0 in rows for bit in row0])
        H = (Q-1)//(W-1)
        A,C,D,X,E,Z,Y = local_planes(B,width*height)
        F = pack(row)//4
        assert min(B,C,D,X,E,Z,Y) > 0
        assert 12*B < Q and A+B+C < Q
        assert fixed_initial+W*Y == C+Q*F
        assert all(bitplane(z) and z<Q for z in (B,D,X,E,Z,B+H))
        P = 0
        for field in reversed((B,D,X,E,Z,B+H)):
            P = field+Q*P
        L,n0,scale = Q**8,Q**6,Q**12
        lam = (L-1)//3
        r = (L-P)*(L-1)+2*lam
        assert 0<P<n0 and P%2 == r%2 == 0 and n0*n0<r<n0**3
        assert r.bit_count() == 3*((L.bit_length()-1)//2)
        assert scale.bit_length()-1 == r.bit_count()
        canonical.append(dict(height=height,width=width,initial=fixed_initial,
                              final_bit_length=F.bit_length(),r_bit_length=r.bit_length()))
    return dict(status='CONDITIONAL_MOVING_FRAME_PASS',universality_status='OPEN',
                proposed_histories=proposed,bounded_histories=bounded,
                aligned_histories=aligned,positive_aligned_histories=positive_aligned,
                canonical_fixed_initial_cases=canonical,
                scope='Finite exhaustive alignment and seven positive canonical histories with the same initial row, through height32; exact popcount and parity, but no huge Pell witnesses or universality claim.')


if __name__ == '__main__':
    result=verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result,indent=2))
