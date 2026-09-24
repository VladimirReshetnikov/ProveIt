#!/usr/bin/env python3
"""Finite checks of conditional alignment; no universal system is claimed."""
from itertools import product
from pathlib import Path
import json


def pack(bits):
    return sum(bit*4**i for i, bit in enumerate(bits))


def digits(value, length):
    return [(value//4**i) % 4 for i in range(length)]


def bitplane(value):
    while value:
        if value % 4 > 1:
            return False
        value //= 4
    return True


def rule(a, b, c):
    return (110 >> (4*a+2*b+c)) & 1


def evolve(row):
    return [rule(row[i-1] if i else 0, row[i],
                 row[i+1] if i+1 < len(row) else 0)
            for i in range(len(row))]


def local_planes(B, length):
    A, C = 4*B, B//4
    aa, bb, cc = (digits(z, length) for z in (A, B, C))
    D = pack([b*c for b, c in zip(bb, cc)])
    X = pack([b ^ c for b, c in zip(bb, cc)])
    E = pack([a*b*c for a, b, c in zip(aa, bb, cc)])
    Z = pack([a ^ (b*c) for a, b, c in zip(aa, bb, cc)])
    Y = pack([rule(a, b, c) for a, b, c in zip(aa, bb, cc)])
    assert B+C == X+2*D and A+D == Z+2*E and Y+E == X+D
    return A, C, D, X, E, Z, Y


def verify_alignment():
    proposed, bounded, aligned = 0, 0, 0
    for width in range(2, 6):
        W = 4**width
        for height in range(1, 4):
            length, Q = width*height, W**height
            h = (Q-1)//(W-1)
            slots = [i for i in range(length) if i % width]
            for choices in product(range(2), repeat=len(slots)):
                proposed += 1
                values = [0]*length
                for i, value in zip(slots, choices):
                    values[i] = value
                B = pack(values)
                assert bitplane(B+h)
                if not B or 4*B+B+B//4 >= Q:
                    continue
                bounded += 1
                A, C, D, X, E, Z, Y = local_planes(B, length)
                assert all(0 <= value < Q for value in (A,B,C,D,X,E,Z,Y,B+h))
                I, F = B % W, Y//W**(height-1)
                condition = I+W*Y == B+Q*F
                rows = [values[j*width:(j+1)*width] for j in range(height)]
                expected = [evolve(row) for row in rows]
                actual = digits(Y, length)
                assert actual == [bit for row in expected for bit in row]
                direct_alignment = all(expected[j] == rows[j+1]
                                       for j in range(height-1))
                assert condition == direct_alignment
                if condition:
                    aligned += 1
                    assert all(row[-1] == 0 for row in rows)
                    assert I > 0 and F > 0 and F < W
                    assert Y == pack([bit for row in expected for bit in row])
                    assert I+W*Y-B < W*Q
    return dict(proposed_bit_histories=proposed, numerically_bounded=bounded,
                temporally_aligned=aligned, width_range=[2,5], height_range=[1,3])


def verify_masks_and_lifts():
    masks = lifts = raw_inputs = 0
    for width in range(1, 4):
        for height in range(1, 4):
            length, W = width*height, 4**width
            Q = W**height
            h = (Q-1)//(W-1)
            for values in product(range(2), repeat=length):
                B = pack(values)
                assert bitplane(B+h) == all(values[j*width] == 0 for j in range(height))
                masks += 1
    for values in product(range(2), repeat=8):
        a,b,c,y,d,x,e,z = values
        old = b+c == x+2*d and a+d == z+2*e and y+e == x+d
        for Q in (4,16,64):
            ap,bp,cp,yp,dp,xp,ep,zp = [u+k*Q for u,k in
                                      zip(values,(2,1,2,1,1,1,1,1))]
            new = bp+cp == xp+2*dp and ap+dp == zp+2*ep and yp+ep == xp+dp
            assert old == new and min(ap,bp,cp,yp,dp,xp,ep,zp) > 0
            lifts += 1
    for value in range(4**6):
        ds = digits(value, 6)
        I0, I1 = pack([d % 2 for d in ds]), pack([d//2 for d in ds])
        assert bitplane(I0) and bitplane(I1) and I0+2*I1 == value
        raw_inputs += 1
    return dict(mask_cases=masks, affine_lift_cases=lifts, raw_input_cases=raw_inputs)


def verify_positive_canonical():
    cases = 0
    for height in range(1, 9):
        row = [0]*(height+1)+[1,1,1,0]+[0]*(height+1)
        width, rows = len(row), []
        for unused in range(height):
            rows.append(row)
            row = evolve(row)
        length, W = width*height, 4**width
        Q, B = W**height, pack([bit for row0 in rows for bit in row0])
        h = (Q-1)//(W-1)
        A,C,D,X,E,Z,Y = local_planes(B, length)
        assert min(B,D,X,E,Z,B+h) > 0
        assert 12*B < Q and A+B+C < Q
        assert bitplane(B+h)
        I, F = pack(rows[0]), pack(row)
        assert 0 < I < W and 0 < F < W
        assert I+W*Y == B+Q*F
        P = 0
        for field in reversed((B,D,X,E,Z,B+h)):
            P = field+Q*P
        n0, Lbig = Q**6, Q**8
        lam = (Lbig-1)//3
        r = (Lbig-P)*(Lbig-1)+2*lam
        assert 0 < P < n0 and P % 2 == 0
        assert n0 >= 64 and n0 < r < n0**3 and r % 2 == 0
        cases += 1
    return dict(canonical_positive_cases=cases,
                checked='Five positive auxiliary planes, initial/final bounds, first-column mask, shared bound, packing ranges and even parity.')


def verify():
    return dict(status='CONDITIONAL_COMPONENTS_PASS', universality_status='OPEN',
                alignment=verify_alignment(), masks_and_lifts=verify_masks_and_lifts(),
                positive_canonical=verify_positive_canonical(),
                scope='Finite component regressions only; no binary-mask/binomial equivalence or universal input theorem is claimed.')


if __name__ == '__main__':
    result = verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(json.dumps(result, indent=2))
