#!/usr/bin/env python3
"""Fresh finite probes of the packed binary tableau; no author code is imported.

These are regression checks, not substitutes for the all-integer proof.
"""
from itertools import product
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent
B = 32
counts = {}


def packed_frames(frames, sites, volume):
    return sum(B ** (t * volume + v)
               for t, frame in enumerate(frames)
               for j, v in enumerate(sites) if frame & (1 << j))


def recurrence_checks():
    volume, sites = 4, (1, 2)
    Q = B ** volume
    I = sum(B ** v for v in sites)
    examined = valid = 0
    for k in (1, 2, 3):
        for pre in product(range(4), repeat=k):
            P = packed_frames(pre, sites, volume)
            for new in product(range(4), repeat=k):
                E = packed_frames(new, sites, volume)
                residual = Q * (P + E) - P
                quotient, rem = divmod(residual, Q ** k)
                arith = rem == 0 and quotient >= 0 and quotient & ~I == 0
                seen, semantic = 0, True
                for p, e in zip(pre, new):
                    semantic &= p == seen and (e & seen) == 0
                    seen |= e
                assert arith == semantic, (k, pre, new, quotient)
                if arith:
                    assert quotient == packed_frames((seen,), sites, volume)
                examined += 1
                valid += arith
    assert valid == sum((k + 1) ** 2 for k in (1, 2, 3))
    counts['recurrence_assignments'] = examined
    counts['valid_recurrence_assignments'] = valid


def neighbor_checks():
    examined = coefficients = 0
    for a, b, c in ((4, 4, 4), (4, 6, 4), (6, 4, 6)):
        vol, X, Y = a*b*c, B**a, B**(a*b)
        interior = tuple((x, y, z) for z in range(1,c-1)
                         for y in range(1,b-1) for x in range(1,a-1))
        def index(t, xyz):
            x, y, z = xyz
            return t*vol + x+a*y+a*b*z
        for k in (1, 2, 3):
            occupancy = [(t, xyz) for t in range(k) for xyz in interior]
            fixtures = [[item] for item in occupancy]
            fixtures += [[], occupancy, occupancy[::2], occupancy[1::3]]
            for fixture in fixtures:
                P = sum(B ** index(t, xyz) for t, xyz in fixture)
                assert P % B == P % X == P % Y == 0
                shifts = (B*P, X*P, Y*P, P//B, P//X, P//Y)
                directions = ((1,0,0),(0,1,0),(0,0,1),(-1,0,0),(0,-1,0),(0,0,-1))
                for actual, delta in zip(shifts, directions):
                    expected = 0
                    for t, xyz in fixture:
                        dest = tuple(x+d for x,d in zip(xyz,delta))
                        assert all(0 <= v < bound for v,bound in zip(dest,(a,b,c)))
                        expected += B ** index(t, dest)
                    assert actual == expected
                    assert actual < B ** (k*vol)
                available = 20 * sum(B**j for j in range(k*vol)) + sum(shifts)
                digits = []
                while available:
                    available, digit = divmod(available, B)
                    digits.append(digit)
                assert len(digits) == k*vol and all(20 <= d <= 26 for d in digits)
                coefficients += len(digits)
                examined += 1
    counts['neighbor_fixtures'] = examined
    counts['neighbor_coefficients'] = coefficients


def legality_checks():
    examined = 0
    for available in range(27):
        for selected in (0, 1):
            feasible = []
            for planes in product((0, 1), repeat=5):
                permitted = all(p <= selected for p in planes) and planes[3]+planes[4] <= selected
                slack = sum(p * 2**j for j, p in enumerate(planes))
                lhs = available & (31*selected)
                accepted = permitted and lhs == 6*selected+slack
                if accepted:
                    feasible.append(slack)
                examined += 1
            assert bool(feasible) == (selected == 0 or available >= 6)
            assert feasible == ([0] if selected == 0 else ([available-6] if available >= 6 else []))
    counts['legality_bitplane_assignments'] = examined


def target_checks():
    examined = 0
    for half in range(2, 10):
        for zeta in range(4*half+4):
            h, sign = divmod(zeta, 2)
            coord = h - 2*sign*h - sign
            for ell in range(2*half):
                arithmetic = ell+2*sign*h+sign == half+h
                assert arithmetic == (ell == half+coord)
                if arithmetic:
                    assert 2*half-ell > 0
                examined += 1
    # Every in-box triple has a unique base-32 point and its own physical index.
    for a,b,c in ((4,4,4),(4,6,8)):
        points = [B**(x+a*y+a*b*z) for z in range(c) for y in range(b) for x in range(a)]
        assert len(set(points)) == a*b*c
    counts['signed_target_bound_cases'] = examined


def adversarial_checks():
    origin, target = (0,0,0), (1,0,0)
    directions = ((1,0,0),(0,1,0),(0,0,1),(-1,0,0),(0,-1,0),(0,0,-1))
    def topple(state, v):
        assert state.get(v,0) >= 6
        state[v] -= 6
        for delta in directions:
            w = tuple(x+d for x,d in zip(v,delta))
            state[w] = state.get(w,0)+1
    state = {origin:12,target:4}
    assert [v for v,h in state.items() if h>=6] == [origin]
    topple(state,origin)
    assert state[target] == 5
    assert [v for v,h in state.items() if h>=6] == [origin]
    topple(state,origin)
    assert state[target] == 6
    topple(state,target)
    # Initially stable adjacent height-five sites cannot start any legal layer.
    assert not any(h>=6 for h in {origin:5,target:5}.values())
    counts['adversarial_examples'] = 2


if __name__ == '__main__':
    recurrence_checks()
    neighbor_checks()
    legality_checks()
    target_checks()
    adversarial_checks()
    result = {'status':'PASS','finite_tests_only':True,'counts':counts,
              'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    (ROOT/'semantics-receipt.json').write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
    print(json.dumps(result,sort_keys=True,indent=2))
