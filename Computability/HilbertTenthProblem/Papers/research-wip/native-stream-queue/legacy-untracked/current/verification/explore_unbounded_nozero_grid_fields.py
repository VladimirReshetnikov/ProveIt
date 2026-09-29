"""A lower-field alias after omitting positive Z from undoubled102.

This is deliberately NOT a full controller or Pell counterexample.
"""
from pathlib import Path
import json
import sympy as sp


def boolean(n):
    if n < 0:
        return False
    while n:
        n, digit = divmod(n, 3)
        if digit == 2:
            return False
    return True


def split(n, parity):
    left = right = 0
    power = 1
    while n:
        n, digit = divmod(n, 3)
        if digit == 2:
            left += power
            right += power
        elif digit == 1:
            if parity:
                left += power
            else:
                right += power
        power *= 3
    assert left + right >= 0 and boolean(left) and boolean(right)
    return left, right


def case(m):
    assert m >= 4 and m % 2 == 0
    R = 3**m
    k = (R - 3) // 6
    x = (k + 1) // 2
    assert k % 2 and 2*x == k+1
    states = list(range(6)) + [3, 1, 2, 3, 4, 5]*x
    u = len(states)
    W = R**3
    q = R**u
    H = (q-1)//(R-1)
    J = (q-1)//2
    values = [2*x, 0, 0]
    A0 = A1 = Kp = Km = 0
    maximum = 0
    for row, state in enumerate(states):
        lane = row % 3
        assert state % 3 == lane
        value = values[lane]
        maximum = max(maximum, value)
        assert 0 <= value < R//3
        if row == 0:
            a0, a1 = k+1, 0
        else:
            a0, a1 = split(value, row % 2)
            assert a0 <= k and a1 <= k
        assert a0+a1 == value
        weight = R**row
        A0 += a0*weight
        A1 += a1*weight
        sign = 1 if state < 3 else -1
        if sign > 0:
            Kp += weight
        else:
            Km += weight
        values[lane] += sign
        assert min(values) >= 0
    assert values == [0, 0, 0]
    D = q+H
    t = k*D
    Z = -q
    supplied = [q, J, W, H, q//W, R, t, A0, A1, Kp, Km, D, R-2*x]
    assert min(supplied) > 0
    residuals = [q-2*J-1, q-W*(q//W), W-R**3,
                 H*(R-1)-2*J, Kp+Km-H, Z+D-H,
                 6*t-(R-3)*D,
                 W*(A0+A1+Kp-Km)-(A0+A1-2*x),
                 2*x+(R-2*x)-R]
    assert residuals == [0]*9
    formal = [Kp, Km, Z, D, t-A0, A0, t-A1, A1]
    expected = [Kp, Km, 0, H-1, k*H-A0+1, A0+k, k*H-A1, A1+k]
    carry = 0
    actual = []
    carries = []
    for value in formal:
        carry, low = divmod(value+carry, q)
        actual.append(low)
        carries.append(carry)
    assert actual == expected and carry == 0
    assert carries == [0, 0, -1, 1, k, 0, k, 0]
    assert all(0 <= value < q and boolean(value) for value in actual)
    assert sum(value*q**i for i, value in enumerate(formal)) == sum(value*q**i for i, value in enumerate(actual))
    assert not boolean(A0) and boolean(D) and D > q and Z < 0
    assert A0 % R == k+1 and actual[5] % R == R//3
    return dict(width=m, radix=R, input=x, height=u, q_bits=q.bit_length(),
                maximum_source=maximum, positive_supplied_coordinates=len(supplied),
                exact_lower_residuals=len(residuals), normalized_Boolean_fields=8,
                signed_carries=carries, D_exceeds_q=True, formal_Z_negative=True,
                initial_track_malformed=True,
                scope='Exact lower-counter equations and first eight mask chunks. No program route, program masks, complete source schedule, or Pell extension is asserted.')


def verify():
    q, H, k, A0, A1, Kp, Km = sp.symbols('q H k A0 A1 Kp Km')
    t = k*(q+H)
    formal = [Kp, Km, -q, q+H, t-A0, A0, t-A1, A1]
    actual = [Kp, Km, 0, H-1, k*H-A0+1, A0+k, k*H-A1, A1+k]
    assert sp.expand(sum((a-b)*q**i for i, (a,b) in enumerate(zip(formal, actual)))) == 0
    cases = [case(m) for m in (4, 6, 8)]
    return dict(status='PASS_UNBOUNDED_NOZERO_LOWER_FIELDS',
                symbolic_packing_identities=1, cases=cases,
                proof='../1980/EXPLORATION_UNBOUNDED_NOZERO_GRID_FIELDS.md',
                scope='A scoped obstruction to proving D<H from the counter subsystem and lower masks alone; the complete Z-eliminated102 construction remains unclassified by this artifact.')


if __name__ == '__main__':
    result = verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(json.dumps(result, indent=2))
