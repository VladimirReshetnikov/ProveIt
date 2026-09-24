"""Exact local arithmetic checks; no universality or history claim."""

from itertools import product
import json
from pathlib import Path


def pack(digits):
    return sum(d * 4**i for i, d in enumerate(digits))


def verify():
    accepted = []
    for a, b, c, cp, u, v, w in product(range(2), repeat=7):
        actual = a + b == v + 2*u and u + c == cp + 2*w
        expected = (u == a*b and v == (a ^ b)
                    and cp == (c ^ (a*b)) and w == u*c)
        assert actual == expected
        if actual:
            accepted.append([a, b, c, cp, u, v, w])
    assert len(accepted) == 8

    packed_cases = 0
    for flat in product(range(2), repeat=9):
        a, b, c = flat[:3], flat[3:6], flat[6:]
        u = [x*y for x, y in zip(a, b)]
        v = [x ^ y for x, y in zip(a, b)]
        cp = [x ^ y for x, y in zip(c, u)]
        w = [x*y for x, y in zip(u, c)]
        A, B, C, U, V, CP, W = map(pack, (a, b, c, u, v, cp, w))
        assert A + B == V + 2*U
        assert U + C == CP + 2*W
        packed_cases += 1
    assert packed_cases == 512

    for s, a, b in product(range(2), repeat=3):
        t = s*(b-a)
        assert (a+t, b-t) == ((b, a) if s else (a, b))
        u, v, p, q = s*a, s*b, s ^ a, s ^ b
        assert s+a == p+2*u and s+b == q+2*v
        assert (a+(v-u), b-(v-u)) == ((b, a) if s else (a, b))

    # Removing the Boolean condition on a carry plane is unsound.
    U, C, CP, W = 4, 0, 0, 2
    assert U+C == CP+2*W and CP != (U ^ C)

    # The scalar Fredkin formula incorrectly mixes different digit positions.
    S, A, B = 1, 0, 4
    t = S*(B-A)
    assert (A+t, B-t) == (4, 0)
    pointwise_u, pointwise_v = S & A, S & B
    assert (A+pointwise_v-pointwise_u, B-pointwise_v+pointwise_u) == (0, 4)

    return {
        "status": "LOCAL_ARITHMETIC_PASS_UNIVERSAL_HISTORY_NOT_ESTABLISHED",
        "scope": "Boolean Toffoli/Fredkin local relations only; no CA universality, input conversion, mask implementation, or history boundary verified",
        "toffoli": {
            "assignment_cases": 128,
            "accepted_gate_assignments": accepted,
            "packed_three_position_cases": packed_cases,
            "primitive_count": 6,
            "multiplications": 2,
            "additions": 4,
            "equalities": ["A+B=V+2U", "U+C=Cprime+2W"],
            "required_domains": "all seven aligned words have base-4 digits in {0,1}; zero allowed",
        },
        "fredkin": {
            "scalar_input_cases": 8,
            "scalar_primitive_count": 4,
            "packed_primitive_count": 9,
            "packed_multiplications": 2,
            "packed_additions_subtractions": 7,
        },
        "explicit_obstructions_checked": [
            "U=4,C=Cprime=0,W=2 defeats omitted carry-plane Booleanity",
            "S=1,A=0,B=4 defeats direct packed use of scalar controlled swap",
        ],
    }


if __name__ == "__main__":
    receipt = verify()
    Path(__file__).with_suffix(".json").write_text(
        json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(receipt, indent=2))
