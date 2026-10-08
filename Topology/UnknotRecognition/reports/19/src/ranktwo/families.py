"""Constructive test families and exact survivor lower-bound arithmetic."""
from __future__ import annotations
from .oracles import inverse


def weaving_prefix(m: int, base: int = 1) -> tuple[int, ...]:
    if type(m) is not int or m < 0 or type(base) is not int or base < 1:
        raise ValueError('m must be nonnegative and base must be positive')
    return (base, -(base + 1)) * m


def central_sleeve(m: int, base: int = 1) -> tuple[int, ...]:
    beta = weaving_prefix(m, base)
    z = (base, base + 1, base) * 2
    return beta + z + inverse(beta) + inverse(z)


def sleeved_unknot(strands: int, m: int) -> tuple[int, ...]:
    if type(strands) is not int or strands < 4:
        raise ValueError('this stress family uses at least four strands')
    return central_sleeve(m, 1) + central_sleeve(m, strands - 2) + tuple(range(1, strands))


HALF_TWIST_LEFT = (1, 2, 3, 1, 2, 1)
HALF_TWIST_RIGHT = (3, 2, 1, 3, 2, 3)
BARRIER_RELATOR = HALF_TWIST_LEFT + inverse(HALF_TWIST_RIGHT)


def shortening_barrier(repetitions: int) -> tuple[int, ...]:
    if type(repetitions) is not int or repetitions < 1:
        raise ValueError('repetitions must be positive')
    return BARRIER_RELATOR * repetitions + (1, 2, 3)


def weaving_determinant(m: int) -> int:
    if type(m) is not int or m < 0:
        raise ValueError('m must be nonnegative')
    # T_m=trace([[2,1],[1,1]]^m), T_0=2, T_1=3.
    if m == 0:
        return 0
    previous, current = 2, 3
    for _ in range(1, m):
        previous, current = current, 3 * current - previous
    return current - 2


def survivor_lower_bound(m: int) -> int:
    if m % 3 == 0:
        raise ValueError('the stated knot-closure lower bound uses 3 not dividing m')
    return (weaving_determinant(m) + 3) // 4
