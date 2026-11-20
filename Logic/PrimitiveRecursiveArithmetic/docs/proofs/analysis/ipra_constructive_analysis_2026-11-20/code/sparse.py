"""Exact finite-query algorithms. Addresses are zero based, MSB of a prefix first."""
from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations, product


@dataclass(frozen=True)
class Ask:
    address: int
    on_zero: object
    on_one: object


@dataclass
class Leaf:
    answers: dict
    value: Fraction


def run(node, bit):
    while isinstance(node, Ask):
        node = node.on_one if bit(node.address) else node.on_zero
    return Fraction(node)


def leaves(tree):
    """Consistent traces. A repeated query makes only its forced transition."""
    result = []
    stack = [(tree, {})]
    while stack:
        node, known = stack.pop()
        if not isinstance(node, Ask):
            result.append(Leaf(known, Fraction(node)))
            continue
        q = node.address
        if q < 0:
            raise ValueError("expected a natural address")
        if q in known:
            stack.append(((node.on_zero, node.on_one)[known[q]], known))
        else:
            for bit, child in ((1, node.on_one), (0, node.on_zero)):
                stack.append((child, {**known, q: bit}))
    return result


def conflicts(left, right):
    return [q for q in left.keys() & right.keys() if left[q] != right[q]]


def least_use(rows, tolerance=Fraction(0)):
    """Least prefix length guaranteeing this output oscillation."""
    if tolerance < 0:
        raise ValueError("expected a nonnegative tolerance")
    use = 0
    for a, b in combinations(rows, 2):
        if abs(a.value - b.value) > tolerance:
            first = min(conflicts(a.answers, b.answers))
            use = max(use, 1 + first)
    return use


def carry_possible(left, right):
    """Can left and right extend to u0(1...) and u1(0...) respectively?"""
    coords = left.keys() | right.keys()
    candidates = {0} | coords | {q + 1 for q in coords}
    incompatible = conflicts(left, right)
    for j in candidates:
        if any(q < j for q in incompatible):
            continue
        if left.get(j, 0) != 0 or right.get(j, 1) != 1:
            continue
        if any(q > j and bit != 1 for q, bit in left.items()):
            continue
        if any(q > j and bit != 0 for q, bit in right.items()):
            continue
        return True
    return False


def carry_error(rows):
    return max((abs(a.value - b.value) for a, b in product(rows, repeat=2)
                if carry_possible(a.answers, b.answers)), default=Fraction(0))


def coherence_error(first, second):
    return max(abs(a.value - b.value) for a, b in product(first, second)
               if not conflicts(a.answers, b.answers))


def aggregates(rows):
    mean = sum((row.value / (1 << len(row.answers)) for row in rows), Fraction(0))
    return min(r.value for r in rows), mean, max(r.value for r in rows)


def rational_bit(x, q):
    """Extract one digit without allocating the entire prefix, including x=1."""
    x = Fraction(x)
    if not 0 <= x <= 1 or q < 0:
        raise ValueError("input outside [0,1] or negative address")
    if x == 1:
        return 1
    den = x.denominator
    return (x.numerator * pow(2, q + 1, 2 * den) % (2 * den)) // den


def evaluate_rational(tree, x):
    return run(tree, lambda q: rational_bit(x, q))


def tent_tree(offset, digits):
    """Midpoint samples of the periodic unit tent, using digits after offset."""
    if offset < 0 or digits < 1:
        raise ValueError("expected a nonnegative offset and positive depth")
    def build(i, prefix):
        if i == digits:
            mid = Fraction(2 * prefix + 1, 1 << (digits + 1))
            return 2 * min(mid, 1 - mid)
        return Ask(offset + i, build(i + 1, 2 * prefix),
                   build(i + 1, 2 * prefix + 1))
    return build(0, 0)


def evaluate_name(family, sample, n):
    """Cauchy evaluator of Theorem 2.2. Input sample has radius 2**(-i).
    family(k) returns a finite tree meeting the coherence and carry contracts.
    """
    if n < 0:
        raise ValueError("expected a natural precision")
    current = n + 3
    maximum_use = 0
    for k in range(current + 1):
        tree = family(k)
        maximum_use = max(maximum_use, least_use(leaves(tree)))
    x = min(Fraction(1), max(Fraction(0), Fraction(sample(maximum_use + 2))))
    return evaluate_rational(tree, x)
