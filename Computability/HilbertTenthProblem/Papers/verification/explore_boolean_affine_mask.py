"""Exact local compiler for Boolean relations; no universal SLP claim.

Fixed constants and bitwise masks in this experiment are mathematical
objects, not free arithmetic implementations of the mask predicate.
Run normally to check the committed receipt, or with --write to refresh it.
"""

from dataclasses import dataclass
from itertools import product
import json
from pathlib import Path
import random
import sys


@dataclass(frozen=True)
class Compilation:
    arity: int
    forbidden: tuple[tuple[int, ...], ...]
    clause_radix: int
    cell_radix: int
    constant: int
    coefficients: tuple[int, ...]
    mask: int

    def evaluate(self, values):
        assert len(values) == self.arity
        return self.constant + sum(c * v for c, v in zip(self.coefficients, values))


def compile_relation(arity, allowed, *, reverse=False, zero_last=False):
    """Compile a truth table; zero_last is useful when zero is forbidden."""
    assert isinstance(arity, int) and arity >= 0
    domain = tuple(product((0, 1), repeat=arity))
    allowed = frozenset(allowed)
    assert allowed <= set(domain)
    forbidden = [p for p in domain if p not in allowed]
    if reverse:
        forbidden.reverse()
    if zero_last:
        zero = (0,) * arity
        assert zero in forbidden
        forbidden.remove(zero)
        forbidden.append(zero)
    radix = 2
    while radix // 2 <= arity - 1:
        radix *= 2
    guard = radix ** len(forbidden)
    constant, coefficients, mask = guard, [0] * arity, 0
    weight = 1
    for pattern in forbidden:
        constant += weight * (sum(pattern) - 1)
        for i, bit in enumerate(pattern):
            coefficients[i] += weight * (1 - 2 * bit)
        mask += (radix // 2) * weight
        weight *= radix
    return Compilation(arity, tuple(forbidden), radix, 2 * guard,
                       constant, tuple(coefficients), mask)


def pack(values, radix):
    word = 0
    for value in reversed(values):
        word = radix * word + value
    return word


def check_assignment(compiled, allowed, values):
    value = compiled.evaluate(values)
    a = compiled.clause_radix
    clauses = [sum(x != y for x, y in zip(values, p)) - 1
               for p in compiled.forbidden]
    direct = a ** len(clauses) + sum(a ** j * u for j, u in enumerate(clauses))
    assert value == direct
    assert 0 < value < compiled.cell_radix
    assert (value & compiled.mask == 0) == (values in allowed)
    if -1 in clauses:
        first = clauses.index(-1)
        assert (value // a ** first) % a == a - 1
    return value


def check_packed(compiled, allowed, cells):
    radix = compiled.cell_radix
    unit = pack([1] * len(cells), radix)
    planes = [pack([cell[i] for cell in cells], radix)
              for i in range(compiled.arity)]
    value = compiled.constant * unit + sum(c * w for c, w in
                                          zip(compiled.coefficients, planes))
    expected = pack([compiled.evaluate(cell) for cell in cells], radix)
    assert value == expected and 0 < value < radix ** len(cells)
    assert (value & (compiled.mask * unit) == 0) == all(c in allowed for c in cells)


def life_allowed(complement_output=False):
    allowed = set()
    for bits in product((0, 1), repeat=9):
        neighbors = sum(bits[:8])
        result = int(neighbors == 3 or (neighbors == 2 and bits[8] == 1))
        allowed.add(bits + (result ^ complement_output,))
    return frozenset(allowed)


def rule110_allowed(complement_output=False):
    allowed = set()
    for left, center, right in product((0, 1), repeat=3):
        result = (110 >> (4 * left + 2 * center + right)) & 1
        allowed.add((left, center, right, result ^ complement_output))
    return frozenset(allowed)


def verify():
    rng = random.Random(20260922)
    relations = assignments = packed_cases = positive_orderings = 0
    for arity in range(4):
        domain = tuple(product((0, 1), repeat=arity))
        for truth in range(1 << len(domain)):
            allowed = frozenset(v for i, v in enumerate(domain) if (truth >> i) & 1)
            relations += 1
            for reverse in (False, True):
                compiled = compile_relation(arity, allowed, reverse=reverse)
                for values in domain:
                    check_assignment(compiled, allowed, values)
                    assignments += 1
                if arity <= 2:
                    for cells in product(domain, repeat=3):
                        check_packed(compiled, allowed, cells)
                        packed_cases += 1
                else:
                    for _ in range(4):
                        cells = [rng.choice(domain) for _ in range(5)]
                        check_packed(compiled, allowed, cells)
                        packed_cases += 1
            if (0,) * arity not in allowed:
                compiled = compile_relation(arity, allowed, zero_last=True)
                assert compiled.constant > 0 and all(c > 0 for c in compiled.coefficients)
                positive_orderings += 1

    examples = {}
    for name, make_allowed in (("rule110", rule110_allowed), ("life", life_allowed)):
        for complement in (False, True):
            allowed = make_allowed(complement)
            arity = len(next(iter(allowed)))
            compiled = compile_relation(arity, allowed, zero_last=complement)
            for values in product((0, 1), repeat=arity):
                check_assignment(compiled, allowed, values)
            for _ in range(256):
                cells = [tuple(rng.randrange(2) for _ in range(arity)) for _ in range(4)]
                check_packed(compiled, allowed, cells)
            if complement:
                assert all(c > 0 for c in compiled.coefficients)
            key = name + ("_complement_output" if complement else "")
            examples[key] = {
                "arity": arity,
                "forbidden_patterns": len(compiled.forbidden),
                "clause_radix": compiled.clause_radix,
                "cell_radix_exponent": compiled.cell_radix.bit_length() - 1,
                "constant_positive": compiled.constant > 0,
                "all_coefficients_positive": all(c > 0 for c in compiled.coefficients),
                "exhaustive_assignments": 1 << arity,
                "packed_four_cell_cases": 256,
                "generic_affine_upper_bound": {"M": arity + 1, "A": arity},
                "repeated_mask_extra_M": 1,
            }
    return {
        "status": "PASS",
        "scope": "Boolean local relation and aligned packed composition only",
        "universal_certificate_improvement": False,
        "exhaustive_relations_arity_0_to_3": relations,
        "assignments_in_two_clause_orders": assignments,
        "packed_small_relation_cases": packed_cases,
        "positive_coefficient_orderings": positive_orderings,
        "examples": examples,
    }


if __name__ == "__main__":
    result = verify()
    path = Path(__file__).with_suffix(".json")
    if sys.argv[1:] == ["--write"]:
        path.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    else:
        assert not sys.argv[1:]
        assert result == json.loads(path.read_text(encoding="utf-8"))
    print(json.dumps(result, indent=2))
