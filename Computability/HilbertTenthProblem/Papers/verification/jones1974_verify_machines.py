#!/usr/bin/env python3
"""Executable checks for the corrected edition of Jones (1974).

Python 3.10+, standard library only. Finite tests are not proofs of the general
computability theorems. A transition writes, moves, and then enters its target
state; 0 is the halt state. Tape positions scanned only after halting are not
counted as actively visited. Run: python3 jones1974_verify_machines.py
Self-contained (reads no article source).
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction
from itertools import product

Rule = tuple[int, int, int]  # write bit, direction (-1 or +1), target state
Machine = dict[tuple[int, int], Rule]  # (state, scanned bit) -> rule

@dataclass
class Result:
    halted: bool
    steps: int
    state: int
    head: int
    ones: set[int]
    visited: set[int]


def validate(machine: Machine) -> int:
    n = max(q for q, _ in machine)
    assert set(machine) == set(product(range(1, n + 1), range(2)))
    assert all(w in (0, 1) and d in (-1, 1) and 0 <= q <= n
               for w, d, q in machine.values())
    return n


def run(machine: Machine, ones: set[int] | None = None,
        limit: int = 1000000) -> Result:
    validate(machine)
    tape = set() if ones is None else set(ones)
    q, head = 1, 0
    visited: set[int] = set()
    for steps in range(limit):
        visited.add(head)
        w, d, q = machine[q, int(head in tape)]
        if w:
            tape.add(head)
        else:
            tape.discard(head)
        head += d
        if q == 0:
            return Result(True, steps + 1, q, head, tape, visited)
    return Result(False, limit, q, head, tape, visited)


def clean_unary(r: Result, value: int) -> bool:
    return r.halted and r.ones == set(range(r.head, r.head + value + 1))


ADD2: Machine = {
    (1, 0): (1, 1, 2), (1, 1): (1, -1, 2),
    (2, 0): (1, -1, 1), (2, 1): (1, -1, 0),
}
DOUBLE: Machine = {
    (1, 0): (0, 1, 4), (1, 1): (0, -1, 2),
    (2, 0): (1, 1, 3), (2, 1): (1, -1, 2),
    (3, 0): (1, 1, 1), (3, 1): (1, 1, 3),
    (4, 0): (0, -1, 4), (4, 1): (0, -1, 5),
    (5, 0): (0, 1, 0), (5, 1): (1, -1, 5),
}


def printer(x: int) -> Machine:
    """The x+1-state construction used only for x >= 1."""
    if x < 1:
        raise ValueError("This construction requires x >= 1")
    m = {(q, 0): (1, -1, q + 1) for q in range(1, x + 1)}
    # The printed figure left these unreachable rules unspecified.
    m.update({(q, 1): (1, -1, 0) for q in range(1, x + 1)})
    m[x + 1, 0] = (1, 1, x + 1)
    m[x + 1, 1] = (1, -1, 0)
    return m


def append_one(machine: Machine) -> Machine:
    n = validate(machine)
    out = {key: (w, d, q if q else n + 1)
           for key, (w, d, q) in machine.items()}
    out[n + 1, 0] = (1, 1, 0)
    out[n + 1, 1] = (1, 1, n + 1)
    return out


def compose(*machines: Machine) -> Machine:
    """Run in argument order; redirect each halt to the next starting state."""
    ns = [validate(m) for m in machines]
    out: Machine = {}
    offset = 0
    for i, (m, n) in enumerate(zip(machines, ns)):
        next_start = offset + n + 1 if i + 1 < len(machines) else 0
        for (q, b), (w, d, target) in m.items():
            out[offset + q, b] = (w, d, offset + target if target else next_start)
        offset += n
    return out


def record_cells(machine: Machine) -> Machine:
    """At most 3n states; for a halting source visiting k cells, score > k.

    Data cells are the even positions; intervening markers are set to 1.
    Only (target, direction) pairs actually occurring in nonhalting rules need
    helper states. A halting source has at least one halt rule, leaving room
    for a final state that scans right and appends a 1. See editorial notes.
    """
    n = validate(machine)
    if not any(q == 0 for _, _, q in machine.values()):
        raise ValueError("Need at least one halt rule for this construction")
    pairs = sorted({(q, d) for _, d, q in machine.values() if q})
    helpers = {pair: n + 1 + i for i, pair in enumerate(pairs)}
    append = n + len(pairs) + 1
    assert append <= 3 * n
    out: Machine = {}
    for key, (w, d, target) in machine.items():
        out[key] = (w, d, helpers[target, d]) if target else (1, d, append)
    for (target, d), helper in helpers.items():
        for b in (0, 1):
            out[helper, b] = (1, d, target)
    out[append, 0] = (1, 1, 0)
    out[append, 1] = (1, 1, append)
    validate(out)
    return out


def small_machine_checks(n: int, cutoff: int) -> tuple[int, int, int, int]:
    """Enumerate all labelled tables. Count only halts witnessed by cutoff.

    Agreement with H(n) uses the established SH(1)=1 or SH(2)=6 bound, not
    a claim that a finite simulation alone proves that later halts cannot occur.
    """
    rules = list(product((0, 1), (-1, 1), range(n + 1)))
    keys = list(product(range(1, n + 1), (0, 1)))
    h = score = cells = shifts = 0
    for choices in product(rules, repeat=2*n):
        m = dict(zip(keys, choices))
        r = run(m, limit=cutoff)
        if r.halted:
            h += 1
            score = max(score, len(r.ones))
            cells = max(cells, len(r.visited))
            shifts = max(shifts, r.steps)
            # Additional finite check of the 3n-state strict construction.
            rec = run(record_cells(m), limit=4*cutoff+10)
            assert rec.halted and len(rec.ones) > len(r.visited)
    return h, score, cells, shifts


def main() -> None:
    checks = 0
    r = run(ADD2)
    assert r.halted and (r.steps, len(r.ones)) == (6, 4)
    print("Example 1 on blank tape: 6 shifts, 4 ones.")
    for x in range(101):
        a = run(ADD2, set(range(x + 1)))
        d = run(DOUBLE, set(range(x + 1)))
        assert clean_unary(a, x + 2) and a.steps == 4
        assert clean_unary(d, 2*x)
        # From the sweep structure: 2x^2 + 7x + 9 shifts.
        assert d.steps == 2*x*x + 7*x + 9
        checks += 2
    print("Unary examples: x=0,...,100; clean output and head position checked.")
    assert not run(DOUBLE, limit=10000).halted
    print("Example 2 blank run tested for 10,000 steps; its blank-loop rule also gives a direct proof.")
    for x in range(1, 101):
        p = run(printer(x))
        assert clean_unary(p, x) and p.steps == x + 2
        comp = compose(printer(x), DOUBLE, ADD2)
        assert validate(comp) == x + 8  # c=2
        assert clean_unary(run(comp), 2*x + 2)
        checks += 2
    print("Printers and proof composition: x=1,...,100 checked.")
    ext = run(append_one(ADD2))
    assert ext.halted and len(ext.ones) == 5
    print("Monotonicity extension: 2-state score 4 becomes 3-state score 5.")
    for n, cutoff, expected in [(1, 1, (32, 1, 1, 1)), (2, 6, (9784, 4, 4, 6))]:
        found = small_machine_checks(n, cutoff)
        assert found == expected
        print(f"All {(4*n+4)**(2*n):,} labelled {n}-state tables: "
              f"halts by step {cutoff}={found[0]:,}, Sigma={found[1]}, "
              f"SC={found[2]}, SH={found[3]}.")
        print("  Strict SC-to-Sigma construction checked for every witnessed halter.")
    assert 20**8 == 25600000000
    for n, h in [(1, 32), (2, 9784), (3, 7571840)]:
        p = Fraction(h, (4*n+4)**(2*n))
        print(f"n={n}: H/N={p}={float(p):.9f}; rounded to 3 decimals: {float(p):.3f}")
    print(f"PASS: {checks} unary/printer/composition cases, plus exhaustive small-table and other checks.")

if __name__ == '__main__':
    main()
