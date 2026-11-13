"""Finite checks supporting (not replacing) the written semantic arguments."""
import itertools
import json
import random
from pathlib import Path
from environment_programs import *


def source_term(rng, depth, variables):
    if depth == 0:
        return ("zero",) if rng.randrange(2) else ("var", rng.randrange(variables))
    choice = rng.randrange(4)
    if choice == 0:
        return ("var", rng.randrange(variables))
    if choice == 1:
        return ("succ", source_term(rng, depth - 1, variables))
    if choice == 2:
        return ("zero",)
    count = ("zero",)
    for _ in range(rng.randrange(3)):
        count = ("succ", count)
    return ("iter", count, source_term(rng, depth - 1, variables),
            source_term(rng, depth - 1, variables + 1))


def main():
    counts = dict(pairing=0, naturality=0, reindex_syntax=0,
                  reindex_reading=0, compiler_substitution=0)
    for a, b in itertools.product(range(9), repeat=2):
        assert unpair(pair(a, b)) == (a, b)
        assert pair(a + 1, b) == 1 + pair(0, pair(a, b))
        assert pair(0, b + 1) == pair(0, b) + 2
        counts["pairing"] += 1
    for n in range(512):
        assert pair(*unpair(n)) == n
        counts["pairing"] += 1

    updates = [ZERO, LEFT, LEFT + SUCCESSOR, RIGHT, RIGHT + LEFT]
    transformations = [IDENTITY, ZERO, SUCCESSOR, RIGHT]
    for n, a, e, h, f in itertools.product(range(4), range(4), range(5),
                                           updates, transformations):
        captured = run(iterator(h), pair(n, pair(a, run(f, e))))
        lifted_h = fork(LEFT, RIGHT + f) + h
        explicit = run(iterator(lifted_h), pair(n, pair(a, e)))
        assert captured == explicit
        counts["naturality"] += 1

    atoms = [equation(LEFT, ZERO), equation(RIGHT + LEFT, LEFT),
             equation(LEFT, LEFT), equation(ZERO, SUCCESSOR)]
    formulas = atoms + [closure(IDENTITY, a) for a in atoms]
    formulas += [binder(RIGHT, a) for a in atoms]
    formulas += [binder(IDENTITY, closure(RIGHT, a)) for a in atoms]
    for a, p, q in itertools.product(formulas, transformations, transformations):
        assert reindex(a, IDENTITY) == a
        assert reindex(reindex(a, p), q) == reindex(a, q + p)
        if a[0] in {"Q", "D"}:
            assert reindex(a, p)[2] is a[2]
        counts["reindex_syntax"] += 1
    for a, p, e in itertools.product(formulas, transformations, range(7)):
        assert finite_reading(reindex(a, p), e, 3) == finite_reading(a, run(p, e), 3)
        counts["reindex_reading"] += 1

    rng = random.Random(20261113)
    for _ in range(80):
        body = source_term(rng, 3, 3)
        replacement = source_term(rng, 2, 2)
        old = compile_term(body)
        new = compile_term(substitute(body, replacement))
        supplied = fork(compile_term(replacement), IDENTITY)
        assert valid_word(old) and valid_word(new) and valid_word(supplied)
        for a, b in itertools.product(range(3), range(2)):
            e = pair(a, pair(b, 0))
            assert run(new, e) == run(supplied + old, e)
            counts["compiler_substitution"] += 1

    receipt = {"status": "passed", "checks": counts,
               "scope": "finite semantic and syntax checks, not a formal proof",
               "random_seed": 20261113}
    output = Path(__file__).resolve().parent.parent / "evidence" / "environment_checks.json"
    output.parent.mkdir(exist_ok=True)
    output.write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt))


if __name__ == "__main__":
    main()
