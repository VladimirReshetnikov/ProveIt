"""Reproducible exact-arithmetic checks; these are tests, not a formal proof."""
from __future__ import annotations
import itertools
import json
import random
from fractions import Fraction
from pathlib import Path
from boundary_transport import *

ROOT = Path(__file__).resolve().parents[1]
COUNTS: dict[str, int] = {}
def check(condition: bool, group: str) -> None:
    COUNTS[group] = COUNTS.get(group, 0)+1
    if not condition:
        raise AssertionError(f'failed {group}, check {COUNTS[group]}')


def test_operators() -> None:
    rng = random.Random(20261002)
    for _ in range(400):
        p = clean({(rng.randrange(5), rng.randrange(5), rng.randrange(4)):
                   rng.randrange(-7, 8) for _ in range(16)})
        for j in (0, 1):
            d, b = split(p, j); e = [0, 0, 0]; e[j] = 1
            check(add(shift(d, tuple(e)), b) == p, 'boundary decomposition')
            check(split(shift(p, tuple(e)), j)[0] == p, 'left inverse')
            check(split(b, j)[0] == {}, 'boundary killed by decrement')
            for modulus in (2, 3, 5, 6):
                pp = clean(p, modulus)
                dd, bb = split(pp, j)
                check(add(shift(dd, tuple(e)), bb, modulus=modulus) == pp,
                      'modular decomposition')


def small_programs() -> list[Program]:
    options = [Instruction('HALT')]
    options += [Instruction('INC', j, q) for j in (0, 1) for q in range(2)]
    options += [Instruction('TEST', j, q, r)
                for j in (0, 1) for q in range(2) for r in range(2)]
    return [Program(tuple(pair)) for pair in itertools.product(options, repeat=2)]


def test_programs() -> dict[str, int]:
    halts = 0; unresolved = 0
    programs = small_programs()
    for program in programs:
        for start in itertools.product(range(2), range(3), range(3)):
            start = tuple(start)
            path, halted = program.run(start, 32)
            h = history(program, path)
            system = compile_system(program, start)
            w = system.witness(h)
            direct = residual(program, start, h)
            compiled = system.evaluate(w)
            check(compiled[:2] == direct and not any(compiled[2:]), 'compiler equality')
            check(system.accepts(w) == halted, 'clocked execution certificate')
            if halted:
                halts += 1
                check(sum(len(p) for p in h) == len(path), 'exact history support')
                check(all(c == 1 for p in w.values() for c in p.values()), 'binary witness')
                unclocked = compile_system(program, start, False)
                check(unclocked.accepts(unclocked.witness(history(program, path, False))),
                      'unclocked certificate')
                # A single altered coefficient cannot be another clocked solution.
                mutated = {var: dict(p) for var, p in w.items()}
                mutated['H0'] = add(mutated['H0'], {(0, 0, 0): 1})
                check(not system.accepts(mutated), 'coefficient mutation rejected')
            else:
                unresolved += 1
                nxt = program.step(path[-1]); assert nxt is not None
                expected = [{} for _ in program.instructions]
                expected[nxt[0]] = {(nxt[1], nxt[2], len(path)): -1}
                check(direct == expected, 'retained final spill')
            for modulus in (2, 3, 5, 6):
                check(system.accepts(w, modulus) == halted, 'characteristic independence')
        # Independent coefficient solver includes all spill rows.
        for start in itertools.product(range(2), range(2), range(2)):
            start = tuple(start)
            rank, columns, consistent = gf2_bounded_solve(program, start, 1, 1, 2)
            path, halted = program.run(start, 2)
            inside = all(c[1] <= 1 and c[2] <= 1 for c in path)
            check(rank == columns, 'independent GF2 injectivity')
            check(consistent == (halted and inside), 'independent GF2 feasibility')
    return {'programs': len(programs), 'simulation_instances': halts+unresolved,
            'halting_within_32': halts, 'not_halting_within_32': unresolved,
            'independent_finite_box_systems': len(programs)*8}


def test_relaxation() -> None:
    infinite = Program((Instruction('INC', 0, 0),))
    for n in range(31):
        path, halted = infinite.run((0, 0, 0), n)
        h = history(infinite, path)
        for p in h:
            for e in list(p):
                p[e] = Fraction(n+1-e[2], n+2)
        check(energy(infinite, (0, 0, 0), h) == Fraction(1, n+2),
              'rational taper energy')
        check(sum(c*c for p in h for c in p.values()) ==
              Fraction((n+1)*(2*n+3), 6*(n+2)), 'taper norm')
    # Enumerate small signed integer coefficient boxes on one nonhalting orbit.
    for n in range(5):
        for coeffs in itertools.product((-1, 0, 1, 2), repeat=n+1):
            value = (coeffs[0]-1)**2+coeffs[-1]**2
            value += sum((coeffs[i]-coeffs[i-1])**2 for i in range(1, n+1))
            check(value >= 1, 'integer energy gap')
    # Verify expanded quadratic form independently on random finite arrays.
    rng = random.Random(53)
    for program in (TRANSFER, FALSE_BOUNDARY, infinite):
        for _ in range(120):
            nodes = {(rng.randrange(len(program.instructions)), rng.randrange(3),
                      rng.randrange(3), rng.randrange(4)): rng.randrange(-3, 4)
                     for _ in range(20)}
            nodes = {v:c for v,c in nodes.items() if c}
            h = [{} for _ in program.instructions]
            for (q,a,b,t), c in nodes.items(): h[q][(a,b,t)] = c
            value = 1-2*nodes.get((0,0,0,0), 0)
            images: dict[Node, list[Coeff]] = {}
            for v,c in nodes.items():
                nxt = program.step(v[:3])
                value += c*c*(1+int(nxt is not None))
                if nxt is not None:
                    w = (*nxt, v[3]+1)
                    value -= 2*c*nodes.get(w, 0)
                    images.setdefault(w, []).append(c)
            for coefficients in images.values():
                value += 2*sum(a*b for a,b in itertools.combinations(coefficients, 2))
            check(value == energy(program, (0,0,0), h), 'expanded convex quadratic')


def test_adversarial_and_export() -> None:
    system = compile_system(FALSE_BOUNDARY, (0,1,0))
    fake = {'H0': {(1,0,0): 1}, 'H1': {}, 'H2': {(1,0,1): 1},
            'D0': {}, 'B0': {(1,0,0): 1}}
    check(not any(system.evaluate(fake, enforce_sorts=False)), 'relaxed boundary false positive')
    rejected = False
    try: system.evaluate(fake)
    except ValueError: rejected = True
    check(rejected, 'boundary sort blocks false positive')
    path, halted = FALSE_BOUNDARY.run((0,1,0), 6)
    check(not halted and path[0] == path[2], 'false-positive source is periodic')
    # Without the clock, a disconnected directed cycle adds a kernel vector.
    p = Program((Instruction('HALT'), Instruction('TEST',0,0,1)))
    base = [{(0,0,0): 1}, {}]
    with_cycle = [{(0,0,0): 1}, {(0,3,0): 7}]
    check(not any(residual(p, (0,0,0), base, False)), 'unclocked base')
    check(not any(residual(p, (0,0,0), with_cycle, False)), 'unclocked cycle kernel')
    check(any(residual(p, (0,0,0), with_cycle)), 'clock removes cycle kernel')
    for make in (lambda: Program(()),
                 lambda: Program((Instruction('INC',0,4),)),
                 lambda: Program((Instruction('TEST',2,0,0),)),
                 lambda: clean({(-1,0,0):1}),
                 lambda: TRANSFER.step((0,-1,0)),
                 lambda: Program((Instruction('INC',0,0.5),)),
                 lambda: Program((Instruction('TEST',True,0,0),)),
                 lambda: Program(('HALT',)),
                 lambda: clean({(0,0,0):1}, 2.5),
                 lambda: shift({(0,0,0):1}, (0,0,0,1)),
                 lambda: shift({(-1,0,0):1}, (1,0,0)),
                 lambda: split({}, 0.0),
                 lambda: gf2_bounded_solve(TRANSFER,(0,0,0),1,1,1.5)):
        rejected = False
        try: make()
        except (ValueError, TypeError): rejected = True
        check(rejected, 'invalid inputs rejected')
    mutable = [Instruction('HALT')]
    frozen = Program(mutable)
    mutable[0] = Instruction('INC',0,0)
    check(frozen.step((0,0,0)) is None, 'constructor snapshots mutable input')
    system = compile_system(TRANSFER, (0,2,0))
    path, halted = TRANSFER.run((0,2,0), 20)
    witness = system.witness(history(TRANSFER, path))
    (ROOT/'examples'/'transfer_equation.txt').write_text(system.tagged_equation())
    output = {'program': [i.__dict__ for i in TRANSFER.instructions], 'input': [0,2,0],
              'path': path, 'halt_time': len(path)-1,
              'sorts': {k: sorted(v) for k,v in system.sorts.items()},
              'witness': {k: [{'exponent': e, 'coefficient': c} for e,c in p.items()]
                          for k,p in witness.items()}}
    (ROOT/'examples'/'transfer_certificate.json').write_text(json.dumps(output, indent=2)+'\n')
    (ROOT/'examples'/'transfer_witness.txt').write_text('\n'.join(
        f'{k} = {poly_text(v)}' for k,v in witness.items())+'\n')


def main() -> None:
    test_operators()
    statistics = test_programs()
    test_relaxation()
    test_adversarial_and_export()
    report = {'status':'PASS', 'seed':20261002, 'arithmetic':'exact integers, rationals, and modular rings',
              'moduli':[2,3,5,6], 'statistics':statistics,
              'checks_by_group':COUNTS, 'total_checks':sum(COUNTS.values()),
              'limitations':['Finite tests are not a proof of universal correctness.',
                             'No numerically instantiated fixed universal machine is included.',
                             'Runs not halting within 32 transitions are not classified as divergent.']}
    (ROOT/'validation'/'test_results.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))

if __name__ == '__main__': main()
