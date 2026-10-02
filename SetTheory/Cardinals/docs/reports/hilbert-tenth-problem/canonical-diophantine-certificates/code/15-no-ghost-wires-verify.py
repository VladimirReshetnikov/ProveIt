#!/usr/bin/env python3
"""Reproduce exact finite checks. No packages beyond Python's standard library.

These tests complement, but do not replace, the manuscript's unbounded proofs.
Writes verification.json and a readable receipt into ../data.
"""
from __future__ import annotations
import hashlib
import itertools
import json
from pathlib import Path
import time
from loop_exact import (Net, ARITY, Poly, check_orbit, compile_schedule,
                        glue_components, glue_permutation, obstruction_examples,
                        orbit_witness, permutation_cycles, ports, step, wire,
                        write_example)


def matchings(items: tuple) -> object:
    if not items:
        yield ()
        return
    a = items[0]
    for k in range(1, len(items)):
        b = items[k]
        rest = items[1:k] + items[k + 1:]
        for m in matchings(rest):
            yield ((a, b),) + m


def involutions(items: tuple[int, ...]):
    if not items:
        yield {}
        return
    a = items[0]
    for rest in involutions(items[1:]):
        yield {a: a, **rest}
    for k in range(1, len(items)):
        b = items[k]
        for rest in involutions(items[1:k] + items[k + 1:]):
            yield {a: b, b: a, **rest}


def eliminate(alpha: dict, beta: dict):
    """Third independent gluing implementation: local pair suppression only."""
    partner = alpha.copy()
    loops = 0
    for x in sorted(beta):
        y = beta[x]
        if x >= y:
            continue
        u, v = partner[x], partner[y]
        if u == y:
            assert v == x
            loops += 1
        else:
            partner[u], partner[v] = v, u
        del partner[x], partner[y]
    return tuple(sorted(wire(a, b) for a, b in partner.items() if a < b)), loops


def test_permutations(max_n: int = 8) -> dict:
    count, checked_solutions = 0, 0
    for n in range(max_n + 1):
        for sigma in itertools.permutations(range(n)):
            w = orbit_witness(sigma)
            assert check_orbit(sigma, w)
            assert sum(w['e']) == len(permutation_cycles(sigma))
            count += 1
            if n <= 4:
                # Include spurious label zero, and every distance through n-1.
                domains = []
                for i in range(1, n + 1):
                    domain = [(i, 0, 0, 1)]
                    domain += [(r, d, i - r - 1, 0)
                               for r in range(i) for d in range(n)]
                    domains.append(domain)
                solutions = 0
                for assignment in itertools.product(*domains):
                    checked_solutions += 1
                    rr = [a[0] for a in assignment]
                    dd = [a[1] for a in assignment]
                    if all(rr[i] == rr[sigma[i]] and
                           dd[i] == (1 - assignment[i][3]) * (dd[sigma[i]] + 1)
                           for i in range(n)):
                        solutions += 1
                assert solutions == 1
    return {'permutations_through_size': max_n, 'permutations': count,
            'bounded_uniqueness_through_size': 4,
            'candidate_assignments_in_uniqueness_check': checked_solutions}


def test_gluing(max_n: int = 8) -> dict:
    cases = 0
    digest = hashlib.sha256()
    for n in range(0, max_n + 1, 2):
        V = tuple((i, 0) for i in range(n))
        betas = list(involutions(tuple(range(n))))
        for matching in matchings(V):
            alpha = {x: y for a, b in matching for x, y in ((a, b), (b, a))}
            for raw in betas:
                beta = {(i, 0): (j, 0) for i, j in raw.items()}
                B = tuple(x for x in V if beta[x] == x)
                edges, loops, sigma, ow = glue_permutation(V, alpha, beta, B)
                assert (edges, loops) == glue_components(V, alpha, beta, B)
                assert (edges, loops) == eliminate(alpha, beta)
                assert check_orbit(sigma, ow)
                digest.update(repr((matching, sorted(raw.items()), edges, loops)).encode())
                cases += 1
    return {'maximum_temporary_vertices': max_n, 'gluing_instances': cases,
            'independent_algorithms': ['permutation', 'multigraph traversal',
                                       'sequential pair suppression'],
            'record_sha256': digest.hexdigest()}


def test_local_rules() -> dict:
    cases, polynomial_checks = 0, 0
    rule_counts = {}
    mutation_rejections = 0
    for ta, tb in (('E', 'E'), ('G', 'E'), ('D', 'E'),
                   ('G', 'G'), ('D', 'D'), ('G', 'D')):
        typ = {0: ta, 1: tb}
        for free_count in (0, 2, 4):
            free = tuple((i, 0) for i in range(-free_count, 0))
            aux = tuple(p for p in ports(typ, free) if p not in ((0, 0), (1, 0)))
            compiled = compile_schedule(typ, free, ((0, 1),))
            for remaining in matchings(aux):
                net = Net(typ.copy(), tuple(sorted((wire((0, 0), (1, 0)),) +
                                                   tuple(wire(a, b) for a, b in remaining))),
                          3, free)
                result, _, rec = step(net, (0, 1))
                independent, _, _ = step(net, (0, 1), independent=True)
                assert result.as_dict() == independent.as_dict()
                assert 0 <= rec['added_loops'] <= 2
                if ta != tb or ta == 'E':
                    assert rec['added_loops'] == 0
                values = compiled.witness(net, result)
                assert compiled.system.energy(values) == 0
                polynomial_checks += 1
                rule_counts[rec['rule']] = rule_counts.get(rec['rule'], 0) + 1
                if free_count == 0:
                    # Vary one witness at a time. This is not an exhaustive proof.
                    for name in compiled.system.variables:
                        bad = values.copy()
                        bad[name] += 1
                        assert compiled.system.failed(bad)
                        mutation_rejections += 1
                cases += 1
    return {'contexts': cases, 'by_rule': rule_counts,
            'compiled_quartic_witness_checks': polynomial_checks,
            'single_coordinate_mutations_rejected': mutation_rejections}


def test_four_delta() -> dict:
    cells = {i: 'D' for i in range(4)}
    cases, steps = 0, 0
    for matching in matchings(ports(cells)):
        net = Net(cells.copy(), tuple(sorted(wire(a, b) for a, b in matching)))
        net.validate()
        for pair in net.active_pairs():
            a, _, _ = step(net, pair)
            b, _, _ = step(net, pair, independent=True)
            assert a.as_dict() == b.as_dict()
            steps += 1
        cases += 1
    return {'closed_four_delta_nets': cases, 'enabled_rewrites_checked': steps}


def canonical(net: Net) -> tuple:
    """Small-instance labelled-port isomorphism by exhaustive type-preserving maps."""
    ids = sorted(net.cells)
    best = None
    for order in itertools.permutations(ids):
        rename = {c: i for i, c in enumerate(order)}
        signature = tuple(net.cells[c] for c in order)
        def p(x):
            return (rename[x[0]], x[1]) if x[0] >= 0 else x
        edges = tuple(sorted(wire(p(a), p(b)) for a, b in net.wires))
        key = (signature, edges, net.loops, net.free)
        if best is None or key < best:
            best = key
    return best if best is not None else ((), (), net.loops, net.free)


def test_periodic_net() -> dict:
    n = Net({0: 'D', 1: 'G', 2: 'E', 3: 'E'}, tuple(sorted([
        wire((0, 0), (1, 0)), wire((0, 1), (2, 0)),
        wire((0, 2), (1, 1)), wire((1, 2), (3, 0))])))
    frontier = [(n, 4, [])]
    found = None
    for depth in range(1, 5):
        nxt = []
        for current, alloc, hist in frontier:
            for pair in current.active_pairs():
                new, alloc_new, rec = step(current, pair, alloc)
                history = hist + [pair]
                if depth == 4 and canonical(new) == canonical(n):
                    found = (new, history)
                    break
                nxt.append((new, alloc_new, history))
            if found:
                break
        if found:
            break
        frontier = nxt
    assert found is not None
    target, history = found
    compiled = compile_schedule(n.cells, n.free, history)
    assignment = compiled.witness(n, target)
    assert compiled.system.energy(assignment) == 0
    return {'length': 4, 'schedule': history,
            'initial': n.as_dict(), 'target': target.as_dict(),
            'same_ordered_port_net_up_to_agent_renaming': True,
            'witnesses': len(compiled.system.variables),
            'residuals': len(compiled.system.residuals)}


def test_example(destination: Path) -> dict:
    stats = write_example(destination)
    A, B = obstruction_examples()
    target = Net({}, (), 2)
    compiled = compile_schedule(A.cells, (), ((0, 1), (2, 3)))
    values = compiled.witness(A, target)
    count = 0
    for name in compiled.system.variables:
        for change in (-1, 1):
            if values[name] + change < 0:
                continue
            bad = values.copy()
            bad[name] += change
            assert compiled.system.failed(bad)
            count += 1
    try:
        compiled.witness(B, target)
        raise AssertionError('B unexpectedly reached target')
    except ValueError:
        pass
    B1, _, _ = step(B, (0, 1))
    assert B1.active_pairs() == () and len(B1.cells) == 2 and B1.loops == 0
    bad = values.copy()
    bp = B.partner()
    from loop_exact import scalar
    for a, b in itertools.combinations(ports(B.cells), 2):
        bad[scalar('in', a, b)] = int(bp[a] == b)
    stats.update({'A_witness_mutations_rejected': count,
                  'B_is_stuck_after_first_step': True,
                  'A_witness_with_B_input_energy': compiled.system.energy(bad)})
    return stats


def main() -> None:
    start = time.monotonic()
    destination = Path(__file__).resolve().parents[1] / 'data'
    destination.mkdir(exist_ok=True)
    report = {'status': 'PASS', 'scope': 'finite exact tests; not a formal proof',
              'permutations': test_permutations(),
              'gluing': test_gluing(),
              'all_six_rules': test_local_rules(),
              'four_delta': test_four_delta(),
              'periodic_net': test_periodic_net(),
              'repository_obstruction': test_example(destination)}
    report['runtime_seconds'] = round(time.monotonic() - start, 3)
    report['code_sha256'] = {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                             for p in sorted(Path(__file__).parent.glob('*.py'))}
    (destination / 'verification.json').write_text(json.dumps(report, indent=2) + '\n')
    (destination / 'verification.txt').write_text(
        'NO GHOST WIRES: EXACT FINITE VERIFICATION\n\n' + json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
