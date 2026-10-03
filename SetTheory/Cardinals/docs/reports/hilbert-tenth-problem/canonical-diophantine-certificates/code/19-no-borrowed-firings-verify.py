#!/usr/bin/env python3
"""Reproducible exact finite checks. Run: python verify.py

Only the Python standard library is used. Reports distinguish semantic
exhaustion, compiled witness checks, bounded rank searches, and polynomial
identity evaluations. No test is advertised as a proof for all inputs.
"""
from __future__ import annotations
from itertools import combinations, product
from pathlib import Path
import json
import platform
import random
import time
from sandpile_certificates import (
    Graph, Certificate, Poly, compile_graph, graph_assignment, stabilize,
    final_state, burning_ranks, rank_conditions, ge_values,
    cube_graph, compile_cube, cube_assignment, lattice_neighbors,
    PeriodicInput, compile_periodic_cube, field_witness_from_cube,
    verify_field_witness, serialize_field_witness, read_field_witness, field_residuals_at, field_tail,
)

ROOT = Path(__file__).resolve().parent


def forbidden_subset(graph: Graph, u: tuple[int, ...], s: tuple[int, ...]) -> bool:
    active = [i for i, value in enumerate(u) if value]
    for mask in range(1, 1 << len(active)):
        subset = [active[k] for k in range(len(active)) if mask & (1 << k)]
        if all(s[i] < sum(graph.adjacency[i][j] for j in subset) for i in subset):
            return True
    return False


def small_graphs():
    for n in range(1, 4):
        edges = list(combinations(range(n), 2))
        for edge_values in product(range(2), repeat=len(edges)):
            a = [[0] * n for _ in range(n)]
            for (i, j), value in zip(edges, edge_values):
                a[i][j] = a[j][i] = value
            for sink in product(range(2), repeat=n):
                try:
                    graph = Graph(tuple(map(tuple, a)), sink)
                except ValueError:
                    continue
                if graph.all_components_dissipative():
                    yield graph


def main() -> None:
    started = time.perf_counter()
    stats: dict[str, object] = {"python": platform.python_version(), "seed": 20261002}
    # The gadget truth tables are checked independently of the compiler.
    nz_cases = 0
    for x in range(21):
        solutions = [(z, a) for z in range(3) for a in range(22)
                     if z * (z - 1) == 0 and x - z * (a + 1) == 0 and (1 - z) * a == 0]
        assert solutions == [(int(x > 0), max(x - 1, 0))]
        nz_cases += 1
    ge_cases = 0
    for x, y in product(range(-3, 6), repeat=2):
        solutions = [(b, p, q) for b in range(3) for p in range(10) for q in range(10)
                     if b * (b - 1) == 0 and x - y - b * p + (1 - b) * (q + 1) == 0
                     and (1 - b) * p == 0 and b * q == 0]
        assert solutions == [ge_values(x, y)]
        ge_cases += 1
    stats.update(nz_input_cases=nz_cases, ge_input_pairs=ge_cases)

    graphs = inputs = candidates = stable_candidates = compiled = 0
    rank_assignments = rank_instances = 0
    for graph in small_graphs():
        graphs += 1
        for chips in product(range(5), repeat=graph.n):
            inputs += 1
            u, s = stabilize(graph, chips)
            r = burning_ranks(graph, u, s)
            assert rank_conditions(graph, u, s, r)
            assert final_state(graph, chips, u) == s
            for candidate in product(range(4), repeat=graph.n):
                candidates += 1
                final = final_state(graph, chips, candidate)
                if not all(0 <= final[i] < graph.degree[i] for i in range(graph.n)):
                    continue
                stable_candidates += 1
                no_fsc = not forbidden_subset(graph, candidate, final)
                assert no_fsc == (candidate == u)
            if inputs % 17 == 0 or graph.n == 1:
                cert = compile_graph(graph, chips)
                values = cert.vector(graph_assignment(graph, chips, u))
                assert not any(cert.evaluate(values))
                assert max(f.degree for f in cert.residuals) == 2
                compiled += 1
            if graph.n <= 2 or inputs % 113 == 0:
                found = []
                for trial_r in product(range(graph.n + 2), repeat=graph.n):
                    rank_assignments += 1
                    if rank_conditions(graph, u, s, trial_r):
                        found.append(trial_r)
                assert found == [r]
                rank_instances += 1
    stats.update(undirected_dissipative_graphs=graphs, initial_configurations=inputs,
                 candidate_odometer_vectors=candidates, stable_balance_candidates=stable_candidates,
                 compiled_valid_witnesses=compiled, rank_instances=rank_instances,
                 rank_assignments=rank_assignments)

    # A multigraph that is outside the simple-graph exhaustion.
    multigraph = Graph(((0, 3, 0), (3, 0, 2), (0, 2, 0)), (1, 0, 2))
    for chips in ((31, 17, 9), (0, 0, 0), (4, 5, 4)):
        cert = compile_graph(multigraph, chips)
        assert not any(cert.evaluate(cert.vector(graph_assignment(multigraph, chips))))
    stats["additional_multigraph_cases"] = 3

    graph = Graph(((0, 1), (1, 0)), (1, 1))
    assert final_state(graph, (1, 1), (1, 1)) == (0, 0)
    assert stabilize(graph, (1, 1))[0] == (0, 0)
    assert forbidden_subset(graph, (1, 1), (0, 0))
    for r in product(range(5), repeat=2):
        assert not rank_conditions(graph, (1, 1), (0, 0), r)
    # The quartic alone over Z has a false root: negative masked slacks.
    phantom_cert = compile_graph(graph, (1, 1))
    signed = {}
    for i in range(2):
        values = dict(u=1, s=0, sigma=1, z=1, alpha=0, r=1, k=0, e=0, beta=0, lam=-1, mu=0)
        signed.update({f"v{i}.{name}": value for name, value in values.items()})
        j = 1-i
        for prefix, triple in (("a", (1, 0, 0)), ("b", (1, 1, 0))):
            signed.update({f"{prefix}{i}_{j}.{name}": value for name, value in zip(("b", "p", "q"), triple)})
    signed_values = [signed[name] for name in phantom_cert.variables]
    assert phantom_cert.quartic().evaluate(signed_values) == 0
    try:
        phantom_cert.evaluate(signed_values)
        raise AssertionError("Signed witnesses were accepted as natural")
    except ValueError:
        pass
    # Full-vertex burning would wrongly reject this perfectly legal no-fire case.
    assert burning_ranks(graph, (0, 0), (0, 0)) == (0, 0)
    assert forbidden_subset(graph, (1, 1), (0, 0))

    # Closed component: one chip circulates forever. Budget failure is explicit.
    closed = Graph(((0, 1), (1, 0)), (0, 0))
    try:
        stabilize(closed, (1, 0), max_batches=20)
        raise AssertionError("Expected an explicit unknown result")
    except TimeoutError:
        pass
    for u in product(range(6), repeat=2):
        s = final_state(closed, (1, 0), u)
        assert not all(0 <= x < 1 for x in s)

    # Directed counterexample: outgoing degrees (1,3), incoming adjacency below.
    incoming = ((0, 2), (1, 0))
    d, c, u, s, r = (1, 3), (0, 2), (2, 1), (0, 1), (2, 1)
    assert all(c[i] < d[i] for i in range(2))
    assert tuple(c[i] - d[i] * u[i] + sum(incoming[i][j] * u[j] for j in range(2))
                 for i in range(2)) == s
    for i in range(2):
        assert s[i] >= sum(incoming[i][j] for j in range(2) if r[j] >= r[i])
        if r[i] > 1:
            assert s[i] < sum(incoming[i][j] for j in range(2) if r[j] >= r[i] - 1)
    try:
        Graph(incoming, (0, 1))
        raise AssertionError("Asymmetric input was accepted")
    except ValueError:
        pass
    # Constructor makes defensive copies.
    source_a, source_sink = [[0, 1], [1, 0]], [1, 1]
    copied = Graph(source_a, source_sink)
    source_a[0][1] = 7
    source_sink[0] = 100
    assert copied == graph

    sample = compile_graph(graph, (3, 1))
    assignment = graph_assignment(graph, (3, 1))
    witness = sample.vector(assignment)
    polynomial = sample.quartic()
    assert polynomial.degree == 4
    assert polynomial.evaluate(witness) == 0
    mutations = 0
    for i, value in enumerate(witness):
        for delta in (-1, 1):
            if value + delta >= 0:
                changed = list(witness)
                changed[i] += delta
                residual_energy = sum(z * z for z in sample.evaluate(changed))
                assert residual_energy > 0
                assert polynomial.evaluate(changed) == residual_energy
                mutations += 1
    rng = random.Random(20261002)
    for _ in range(250):
        values = [rng.randrange(7) for _ in witness]
        assert polynomial.evaluate(values) == sum(z * z for z in sample.evaluate(values))
    stats.update(worked_example_variables=len(witness), worked_example_residuals=len(sample.residuals),
                 worked_example_quartic_degree=polynomial.degree,
                 worked_example_quartic_monomials=len(polynomial.terms),
                 single_coordinate_mutations_rejected=mutations,
                 expanded_polynomial_random_identity_checks=250)

    (ROOT / "examples").mkdir(exist_ok=True)
    (ROOT / "examples/two_vertex_certificate.json").write_text(
        json.dumps(sample.serialize(expand_quartic=True), indent=2) + "\n")
    (ROOT / "examples/two_vertex_witness.json").write_text(
        json.dumps(assignment, indent=2) + "\n")

    cube_cases = 0
    for dimension in (1, 2, 3):
        for radius in (0, 1, 2):
            cert, g, points, halo = compile_cube(dimension, radius, lambda _: 0)
            ell = 2 * radius + 1
            assert len(cert.variables) == (11 + 12 * dimension) * ell ** dimension - 10 * dimension * ell ** (dimension - 1)
            assert len(cert.residuals) == (12 + 16 * dimension) * ell ** dimension - 14 * dimension * ell ** (dimension - 1)
            assert len(halo) == 2 * dimension * ell ** (dimension - 1)
            assert not any(cert.evaluate(cert.vector(cube_assignment(g, points, halo, lambda _: 0))))
            cube_cases += 1
    # Finite avalanche, zero background. Compare two externally chosen cubes.
    eta = lambda x: 100 if all(a == 0 for a in x) else 0
    avalanche_data = []
    for radius in (2, 3):
        cert, g, points, halo = compile_cube(3, radius, eta)
        a = cube_assignment(g, points, halo, eta)
        assert not any(cert.evaluate(cert.vector(a)))
        profile = {x: a[f"v{i}.u"] for i, x in enumerate(points) if a[f"v{i}.u"]}
        ranks = {x: a[f"v{i}.r"] for i, x in enumerate(points) if a[f"v{i}.r"]}
        assert 2 * max(profile.values()) <= 100 * (radius + 1) ** 2
        avalanche_data.append((profile, ranks))
    assert avalanche_data[0] == avalanche_data[1]
    profile, ranks = avalanche_data[0]
    stats.update(cube_count_and_zero_witness_checks=cube_cases,
                 finite_avalanche_supported_vertices=len(profile),
                 finite_avalanche_total_topplings=sum(profile.values()),
                 finite_avalanche_max_odometer=max(profile.values()),
                 finite_avalanche_max_burning_rank=max(ranks.values()),
                 padding_comparison_radii=[2, 3])
    (ROOT / "examples/three_dimensional_avalanche.json").write_text(json.dumps({
        "input": "100 chips at origin, zero elsewhere", "ambient_dimension": 3,
        "profile": [{"site": x, "odometer": profile[x], "burning_rank": ranks[x]}
                    for x in sorted(profile)]}, indent=2) + "\n")
    leaky = lambda x: 6 if x == (0, 0, 0) else 5
    cert, g, points, halo = compile_cube(3, 0, leaky)
    assert stabilize(g, (6,)) == ((1,), (0,))
    try:
        cube_assignment(g, points, halo, leaky)
        raise AssertionError("The leaking halo was accepted")
    except ValueError:
        pass
    # Periodic field tails: local vertex residuals and all directed comparators.
    tail_checks = 0
    for b in range(6):
        u = z = alpha = r = k = e = beta = lam = mu = 0
        s, sigma = b, 5 - b
        vertex = [s - b + 6*u, s + sigma - 5, z*(z-1), u-z*(alpha+1),
                  (1-z)*alpha, r-z-k, (1-z)*k, e*(e-1), k-e*(beta+1),
                  (1-e)*beta, lam-z*(s-6), mu-e*(6-s-1)]
        assert vertex == [0]*12
        for _ in range(6):
            assert ge_values(0, 0) == (1, 0, 0)
            assert ge_values(0, -1) == (1, 1, 0)
        tail_checks += 1
    stats["local_periodic_tail_height_cases"] = tail_checks
    periodic = PeriodicInput((2, 1, 1), (0, 1), (((0, 0, 0), 100),))
    pc, pg, pp, ph = compile_periodic_cube(periodic, 3)
    assert not any(pc.evaluate(pc.vector(cube_assignment(pg, pp, ph, periodic.value))))
    assert periodic.value((-1, 0, 0)) == 1
    try:
        PeriodicInput((1, 1, 1), (6,))
        raise AssertionError("Unstable background accepted")
    except ValueError:
        pass
    outside = PeriodicInput((1, 1, 1), (0,), (((4, 0, 0), 1),))
    try:
        compile_periodic_cube(outside, 3)
        raise AssertionError("An out-of-cube perturbation was accepted")
    except ValueError:
        pass
    stats["effective_periodic_input_validation_checks"] = 4
    field_input = PeriodicInput((1, 1, 1), (0,), (((0, 0, 0), 100),))
    fields = field_witness_from_cube(field_input, 2)
    assert fields == field_witness_from_cube(field_input, 3)
    assert verify_field_witness(field_input, fields)
    assert len(field_residuals_at(field_input, fields, (0, 0, 0))) == 60
    assert all(len(v) == 47 for v in fields.values())
    document = serialize_field_witness(field_input, fields)
    assert read_field_witness(json.loads(json.dumps(document))) == (field_input, fields)
    field_mutations = 0
    for x in list(fields)[:10]:
        for i in (0, 1, 5, 11, 46):
            mutated = dict(fields)
            values = list(fields[x])
            values[i] += 1
            mutated[x] = tuple(values)
            assert not verify_field_witness(field_input, mutated)
            field_mutations += 1
    for x in list(fields)[:10]:
        mutated = dict(fields)
        del mutated[x]
        assert not verify_field_witness(field_input, mutated)
    duplicated = json.loads(json.dumps(document))
    duplicated["exceptions"].insert(0, duplicated["exceptions"][0])
    try:
        read_field_witness(duplicated)
        raise AssertionError("Duplicate serialized sites were accepted")
    except ValueError:
        pass
    redundant = dict(fields)
    redundant[(99, 0, 0)] = field_tail(field_input, (99, 0, 0))
    assert not verify_field_witness(field_input, redundant)
    stable_input = PeriodicInput((2, 1, 1), (0, 5))
    assert field_witness_from_cube(stable_input, 0) == {}
    assert verify_field_witness(stable_input, {})
    (ROOT / "examples/three_dimensional_field_certificate.json").write_text(
        json.dumps(document, indent=2) + "\n")
    stats.update(field_witness_arity=47, field_local_residual_count=60,
                 field_exception_sites=len(fields), field_coordinate_mutations_rejected=field_mutations,
                 field_exception_deletions_rejected=10, field_canonical_serialization_checks=4)
    stats["adversarial_checks"] = [
        "stable balance phantom firing rejected", "signed false root excluded by the natural domain",
        "support-only burning required",
        "closed-graph budget exhaustion reported unknown", "directed false positive and API rejection",
        "defensive graph input copying", "six unstable halo sites rejected",
        "padding preserves the finite-support profile and canonical ranks"]
    stats["status"] = "PASS"
    stats["elapsed_seconds"] = round(time.perf_counter() - started, 3)
    (ROOT / "verification").mkdir(exist_ok=True)
    (ROOT / "verification/results.json").write_text(json.dumps(stats, indent=2) + "\n")
    lines = ["EXACT FINITE VERIFICATION — " + str(stats["status"])]
    lines += [f"{k}: {v}" for k, v in stats.items()]
    (ROOT / "verification/results.txt").write_text("\n".join(lines) + "\n")
    print("\n".join(lines))


if __name__ == "__main__":
    main()
