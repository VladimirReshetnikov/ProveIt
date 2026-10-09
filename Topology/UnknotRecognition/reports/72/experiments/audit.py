"""Exhaustive and randomized independent checks; run from the package root."""
from __future__ import annotations
import json, platform, random, sys, time
from pathlib import Path
from rooted_disc.kernel import State, Candidate, decorated_states, star_states, feature, dual_row, direct_compatibility, reduce_candidates, binary_rank
from rooted_disc.verify import reference_feature, verify_reduction
from rooted_disc.search_verify import verify_search
from rooted_disc.assembly import solve, enumerate_assignments
from rooted_disc.mesh import replay_pair, replay_assignment
from experiments.common import random_grammar, workload


def run() -> dict:
    rng = random.Random(20261009)
    start = time.perf_counter()
    result = {"seed": 20261009, "python": sys.version, "platform": platform.platform(), "uncharged": [], "charged": [], "rank": []}
    print("exhaustive uncharged", flush=True)
    for r in range(1, 6):
        states = list(decorated_states(r))
        rows = [feature(s) for s in states]
        dual = [dual_row(s) for s in states]
        for s, row in zip(states, rows): assert row == reference_feature(s)
        for i, s in enumerate(states):
            for j, t in enumerate(states):
                assert bool((rows[i] & dual[j]).bit_count() & 1) == direct_compatibility(s, t)
        result["uncharged"].append({"r": r, "states": len(states), "pairs": len(states) ** 2, "rank": binary_rank(rows), "bound": 3 ** (r - 1)})
    print("exhaustive charged", flush=True)
    for r in range(1, 4):
        states = list(decorated_states(r, 4))
        rows = [feature(s) for s in states]
        for s, row in zip(states, rows): assert row == reference_feature(s)
        for target in (0, 1, 2, 3, None):
            dual = [dual_row(s, target) for s in states]
            for i, s in enumerate(states):
                for j, t in enumerate(states):
                    assert bool((rows[i] & dual[j]).bit_count() & 1) == direct_compatibility(s, t, target)
        result["charged"].append({"r": r, "q": 4, "states": len(states), "pair_target_checks": 5 * len(states) ** 2})
    print("rank and sharpness", flush=True)
    for r, q in [(1, 1), (2, 1), (3, 1), (4, 1), (5, 1), (6, 1), (1, 4), (2, 4), (3, 4), (4, 4), (5, 4)]:
        states = [s for s, _, _ in star_states(r, q)]
        for target in ([0] if q == 1 else [0, None]):
            rows = [sum(int(direct_compatibility(s, t, target)) << i for i, t in enumerate(states)) for s in states]
            rank = binary_rank(rows)
            assert rank == q * 3 ** (r - 1)
            result["rank"].append({"r": r, "q": q, "target": target, "rank": rank, "matrix_entries": len(states) ** 2})
    exposed = 0
    for r, q in [(5, 1), (4, 4)]:
        family = list(star_states(r, q))
        bykey = {(word, s.charges[0]): s for s, c, word in family}
        for state, cost, word in family:
            t = bykey[tuple({"R": "G", "G": "R", "B": "B"}[x] for x in word), state.charges[0]]
            feasible = [(c, s) for s, c, _ in family if direct_compatibility(s, t, 0)]
            m = min(c for c, _ in feasible)
            assert [s for c, s in feasible if c == m] == [state]
            exposed += 1
    result["uniquely_exposed_weighted_candidates"] = exposed
    print("weighted randomized", flush=True)
    states = list(decorated_states(4, 4))
    comparisons = 0
    for _ in range(1000):
        chosen = rng.choices(states, k=rng.randrange(1, 75))
        family = [Candidate(s, rng.randrange(-10, 11) * (1 << rng.randrange(0, 130)) + i, (i,)) for i, s in enumerate(chosen)]
        kept, cert = reduce_candidates(family, geometry_key="audit-source")
        assert verify_reduction(family, cert, geometry_key="audit-source")
        for _ in range(10):
            t, target = rng.choice(states), rng.choice([None, 0, 1, 2, 3])
            def optimum(f): return min((c.cost for c in f if direct_compatibility(c.state, t, target)), default=None)
            assert optimum(family) == optimum(kept)
            comparisons += 1
    result["weighted_families"] = 1000; result["weighted_optimum_queries"] = comparisons
    print("literal pair meshes", flush=True)
    meshchecks, triangles, successful = 0, 0, 0
    state_cache = {}
    for _ in range(1000):
        r = rng.randrange(1, 6); q = 1 if r >= 4 else 4
        if (r, q) not in state_cache: state_cache[r, q] = list(decorated_states(r, q, root_good=False))
        states = state_cache[r, q]
        s, t = rng.choice(states), rng.choice(states)
        target = 0 if q == 1 else rng.choice([None, 0, 1, 2, 3])
        flips = tuple(bool(rng.randrange(2)) for _ in range(r))
        m = replay_pair(s, t, flips)
        assert m.succeeds(target) == direct_compatibility(s, t, target)
        meshchecks += 1; triangles += m.triangles; successful += m.succeeds(target)
    result["pair_meshes"] = {"checks": meshchecks, "triangles": triangles, "successes": successful}
    print("complete small languages", flush=True)
    assignments, found, replayed = 0, 0, 0
    for index in range(200):
        g = random_grammar(rng, width=2, layers=2, options=2)
        expected = None
        for w in enumerate_assignments(g):
            m = replay_assignment(g, w); assignments += 1
            if m.succeeds(g.target): expected = m.cost if expected is None else min(expected, m.cost)
        exact, reduced = solve(g, reduced=False), solve(g, reduced=True, certificates=True)
        assert verify_search(g, reduced.as_dict())
        assert exact.cost == reduced.cost == expected
        assert exact.status == reduced.status
        if reduced.witness is not None:
            check = replay_assignment(g, reduced.witness)
            assert check.succeeds(g.target) and check.cost == reduced.cost
            replayed += 1
        found += expected is not None
    result["languages"] = {"grammars": 200, "literal_assignments": assignments, "positive_grammars": found, "positive_witness_replays": replayed, "complete_language_certificates": 200}
    g = workload(3, 4, seed=20261009)
    answer = solve(g, reduced=True, certificates=True)
    assert answer.witness is not None
    literal = replay_assignment(g, answer.witness)
    assert literal.succeeds(g.target) and literal.cost == answer.cost
    Path("examples/workload.json").write_text(json.dumps(g.as_dict(), indent=2) + "\n")
    Path("examples/checked_answer.json").write_text(json.dumps(answer.as_dict(), indent=2) + "\n")
    result["example"] = {"source_sha256": g.digest(), "cost": answer.cost, "witness": answer.witness, "root_euler": literal.root_euler,
                          "root_charge": literal.root_charge, "components": literal.components, "triangles": literal.triangles}
    result["seconds"] = time.perf_counter() - start
    return result

if __name__ == "__main__":
    result = run()
    Path("results/audit.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
