"""All-stage reverse-suffix compilation versus fresh dense setup at every stage.

Both arms compute responses for the same actual diagram and crossing order.
The dense arm uses the same singular-safe arithmetic but independently rebuilds
every cut-face graph.  Its original coloring is computed once per whole arm.
Timings include source preparation and all suffix setups; they exclude query
audit and imports.  These are response compilation timings, not recognition.
"""
import argparse
import hashlib
import json
from pathlib import Path
import random
import statistics
import sys
from time import perf_counter

FAST = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(FAST))
from fastunknot.diagram import Diagram
from fastunknot.streaming_response import StreamingResponse, compile_suffix_responses


def source_palette(diagram):
    alpha = diagram.alpha()
    face = {dart: i for i, cycle in enumerate(diagram.faces()) for dart in cycle}
    adjacent = [set() for _ in diagram.faces()]
    for dart, other in enumerate(alpha):
        adjacent[face[dart]].add(face[other])
    colors, queue = {0: 0}, [0]
    for current in queue:
        for other in adjacent[current]:
            if other not in colors:
                colors[other] = 1 - colors[current]
                queue.append(other)
    return alpha, tuple(colors[face[d]] for d in range(len(alpha)))


def dense_stage(pd, order, stage, alpha, palette, prime, anchor):
    """Independent full-suffix fragment reconstruction and dense elimination."""
    darts = {4 * c + j for c in order[stage:] for j in range(4)}
    neighbors = {d: set() for d in darts}
    for dart in darts:
        other = alpha[dart]
        if other in darts:
            target = 4 * (other // 4) + (other + 1) % 4
            neighbors[dart].add(target)
            neighbors[target].add(dart)
    owner, groups = {}, []
    for start in sorted(darts):
        if start in owner:
            continue
        pending, group = [start], set()
        while pending:
            dart = pending.pop()
            if dart in group:
                continue
            group.add(dart)
            pending.extend(neighbors[dart] - group)
        root = min(group)
        for dart in group:
            owner[dart] = root
        groups.append(root)
    black = tuple(root for root in groups if palette[root])
    boundary = {}
    for crossing in order[stage:]:
        for j, label in enumerate(pd[crossing]):
            if label in boundary:
                boundary.pop(label)
            else:
                boundary[label] = 4 * crossing + j
    keep = {owner[anchor]}
    for dart in boundary.values():
        for face in (owner[dart], owner[4 * (dart // 4) + (dart + 1) % 4]):
            if palette[face]:
                keep.add(face)
    edges = []
    for crossing in order[stage:]:
        slots = [j for j in range(4) if palette[4 * crossing + j]]
        first, second = (owner[4 * crossing + j] for j in slots)
        edges.append((first, second, -1 if slots == [0, 2] else 1))
    state = StreamingResponse.empty(prime).advance(
        black, edges, {v: v for v in black}, tuple(sorted(keep)))
    return state, owner, len(black)


def dense_all(pd, order, prime):
    diagram = Diagram.from_pd(pd)
    alpha, palette = source_palette(diagram)
    anchor = next(4 * order[-1] + j for j in range(4) if palette[4 * order[-1] + j])
    return tuple(dense_stage(diagram.pd, order, stage, alpha, palette, prime, anchor)
                 for stage in range(len(order)))


def audit(streamed, dense, rng):
    queries = singular = zeros = interior_stages = 0
    for snapshot, (fresh, owner, vertices) in zip(streamed, dense):
        state = snapshot.response
        singular += state.radical > 0
        zeros += state.zero
        interior_stages += vertices > len(state.terminals)
        for _ in range(5):
            partition = {v: rng.randrange(4) for v in fresh.terminals}
            first = tuple(partition[owner[v]] for v in state.terminals)
            second = tuple(partition[v] for v in fresh.terminals)
            actual, expected = state.query(first), fresh.query(second)
            if actual != expected:
                raise AssertionError((snapshot.stage, first, second, actual, expected))
            queries += 1
    return dict(queries=queries, singular_stages=singular, zero_stages=zeros,
                nontrivial_interior_stages=interior_stages)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--rounds", type=int, default=3)
    parser.add_argument("--sizes", type=int, nargs="+", default=(16, 32, 64, 128))
    parser.add_argument("--large-stream", type=int, default=2048)
    args = parser.parse_args()
    rng = random.Random(8102026)
    result = dict(seed=8102026, prime=65521, rounds=args.rounds,
                  scope="All suffix response setup on actual diagrams; not recognition",
                  baseline="Independent all-stage dense graphs, same pivot arithmetic",
                  cases=[], large_stream={})
    for size in args.sizes:
        exponent = size // 2
        if exponent % 3 == 0:
            raise ValueError("requested torus braid closure is not a knot")
        diagram = Diagram.from_braid(3, [1, 2] * exponent)
        order = list(range(diagram.crossings))
        cases = [("natural", order)]
        if size <= 64:
            shuffled = order.copy()
            rng.shuffle(shuffled)
            cases.append(("shuffled", shuffled))
        for kind, order in cases:
            # One excluded warmup, also the independent query audit.
            streamed = compile_suffix_responses(diagram.pd, order, result["prime"])
            fresh = dense_all(diagram.pd, order, result["prime"])
            checks = audit(streamed, fresh, rng)
            times = {"stream": [], "dense_a": [], "dense_b": []}
            for _ in range(args.rounds):
                arms = list(times)
                rng.shuffle(arms)
                for arm in arms:
                    start = perf_counter()
                    if arm == "stream":
                        value = compile_suffix_responses(diagram.pd, order, result["prime"])
                    else:
                        value = dense_all(diagram.pd, order, result["prime"])
                    elapsed = perf_counter() - start
                    if len(value) != diagram.crossings:
                        raise AssertionError("missing suffix")
                    times[arm].append(elapsed)
            medians = {arm: statistics.median(values) for arm, values in times.items()}
            stats = dict(streamed[0].stats)
            dense_updates = sum(dict(item[0].stats)["elimination_updates"] for item in fresh)
            stored = sum(len(s.response.matrix) ** 2 for s in streamed)
            record = dict(crossings=diagram.crossings, braid=[1, 2] * exponent,
                          order_kind=kind, order=order, audit=checks, stats=stats,
                          dense_elimination_updates=dense_updates,
                          dense_max_dimension=max(item[2] for item in fresh),
                          stored_field_elements=stored, times=times, medians=medians,
                          speedup=medians["dense_a"] / medians["stream"],
                          control_ratio=medians["dense_a"] / medians["dense_b"])
            result["cases"].append(record)
            print(json.dumps({key: record[key] for key in
                              ("crossings", "order_kind", "medians", "speedup", "control_ratio")}))
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(json.dumps(result, indent=2) + "\n")
    exponent = args.large_stream // 2
    if exponent % 3 == 0:
        exponent += 1
    diagram = Diagram.from_braid(3, [1, 2] * exponent)
    start = perf_counter()
    large = compile_suffix_responses(diagram.pd, prime=result["prime"])
    result["large_stream"] = dict(crossings=diagram.crossings,
                                   seconds=perf_counter() - start,
                                   stats=dict(large[0].stats),
                                   stored_field_elements=sum(len(s.response.matrix) ** 2 for s in large))
    result["sources"] = {str(path.relative_to(FAST)): hashlib.sha256(path.read_bytes()).hexdigest()
                          for path in (Path(__file__), FAST / "fastunknot/streaming_response.py")}
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result["large_stream"]))


if __name__ == "__main__":
    main()
