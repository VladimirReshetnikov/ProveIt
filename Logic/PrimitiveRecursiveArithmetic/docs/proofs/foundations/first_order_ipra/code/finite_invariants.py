"""Executable checks for monadic rank profiles and the one-relation encoding.

Run from any directory with Python 3.10+. No third-party dependencies.
"""
from itertools import combinations_with_replacement, product
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from ef_certificates import Game, Structure


def unary_model(colours, predicate_count):
    if not colours or any(c not in range(2 ** predicate_count) for c in colours):
        raise ValueError("expected a nonempty sequence of p-bit colours")
    relations = tuple(
        frozenset((i,) for i, colour in enumerate(colours) if (colour >> bit) & 1)
        for bit in range(predicate_count)
    )
    return Structure(len(colours), (1,) * predicate_count, relations)


def profile(colours, predicate_count, rank):
    if rank < 0:
        raise ValueError("rank must be nonnegative")
    return tuple(min(rank, colours.count(c)) for c in range(2 ** predicate_count))


def graph_encoding(model):
    """Return a directed graph together with the existential tag witnesses."""
    edges = set()
    next_vertex = model.size

    def fresh():
        nonlocal next_vertex
        v = next_vertex
        next_vertex += 1
        return v

    domain_tag = fresh()
    edges.update((x, domain_tag) for x in range(model.size))
    tags = []
    for arity, table in zip(model.arities, model.relations):
        tuple_tag = fresh()
        coordinates = tuple(fresh() for _ in range(arity))
        tags.append((tuple_tag, coordinates))
        for row in sorted(table):
            witness = fresh()
            edges.add((witness, tuple_tag))
            for slot, element in enumerate(row):
                link = fresh()
                edges.update(((witness, link), (link, coordinates[slot]), (link, element)))
    graph = Structure(next_vertex, (2,), (frozenset(edges),))
    return graph, domain_tag, tags


def graph_decoding(graph, domain_tag, tags):
    """Evaluate the defining edge patterns with the supplied tag assignment."""
    edges = graph.relations[0]
    carrier = [x for x in range(graph.size) if (x, domain_tag) in edges]
    if not carrier:
        raise ValueError("interpreted sort must be inhabited")
    out = [set() for _ in range(graph.size)]
    for x, y in edges:
        out[x].add(y)
    result = []
    for tuple_tag, coordinate_tags in tags:
        tuples = set()
        for v in range(graph.size):
            if (v, tuple_tag) not in edges:
                continue
            choices = [
                [j for j, x in enumerate(carrier)
                 if any((link, tag) in edges and (link, x) in edges for link in out[v])]
                for tag in coordinate_tags
            ]
            tuples.update(product(*choices))
        result.append(frozenset(tuples))
    return Structure(len(carrier), tuple(len(coords) for _, coords in tags), tuple(result))


def check_encoding():
    rows = list(product(range(2), repeat=2))
    cases = 0
    for mask, p in product(range(1 << len(rows)), (False, True)):
        model = Structure(2, (2, 0, 1), (
            frozenset(row for i, row in enumerate(rows) if mask >> i & 1),
            frozenset([()]) if p else frozenset(), frozenset([(1,)])))
        assert graph_decoding(*graph_encoding(model)) == model
        cases += 1
    return cases


def check_profiles():
    samples = [word for n in range(1, 4)
               for word in combinations_with_replacement(range(4), n)]
    models = [unary_model(word, 2) for word in samples]
    cases = 0
    for i, left in enumerate(samples):
        for j, right in enumerate(samples[:i+1]):
            game = Game(models[i], models[j])
            for r in range(3):
                expected = profile(left, 2, r) == profile(right, 2, r)
                actual = game.solve(r) is None
                assert actual == expected, (left, right, r, actual, expected)
                cases += 1
    return cases


if __name__ == "__main__":
    print("Single-binary-relation graph encoding round trips:", check_encoding())
    print("Monadic profile and independent EF game comparisons:", check_profiles())
