"""Reproducible independent integer-cofactor audit of every evolving suffix."""
import argparse
import hashlib
import json
from pathlib import Path
import random
import sys

FAST = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(FAST))
from fastunknot.diagram import Diagram
from fastunknot.streaming_response import compile_suffix_responses
from tests.test_streaming_response import cofactor, independent_suffix_graph


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--attempts", type=int, default=240)
    args = parser.parse_args()
    rng = random.Random(2026100851)
    result = dict(seed=2026100851, attempts=args.attempts, primes=[2, 3, 5, 101],
                  inputs=[], suffixes=0, field_responses=0, queries=0,
                  singular_responses=0, absorbing_zero_responses=0,
                  max_radical=0, max_boundary=0, max_new_interior=0,
                  streams_with_two_pivots=0, mismatches=0,
                  oracle="independent graph components and integer Bareiss cofactors",
                  scope="arbitrary terminal partitions of actual evolving knot suffixes")
    for _ in range(args.attempts):
        strands = rng.randrange(2, 6)
        word = [rng.choice((-1, 1)) * rng.randrange(1, strands)
                for _ in range(rng.randrange(1, 25))]
        try:
            diagram = Diagram.from_braid(strands, word)
        except ValueError:
            continue
        order = list(range(diagram.crossings))
        rng.shuffle(order)
        result["inputs"].append(dict(strands=strands, word=word, order=order))
        graphs = [independent_suffix_graph(diagram, order, stage)
                  for stage in range(diagram.crossings)]
        result["suffixes"] += len(graphs)
        for prime in result["primes"]:
            snapshots = compile_suffix_responses(diagram.pd, order, prime)
            result["streams_with_two_pivots"] += dict(snapshots[0].stats)["two_pivots"] > 0
            for snapshot, (matrix, owner) in zip(snapshots, graphs):
                state = snapshot.response
                result["field_responses"] += 1
                result["singular_responses"] += state.radical > 0
                result["absorbing_zero_responses"] += state.zero
                result["max_radical"] = max(result["max_radical"], state.radical)
                result["max_boundary"] = max(result["max_boundary"], len(snapshot.labels))
                result["max_new_interior"] = max(result["max_new_interior"],
                                                  dict(state.stats)["max_new_interior"])
                terminals = [owner[v] for v in state.terminals]
                for query in range(8):
                    labels = tuple(range(len(terminals))) if query == 0 else (
                        (0,) * len(terminals) if query == 1 else
                        tuple(rng.randrange(4) for _ in terminals))
                    actual = state.query(labels)
                    expected = cofactor(matrix, terminals, labels, prime)
                    result["queries"] += 1
                    if actual != expected:
                        result["mismatches"] += 1
                        raise AssertionError((diagram.pd, order, prime, snapshot.stage,
                                              labels, actual, expected))
    result["validated_inputs"] = len(result["inputs"])
    result["sources"] = {str(path.relative_to(FAST)): hashlib.sha256(path.read_bytes()).hexdigest()
                          for path in (Path(__file__), FAST / "fastunknot/streaming_response.py",
                                       FAST / "tests/test_streaming_response.py",
                                       FAST / "fastunknot/integer_determinant.py")}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({key: value for key, value in result.items() if key not in ("inputs", "sources")}))


if __name__ == "__main__":
    main()
