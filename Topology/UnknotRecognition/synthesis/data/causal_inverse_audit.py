"""Reproduce the support-memory counterexample to immediate-inverse pruning.

Run with python -B synthesis/data/causal_inverse_audit.py from the unknot root.
This is an abstract reversible Boolean system, not an RIII knot example.
The independent exhaustive enumeration is compared with report 27's prototype.
"""
import hashlib
import itertools
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
ARCHIVE = ROOT / "reports/27"
sys.path.insert(0, str(ARCHIVE))
from prototype.causal_search import (BooleanLocalSystem, Move, Reduction,
                                    birth_front_unlock)


def main():
    system = BooleanLocalSystem(4, (
        Move("A", frozenset(range(4)), frozenset((0, 1)), ((2, 0), (3, 0))),
        Move("B", frozenset((0, 2)), frozenset((2,)), ((0, 0),)),
        Move("C", frozenset((1, 3)), frozenset((3,)), ((1, 0),)),
    ), (Reduction("finish", frozenset((2, 3)), ((2, 1), (3, 1))),))

    # Enumerate all words without the prototype's normal-form/memo machinery.
    witnesses = []
    for length in range(1, 5):
        for word in itertools.product(system.moves, repeat=length):
            state, active, births = 0, set(), 0
            for index, move in enumerate(word):
                if not move.legal(state):
                    break
                births += active.isdisjoint(move.support)
                active.update(move.support)
                state = move.apply(state)
                if system.legal_reductions(state):
                    if index == length - 1:
                        names = tuple(m.name for m in word)
                        witnesses.append((names, births))
                    break
    bounded = [names for names, births in witnesses if births <= 1]
    inverse_pruned = [names for names in bounded
                      if all(a != b for a, b in zip(names, names[1:]))]
    actual = birth_front_unlock(system, 0, 4, 1)
    assert set(bounded) == {("A", "A", "B", "C"), ("A", "A", "C", "B")}
    assert not inverse_pruned
    assert actual.trace in bounded
    assert ("B", "C") in [names for names, births in witnesses if births == 2]
    result = {
        "scope": "four-site abstract involutions; not an RIII knot counterexample",
        "max_depth": 4, "max_births": 1,
        "moves": [{"name": m.name, "support": sorted(m.support),
                   "toggle": sorted(m.toggle), "guard": m.guard} for m in system.moves],
        "bounded_first_unlock_traces": bounded,
        "immediate_inverse_pruned_traces": inverse_pruned,
        "archive_prototype_trace": actual.trace,
        "archive_prototype_explored": actual.explored_nodes,
        "source_sha256": {
            str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in (Path(__file__), ARCHIVE / "prototype/causal_search.py",
                         ARCHIVE / "integration/clustered_r3_snippet.py")},
    }
    target = Path(__file__).with_name("causal-inverse-audit.json")
    target.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
