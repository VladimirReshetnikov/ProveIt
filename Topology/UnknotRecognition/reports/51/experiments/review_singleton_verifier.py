"""Independent small exhaustive review of the version-eight local replay rule."""
from copy import deepcopy
from hashlib import sha256
from itertools import product
import json
from pathlib import Path
import sys
from unittest.mock import patch

FAST = (Path(sys.argv[1]).resolve() if len(sys.argv) > 1 else
        Path(__file__).resolve().parent.parent /
        'snapshots/final/Topology/UnknotRecognition/fast')
sys.path.insert(0, str(FAST))
from fastunknot.compressed_words import WordArena
from fastunknot.compressed_search import _search
from fastunknot.group_certificate import _Budget
from fastunknot.singleton_dag_verify import (
    replay_compressed_singleton_dag, replay_literal_singleton_dag)


def invert(word):
    return [-value for value in reversed(word)]


def replacement(word, images):
    result = []
    for value in word:
        image = images.get(abs(value), [abs(value)])
        result.extend(image if value > 0 else invert(image))
    return result


def main():
    alphabet = [-3, -2, -1, 1, 2, 3]
    words = [[]] + [[letter] for letter in alphabet]
    words.extend(map(list, product(alphabet, repeat=2)))
    accepted, rejected = 0, 0
    for first, second in product(words, repeat=2):
        source = [first, second, [1, 3, -2, -3, 1, -1]]
        for order in ((1, 2), (2, 1)):
            rank = {child: index + 1 for index, child in enumerate(order)}
            pivots = [dict(relation=child - 1, generator=child) for child in order]
            evidence = dict(kind='singleton_dag', pivots=pivots)
            expected, images = True, {}
            for child in order:
                donor = source[child - 1]
                positions = [i for i, value in enumerate(donor) if abs(value) == child]
                if len(positions) != 1:
                    expected = False
                    break
                position = positions[0]
                body = donor[position + 1:] + donor[:position]
                if any(rank.get(abs(value), 0) >= rank[child] for value in body):
                    expected = False
                    break
                if donor[position] > 0:
                    body = invert(body)
                images[child] = replacement(body, images)
            arena = WordArena()
            roots = [arena.from_word(word) for word in source]
            original_roots = roots[:]
            alive = {1, 2, 3}
            literal, literal_alive = deepcopy(source), alive.copy()
            assert replay_compressed_singleton_dag(arena, roots, alive, evidence) == expected
            assert replay_literal_singleton_dag(literal, literal_alive, evidence,
                _Budget(lambda: None, 100000, 1000000)) == expected
            if expected:
                accepted += 1
                wanted = [[], [], replacement(source[2], images)]
                assert [list(arena.expand(root)) for root in roots] == wanted
                assert literal == wanted
                assert alive == literal_alive == {3}
            else:
                rejected += 1
                assert roots == original_roots and alive == {1, 2, 3}
                assert literal == source and literal_alive == {1, 2, 3}
    # Partial candidates must preserve a raw state and its later normalization
    # boundary. This rank-two endpoint is deliberately not an unknot certificate.
    traces = []
    for enabled in (False, True):
        arena = WordArena()
        roots = [arena.from_word(word) for word in
                 [[1, -2], [2, -3], [1, 4, -1, -4]]]
        alive, moves, terminal = {1, 2, 3, 4}, [], {}
        with patch('fastunknot.singleton_dag.apply_singleton_dag', side_effect=AssertionError):
            result = _search(arena, roots, alive, moves, primitive_terminal=terminal,
                             primitive_forest=True, singleton_dag=enabled)
        traces.append((result, [list(arena.expand(root)) for root in roots], alive, moves, terminal))
    assert traces[0] == traces[1]
    assert not traces[0][0]
    assert [move['kind'] for move in traces[0][3]] == ['primitive_forest', 'normalize_relators']
    print(json.dumps(dict(accepted=accepted, rejected=rejected, cases=accepted + rejected,
        partial_dispatch_preserves_raw_handoff=True,
        source_sha256=sha256((FAST / 'fastunknot/singleton_dag_verify.py').read_bytes()).hexdigest()),
        indent=2))


if __name__ == '__main__':
    main()
