"""Finite diagnostics for the unit-composition lemma, not its general proof.

An edge is None (constant bound) or (surviving_label, next_coordinate).
The graph is traced from the OUTERMOST operation to the innermost one.
The mathematical proof for every dimension is in theory/obstruction.tex.
"""
import itertools
import json
from pathlib import Path


def surviving_word(edges, start, length):
    letters = []
    coordinate = start
    for _ in range(length):
        edge = edges[coordinate]
        if edge is None:
            return None
        label, coordinate = edge
        letters.append(label)
    return tuple(letters)


def collapse_word(edges):
    dimension = len(edges)
    length = dimension.bit_length()
    survivors = {surviving_word(edges, i, length)
                 for i in range(dimension)}
    for word in itertools.product((0, 1), repeat=length):
        if word not in survivors:
            return word
    raise ValueError('Pigeonhole claim failed')


def independent_trace(edges, coordinate, word):
    """Check a candidate word without generating surviving words."""
    for step, letter in enumerate(word, 1):
        edge = edges[coordinate]
        if edge is None:
            return {'constant_at_step': step}
        required, coordinate = edge
        if letter != required:
            return {'mismatch_at_step': step}
    raise ValueError('Input dependence survived the entire word')


def run():
    counts = {}
    for dimension in range(1, 5):
        options = [None] + list(itertools.product((0, 1), range(dimension)))
        count = 0
        for edges in itertools.product(options, repeat=dimension):
            word = collapse_word(edges)
            if not 2 ** len(word) > dimension:
                raise ValueError('Word length is insufficient')
            for coordinate in range(dimension):
                independent_trace(edges, coordinate, word)
            count += 1
        counts[str(dimension)] = count
    examples = []
    for dimension in [5, 8, 16, 31, 32]:
        for shift in [0, 1, 3]:
            edges = tuple((i % 2, (i + shift) % dimension)
                          for i in range(dimension))
            word = collapse_word(edges)
            traces = [independent_trace(edges, i, word)
                      for i in range(dimension)]
            examples.append({'dimension': dimension, 'shift': shift,
                             'word_outer_to_inner': list(word),
                             'traces': traces})
    receipt = {
        'scope': 'Finite graph diagnostics; the general theorem is a written proof.',
        'exhaustive_graph_counts': counts,
        'exhaustive_graph_total': sum(counts.values()),
        'larger_examples': examples,
        'passed': True,
    }
    destination = Path(__file__).resolve().parent / 'evidence/obstruction_diagnostics.json'
    destination.write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({'exhaustive_graphs': sum(counts.values()),
                      'larger_examples': len(examples), 'passed': True}))
    return receipt


if __name__ == '__main__':
    run()
