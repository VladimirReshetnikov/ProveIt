"""Exact finite-state binary registers. No coordinate expansion or random sampling."""
from __future__ import annotations
from dataclasses import dataclass
from collections.abc import Sequence
from . import gf2


@dataclass(frozen=True)
class Register:
    widths: tuple[int, ...]
    transitions: tuple[tuple[tuple[int, ...], tuple[int, ...]], ...]
    initial: int
    outputs: tuple[int, ...]
    output_count: int

    def __post_init__(self):
        if not self.widths or any(type(b) is not int or b < 1 for b in self.widths):
            raise ValueError('register widths must be positive integers')
        if len(self.transitions) != len(self.widths)-1:
            raise ValueError('wrong transition count')
        gf2.check_rows([self.initial], self.widths[0])
        for j, pair in enumerate(self.transitions):
            if len(pair) != 2:
                raise ValueError('a binary register has exactly two transitions per layer')
            for matrix in pair:
                if len(matrix) != self.widths[j]:
                    raise ValueError('wrong transition height')
                gf2.check_rows(matrix, self.widths[j+1])
        if len(self.outputs) != self.widths[-1]:
            raise ValueError('wrong output height')
        gf2.check_rows(self.outputs, self.output_count)

    @property
    def length(self) -> int:
        return len(self.transitions)

    def evaluate(self, word: Sequence[int]) -> int:
        if len(word) != self.length or any(type(x) is not int or x not in (0, 1) for x in word):
            raise ValueError('word must be a binary tuple of the register length')
        state = self.initial
        for x, pair in zip(word, self.transitions):
            state = gf2.row_mul(state, pair[x])
        return gf2.row_mul(state, self.outputs)

    def reachable(self) -> dict:
        """Span of reachable rows with actual witnesses; at most B per layer.

        Witnesses are shared predecessor nodes, not copied length-j tuples.
        Hence witness bookkeeping is O(m B), not O(m^2 B).
        """
        nodes = [(-1, -1)]
        basis = [(self.initial, 0)] if self.initial else []
        dimensions = [len(basis)]
        candidates_count = 0
        for pair in self.transitions:
            candidates = [(gf2.row_mul(state, pair[x]), parent, x)
                          for state, parent in basis for x in (0, 1)]
            candidates_count += len(candidates)
            selected = gf2.independent_indices([v for v, _, _ in candidates])
            basis = []
            for j in selected:
                value, parent, symbol = candidates[j]
                nodes.append((parent, symbol))
                basis.append((value, len(nodes)-1))
            dimensions.append(len(basis))
        outputs = [(gf2.row_mul(state, self.outputs), node) for state, node in basis]
        selected = gf2.independent_indices([v for v, _ in outputs])
        chosen = [outputs[j] for j in selected]
        witnesses = []
        for _, node in chosen:
            word = []
            while node:
                node, symbol = nodes[node]
                word.append(symbol)
            witnesses.append(list(reversed(word)))
        return {'evaluation_rows': [v for v, _ in chosen],
                'witnesses': witnesses,
                'reachable_dimensions': dimensions,
                'candidate_rows': candidates_count,
                'terminal_state_rows': [v for v, _ in basis]}

    def state_gram(self) -> list[int]:
        """W=sum_x state(x)^T state(x); this is NOT a rank certificate in F_2."""
        w = [self.initial if self.initial >> j & 1 else 0
             for j in range(self.widths[0])]
        for j, pair in enumerate(self.transitions):
            terms = []
            for matrix in pair:
                terms.append(gf2.mul(gf2.transpose(matrix, self.widths[j+1]),
                                     gf2.mul(w, matrix)))
            w = gf2.add(*terms)
        return w

    def to_dict(self) -> dict:
        return {'widths': list(self.widths),
                'transitions': [[list(a), list(b)] for a, b in self.transitions],
                'initial': self.initial, 'outputs': list(self.outputs),
                'output_count': self.output_count}

    @classmethod
    def from_dict(cls, obj: dict) -> 'Register':
        if not isinstance(obj, dict):
            raise ValueError('JSON object required')
        return cls(tuple(obj['widths']),
                   tuple((tuple(a), tuple(b)) for a, b in obj['transitions']),
                   obj['initial'], tuple(obj['outputs']), obj['output_count'])


def product_register(terms: Sequence[Sequence[int]], output_masks: Sequence[int],
                     output_count: int, *, length: int | None = None) -> Register:
    """Each literal is its two-bit truth table: 0,1,2,3 = zero,not-x,x,one.

    A term is a product of literals; output_masks says which functions contain it.
    Unlike expanded algebraic normal form, a point indicator uses one product term.
    """
    if len(terms) != len(output_masks):
        raise ValueError('term/output count mismatch')
    if length is None:
        length = len(terms[0]) if terms else 0
    if type(length) is not int or length < 0:
        raise ValueError('invalid register length')
    if any(len(t) != length or any(type(a) is not int or not 0 <= a <= 3 for a in t)
           for t in terms):
        raise ValueError('invalid product term')
    gf2.check_rows(output_masks, output_count)
    if not terms:
        return Register(tuple([1]*(length+1)), tuple(((1,), (1,)) for _ in range(length)),
                        0, (0,), output_count)
    b = len(terms)
    transitions = []
    for j in range(length):
        transitions.append(tuple(tuple((1 << k) if term[j] >> x & 1 else 0
                                       for k, term in enumerate(terms)) for x in (0, 1)))
    return Register(tuple([b]*(length+1)), tuple(transitions), (1 << b)-1,
                    tuple(output_masks), output_count)
