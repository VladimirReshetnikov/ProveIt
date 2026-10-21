#!/usr/bin/env python3
"""Independent structural and finite check of the 25-leaf fused transfer.

No repository or generator module is imported.  The all-natural proof is
in fused_transfer_review.md; the bounded execution loop is corroboration.
"""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
EXPECTED = [
    ('CD', 1, (2, 1)), ('CC', 1, (0,)),
    ('CD', 5, (11, 3)), ('CI', 1, (4,)),
    ('CD', 5, (10, 5)), ('CI', 1, (6,)),
    ('CD', 5, (9, 7)), ('CI', 1, (8,)),
    ('CC', 2, (6,)), ('CB', 1, (11,)), ('CH', None, ()),
    ('CD', 2, (19, 12)), ('CI', 7, (13,)),
    ('CD', 6, (15, 14)), ('CB', 1, (18,)),
    ('CD', 7, (18, 16)), ('CI', 6, (17,)),
    ('CC', 2, (15,)), ('CC', 3, (11,)),
    ('CD', 7, (22, 20)), ('CI', 2, (21,)), ('CC', 2, (19,)),
    ('CD', 6, ('normal', 23)), ('CI', 5, (24,)), ('CC', 2, (22,)),
]


def resolve(rows):
    """Compositional resolution of normal/break/continue continuations."""
    instructions = {p: (op, arg) for p, op, arg in rows}
    assert len(instructions) == len(rows)
    walked = []

    def visit(prefix):
        if prefix in instructions:
            op, arg = instructions[prefix]
            assert not any(q.startswith(prefix) and q != prefix for q in instructions)
            walked.append([prefix, op, arg])
            if op == 'CI':
                targets = ('normal',)
            elif op == 'CD':
                targets = (('break', 1), 'normal')
            elif op in ('CB', 'CC'):
                targets = (('break' if op == 'CB' else 'continue', arg),)
            else:
                assert op == 'CH' and arg is None
                targets = ()
            return [(op, arg, targets)]
        assert any(q.startswith(prefix + '0') for q in instructions)
        assert any(q.startswith(prefix + '1') for q in instructions)
        left, right = visit(prefix + '0'), visit(prefix + '1')
        offset = len(left)

        def bind(target, side):
            if isinstance(target, int):
                return target + (offset if side else 0)
            if target == 'normal':
                return 'normal' if side else offset
            kind, depth = target
            if not side and kind == 'break':
                return 'normal' if depth == 1 else ('break', depth - 1)
            if side and kind == 'continue':
                return 0 if depth == 1 else ('continue', depth - 1)
            return target

        return [(op, arg, tuple(bind(q, 0) for q in qs)) for op, arg, qs in left] + [
            (op, arg, tuple(bind(q, 1) for q in qs)) for op, arg, qs in right]

    graph = visit('')
    assert walked == rows
    assert all(q == 'normal' or isinstance(q, int) for _, _, qs in graph for q in qs)
    return graph


def pairing(a, b):
    return (a + b) * (a + b + 1) // 2 + b


def unpair(n):
    # A separate direct diagonal search suffices for the small finite check.
    s = 0
    while (s + 1) * (s + 2) // 2 <= n:
        s += 1
    b = n - s * (s + 1) // 2
    return s - b, b


def run(graph, store):
    store = store[:]
    pc, steps = 0, 0
    while pc != 'normal':
        steps += 1
        assert steps <= 100000
        op, arg, qs = graph[pc]
        if op == 'CH':
            return 'halt', store, steps
        if op == 'CI':
            store[arg] += 1
            pc = qs[0]
        elif op == 'CD':
            positive = store[arg] > 0
            if positive:
                store[arg] -= 1
            pc = qs[int(positive)]
        else:
            pc = qs[0]
    return 'return', store, steps


def main():
    raw = (HERE.parent / 'research/fused25_macro.sites.json').read_bytes()
    rows = json.loads(raw)
    graph = resolve(rows)
    assert graph == EXPECTED
    cases, max_steps = 0, 0
    for t in range(7):
        for w in range(40):
            x, v = unpair(w)
            assert pairing(x, v) == w
            for d in range(4):
                for h in range(7):
                    # Arbitrary untouched N and L also checked.
                    original = [37, t, w, 0, d, h, 0, 0, 91]
                    status, out, steps = run(graph, original)
                    if h == 1:
                        assert status == 'halt'
                    else:
                        assert status == 'return'
                        assert out == [37, h, v, 0, d, x, 0, 0, 91]
                    cases += 1
                    max_steps = max(max_steps, steps)
    receipt = {
        'status': 'PASS',
        'macro_sha256': hashlib.sha256(raw).hexdigest(),
        'leaf_occurrences': len(rows),
        'resolved_graph_equals_literal_contract_graph': True,
        'unresolved_structured_exits': 0,
        'finite_corroboration_cases': cases,
        'finite_maximum_primitive_steps': max_steps,
        'all_natural_argument': 'fused_transfer_review.md',
        'scope': 'Exact structured CFG plus finite corroboration; universal semantics is the accompanying mathematical proof, not the finite loop.',
    }
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
