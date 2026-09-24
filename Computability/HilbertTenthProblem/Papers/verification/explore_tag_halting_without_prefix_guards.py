#!/usr/bin/env python3
"""Exact finite-stream halting without intermediate tag-queue bounds."""
from itertools import product
from pathlib import Path
import json


def words(max_length):
    return [tuple(w) for n in range(max_length + 1)
            for w in product((0, 1), repeat=n)]


def stream(w, h, selector):
    return w + tuple(a for symbol in selector for a in h[symbol])


def accepts(w, beta, h, selector):
    u = stream(w, h, selector)
    t = len(selector)
    return (beta*t <= len(u) < beta*(t+1)
            and all(u[beta*i] == symbol
                    for i, symbol in enumerate(selector)))


def execute(w, beta, h, max_steps):
    queue = w
    reads = []
    for step in range(max_steps + 1):
        if len(queue) < beta:
            return tuple(reads), queue
        if step == max_steps:
            return None
        a = queue[0]
        reads.append(a)
        queue = queue[beta:] + h[a]
    raise AssertionError('unreachable')


def extract(w, beta, h, selector):
    assert accepts(w, beta, h, selector)
    u = stream(w, h, selector)
    prefix = w
    queue = w
    lengths = []
    first_halt = None
    for j in range(len(selector) + 1):
        ell = len(prefix) - beta*j
        lengths.append(ell)
        if first_halt is None:
            assert queue == prefix[beta*j:] and ell == len(queue)
            if ell < beta:
                assert 0 <= ell < beta
                first_halt = j
            else:
                assert j < len(selector)
                assert beta*j < len(prefix)
                assert queue[0] == prefix[beta*j] == u[beta*j] == selector[j]
                queue = queue[beta:] + h[selector[j]]
        if j < len(selector):
            prefix += h[selector[j]]
    assert first_halt is not None
    direct = execute(w, beta, h, len(selector))
    assert direct is not None and len(direct[0]) == first_halt
    return first_halt, lengths


def verify():
    depth = 5
    appendants = words(2)
    initials = words(3)
    selectors = words(depth)
    cases = accepted = noncausal = halted = instances = 0
    for beta in range(1, 5):
        for h in product(appendants, repeat=2):
            for w in initials:
                any_stream = False
                direct = execute(w, beta, h, depth)
                for selector in selectors:
                    ok = accepts(w, beta, h, selector)
                    cases += 1
                    if ok:
                        any_stream = True
                        accepted += 1
                        first, _ = extract(w, beta, h, selector)
                        noncausal += first < len(selector)
                assert any_stream == (direct is not None)
                if direct is not None:
                    assert accepts(w, beta, h, direct[0])
                    halted += 1
                instances += 1
    w = (0, 0)
    beta = 2
    h = ((0,), (1, 0, 0))
    selector = (0, 0, 1)
    first, lengths = extract(w, beta, h, selector)
    assert first == 1 and lengths == [2, 1, 0, 1]
    assert stream(w, h, selector) == (0, 0, 0, 0, 1, 0, 0)
    return dict(
        status='PASS_TAG_HALTING_WITHOUT_PREFIX_GUARDS',
        alphabet_size=2, deletion_numbers=[1, 2, 3, 4],
        exhaustive_appendant_max_length=2, initial_max_length=3,
        selector_max_length=depth, instances=instances,
        proposed_stream_cases=cases, accepted_streams=accepted,
        accepted_streams_extending_beyond_real_halt=noncausal,
        direct_halts_within_depth=halted,
        self_supported_example=dict(initial='00', appendants=['0', '100'],
            selector='001', produced='0000100', deletion_number=2,
            formal_prefix_lengths=lengths, actual_halting_step=first),
        proof='../1980/EXPLORATION_TAG_HALTING_WITHOUT_PREFIX_GUARDS.md',
        scope='General eventual-halting equivalence proved in the note, with bounded direct queue checks here. No finite SLP, input compiler, or new universal operation bound is claimed.')


if __name__ == '__main__':
    result = verify()
    Path(__file__).with_suffix('.json').write_text(
        json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print(result['status'])
    print({k: v for k, v in result.items() if k not in ('proof', 'scope')})
