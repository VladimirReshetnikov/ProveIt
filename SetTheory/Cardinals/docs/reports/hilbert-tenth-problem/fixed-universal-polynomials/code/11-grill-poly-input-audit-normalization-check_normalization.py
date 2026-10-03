# Portable locally authored code; upstream Python is never imported or executed.
# See PROVENANCE.json and PORTABILITY.md for all transformations.
"""Independent bounded checks for Semantic Contract section 5.
No upstream source or prior checker is imported or executed.
"""
from itertools import product
from collections import Counter
import hashlib
import json
D = 'dummy'
H = 'halt'
A, B = ('A', 'B')

def source_step(word, phase, rules):
    out = []
    for symbol in word:
        if not symbol != H:
            raise RuntimeError('Invariant failed at original source line 16')
        if phase == 0:
            out.extend(rules[symbol])
        phase ^= 1
    return (tuple(out), phase)

def norm_step(word, phase, rules):
    out = []
    for symbol in word:
        if symbol == D:
            prod = (D, D)
        elif isinstance(symbol, tuple):
            if not len(symbol) == 2:
                raise RuntimeError('Invariant failed at original source line 28')
            prod = symbol
        else:
            if not symbol != H:
                raise RuntimeError('Invariant failed at original source line 31')
            prod0 = rules[symbol] if phase == 0 else ()
            if not len(prod0) <= 4:
                raise RuntimeError('Invariant failed at original source line 33')
            padded = tuple(prod0) + (D,) * (4 - len(prod0))
            prod = (padded[:2], padded[2:])
            phase ^= 1
        if not len(prod) == 2:
            raise RuntimeError('Invariant failed at original source line 37')
        out.extend(prod)
    return (tuple(out), phase)

def erase(word):
    if not all((not isinstance(symbol, tuple) for symbol in word)):
        raise RuntimeError('Invariant failed at original source line 42')
    return tuple((symbol for symbol in word if symbol != D))

def compare_two_steps(word, phase, rules, counts):
    expected, phase_expected = source_step(erase(word), phase, rules)
    mid, phase_mid = norm_step(word, phase, rules)
    if not all((symbol == D or isinstance(symbol, tuple) for symbol in mid)):
        raise RuntimeError('Invariant failed at original source line 48')
    if not H not in mid:
        raise RuntimeError('Invariant failed at original source line 49')
    got, phase_got = norm_step(mid, phase_mid, rules)
    if not erase(got) == expected:
        raise RuntimeError('Invariant failed at original source line 51')
    if not phase_mid == phase_got == phase_expected:
        raise RuntimeError('Invariant failed at original source line 52')
    if not (len(mid) == 2 * len(word) and len(got) == 4 * len(word)):
        raise RuntimeError('Invariant failed at original source line 53')
    counts['two_generation_checks'] += 1
    counts['odd_erased_inputs'] += len(erase(word)) % 2
    counts['phase_one_inputs'] += phase
    if got.count(H) == 1:
        prefix = got[:got.index(H)]
        for p in (0, 1):
            hypothetic, _ = norm_step(prefix, p, rules)
            if not H not in hypothetic:
                raise RuntimeError('Invariant failed at original source line 63')
        counts['unique_halt_prefix_checks'] += 1
    return (got, phase_got)

def main():
    counts = Counter()
    prods = [p for n in range(5) for p in product((A, B, H), repeat=n)]
    words = [w for n in range(1, 4) for w in product((A, B), repeat=n)]
    for pa in prods:
        for pb in prods:
            rules = {A: pa, B: pb}
            for word in words:
                with_dummies = (D, D) + tuple((t for s in word for t in (s, D))) + (D,)
                for phase in (0, 1):
                    compare_two_steps(word, phase, rules, counts)
                    compare_two_steps(with_dummies, phase, rules, counts)
    rules = {A: (B, B, B), B: (A, A)}
    word, norm, phase, nphase = ((A, A), (A, A), 0, 0)
    trace = []
    for generation in range(8):
        trace.append({'original_generation': generation, 'erased_length': len(word), 'normalized_length': len(norm), 'phase': phase})
        norm, nphase = compare_two_steps(norm, nphase, rules, counts)
        word, phase = source_step(word, phase, rules)
        if not (erase(norm) == word and nphase == phase):
            raise RuntimeError('Invariant failed at original source line 91')
    if not (trace[1]['erased_length'] == 3 and trace[2]['phase'] == 1):
        raise RuntimeError('Invariant failed at original source line 92')
    rules = {A: (A,), B: (B, B)}
    odd_mid, carry = source_step((A, B, B), 0, rules)
    if not (carry == 1 and odd_mid == (A, B, B)):
        raise RuntimeError('Invariant failed at original source line 97')
    carried_word, carried = source_step(odd_mid, carry, rules)
    reset_word, reset_phase = source_step(odd_mid, 0, rules)
    if not (carried_word == (B, B) and carried == 0):
        raise RuntimeError('Invariant failed at original source line 100')
    if not (reset_word == (A, B, B) and reset_phase == 1):
        raise RuntimeError('Invariant failed at original source line 101')
    accept = 'accept'
    rules = {A: (A, A), accept: (H,)}
    out, _ = compare_two_steps((A, accept), 0, rules, counts)
    if not H not in out:
        raise RuntimeError('Invariant failed at original source line 106')
    out, _ = compare_two_steps((accept, A), 0, rules, counts)
    if not out.count(H) == 1:
        raise RuntimeError('Invariant failed at original source line 108')
    rules = {A: (A, H), B: ()}
    original, p = source_step((A, B), 0, rules)
    bad_prefix, _ = source_step(original[:original.index(H)], p, rules)
    if not H in bad_prefix:
        raise RuntimeError('Invariant failed at original source line 114')
    normalized, np = compare_two_steps((A, B), 0, rules, counts)
    good_prefix, _ = norm_step(normalized[:normalized.index(H)], np, rules)
    if not H not in good_prefix:
        raise RuntimeError('Invariant failed at original source line 117')
    counts['phase_one_discarded_accept_regressions'] = 1
    counts['prefix_hazard_repair_regressions'] = 1
    return {'verdict': 'PASS', 'checks': dict(counts), 'repeated_trace': trace, 'notes': ['No repository code imported or executed.', 'Multiple-H outputs are identity-tested only and are not declared valid halts.', 'Finite tests support the algebraic proof; they do not establish universality.']}
if __name__ == '__main__':
    print(json.dumps(main(), indent=2, sort_keys=True))
