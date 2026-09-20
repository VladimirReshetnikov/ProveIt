#!/usr/bin/env python3
"""Regression, structural theorem and local-certificate tests (stdlib only)."""
from __future__ import annotations
from itertools import combinations
from pathlib import Path
import json
import math
import sys
import time
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'src'))
from mix_parser import Parser
from family_certificate import build_certificate
from check_certificate import check_certificate


def run():
    start = time.perf_counter()
    p2, p3 = Parser(2), Parser(3)
    source_word = 'aaabbbcbbccccaa'
    assert not p2.accepts_word(source_word)
    assert p3.accepts_word(source_word)
    assert p2.accepts_word('aaccbb')
    assert not p3.accepts(('a', 'accb', 'b'))
    assert Parser(1).accepts_word('')
    assert not Parser(1).accepts_word('abc')
    assert not p3.accepts_word('abcc')
    assert not p3.accepts(('a', 'a', 'bb', 'cc'))
    assert p3.accepts(('', 'aaccbb', ''))
    for bad in ['abcd', 'a b c', 'ABC']:
        try:
            p3.accepts_word(bad)
        except ValueError:
            pass
        else:
            raise AssertionError('Invalid alphabet was accepted by the API.')

    certificates = 0
    for n in range(6):
        for bb in combinations(range(2*n), n):
            bs = set(bb)
            v = ''.join('b' if j in bs else 'c' for j in range(2*n))
            assert p2.accepts((v, 'a'*n))
            for p in range(n+1):
                t = ('a'*p, v, 'a'*(n-p))
                assert p3.accepts(t)
                cert = build_certificate(v, p)
                assert check_certificate(cert) == t
                certificates += 1
    cone = []
    for n in range(2, 13):
        tested = 0
        for p in range(1, n):
            u = n-p
            for r in range(1, u):
                for s in range(1, p):
                    if r == s:
                        continue
                    w = 'a'*p + 'b'*(n-s) + 'c'*r + 'b'*s + 'c'*(n-r) + 'a'*u
                    assert not p2.accepts_word(w), (p, u, r, s)
                    assert p3.accepts_word(w)
                    tested += 1
        expected = (math.comb(n-1, 3) if n >= 4 else 0) - (n-2)**2 // 4
        assert tested == expected
        cone.append({'N': n, 'checked_cone_words': tested})
    # The checker rejects a deliberately corrupted positive proof.
    corrupt = build_certificate('bc', 1)
    corrupt['nodes'][-1]['left'][0] = 'aa'
    try:
        check_certificate(corrupt)
    except ValueError:
        pass
    else:
        raise AssertionError('Certificate checker failed its negative test.')
    return {'all_checks_passed': True, 'binary_family_certificates_checked': certificates,
            'binary_family_max_N': 5, 'cone_checks': cone,
            'seconds': time.perf_counter()-start}

if __name__ == '__main__':
    print(json.dumps(run(), indent=2))
