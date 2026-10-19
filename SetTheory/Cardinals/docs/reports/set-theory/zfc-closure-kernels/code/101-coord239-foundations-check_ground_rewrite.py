#!/usr/bin/env python3
"""Independent certificate fixtures for context, substitution and direction."""
import json
from pathlib import Path
import ground_rewrite as g

def main():
    sig = {'a': 0, 'b': 0, 'f': 2, 'h': 1}
    a, b = ('a',), ('b',)
    eqs = [(('f', 'x', 'x'), 'x')]
    left, right = ('h', ('f', a, a)), ('h', a)
    good = g.encode([(0, 0, [0], {'x': a})], sig, eqs)
    assert g.validate(good, sig, eqs, left, right) == (True, 1)
    reverse = g.encode([(0, 1, [0], {'x': a})], sig, eqs)
    assert g.validate(reverse, sig, eqs, right, left) == (True, 1)
    rejected = 0
    trials = [(good, ('h', ('f', a, b)), right),
              (good, left, right)]
    try:
        g.validate(*trials[0][:1], sig, eqs, *trials[0][1:])
    except ValueError:
        rejected += 1
    else:
        raise AssertionError('accepted unequal repeated-variable instances')
    for cut in range(len(good)):
        try:
            g.validate(good[:cut], sig, eqs, left, right)
        except ValueError:
            rejected += 1
        else:
            raise AssertionError('accepted truncated certificate')
    for bad in [good + '0', 'x', g.encode([(0, 0, [1], {'x': a})], sig, eqs)]:
        try:
            g.validate(bad, sig, eqs, left, right)
        except ValueError:
            rejected += 1
        else:
            raise AssertionError('accepted malformed context/certificate')
    extra = [(('h', 'x'), ('f', 'x', 'y'))]
    cert = g.encode([(0, 0, [], {'x': a, 'y': b})], sig, extra)
    assert g.validate(cert, sig, extra, ('h', a), ('f', a, b)) == (True, 1)
    deep = a
    for _ in range(2500):
        deep = ('h', deep)
    deep_cert = g.encode([(0, 0, [], {'x': deep})], sig, eqs)
    assert g.validate(deep_cert, sig, eqs, ('f', deep, deep), deep) == (True, 1)
    tiny = [('a',), ('b',)]
    finite_search = g.search({'a': 0, 'b': 0}, [(tiny[0], tiny[1])], *tiny, max_code=256)
    assert finite_search['status'] == 'CERTIFIED_GROUND_DERIVATION'
    result = {'status': 'PASS', 'contextual_forward': True, 'reverse': True,
              'repeated_variables': True, 'one_sided_variables': True,
              'deep_ground_terms_2500': True,
              'malformed_rejections': rejected, 'finite_search_control': finite_search,
              'scope': 'Finite correctness fixtures, not a binary TM or consistency check.'}
    out = Path(__file__).with_name('ground_rewrite_checks.json')
    out.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()
