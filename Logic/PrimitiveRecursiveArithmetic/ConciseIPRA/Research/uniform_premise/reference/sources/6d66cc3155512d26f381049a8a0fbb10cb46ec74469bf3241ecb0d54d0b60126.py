"""Finite structural regression for two distinct local R slots.

This checks raw substitution against independently constructed named syntax,
not against a second copy of the same opening routine. It is untrusted test
code, never imported by the kernel.
"""
import json
import pathlib
import random

from producer import Z, V, S, R, fresh, subst, encode
from validate import load_kernel

ROOT = pathlib.Path(__file__).resolve().parent


def main():
    env = load_kernel(ROOT / 'kernel.py')
    env['k'] = -1
    rng = random.Random(7382026)
    u, v, p = fresh('counter'), fresh('state'), fresh('passive')

    def term(depth, variables):
        pick = rng.randrange(5 if depth else 2)
        if pick == 0: return Z
        if pick == 1: return V(rng.choice(variables))
        if pick == 2: return S(term(depth-1, variables))
        return R(term(depth-1, variables), term(depth-1, variables),
                 lambda j, w: term(depth-1, variables + [j[1], w[1]]))

    for _ in range(2000):
        body = term(3, [u, v, p])
        counter = term(2, [p])
        seed = term(2, [p])
        rigid = {p: -1}
        raw_body = encode(body, (v, u), rigid)
        raw_counter = encode(counter, rigid=rigid)
        raw_seed = encode(seed, rigid=rigid)
        previous = ('rec', counter, seed, u, v, body)
        expected = encode(subst(subst(body, u, counter), v, previous), rigid=rigid)
        actual = env['i'](env['i'](raw_body, raw_counter, 3),
                          [raw_counter, raw_seed, raw_body], 1)
        assert actual == expected, (raw_body, actual, expected)

    # If the counter is used, an exposed free positive image must reject.
    try:
        env['i'](3, 1, 3)
    except Exception:
        pass
    else:
        raise AssertionError('A free counter image was captured')

    result = {'canonical_named_substitution_examples': 2000,
              'captured_counter_image_rejected': True,
              'failures': [],
              'limits': 'Finite structural regression; the universal opening lemma is written separately.'}
    (ROOT / 'opening_validation.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
