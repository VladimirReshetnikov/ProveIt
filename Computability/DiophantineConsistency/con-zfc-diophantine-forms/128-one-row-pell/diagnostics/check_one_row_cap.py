#!/usr/bin/env python3
"""Finite independent diagnostics for the one-row Pell theorem.

These checks do not replace the unbounded proof.  They exercise both signs,
zero indices, near-minimum allowed moduli, explicit completeness witnesses,
and the necessity of the nonnegative quotient hypothesis.
"""

import itertools
import json


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def pell(a, count):
    result = [(1, 0)]
    for _ in range(count):
        x, y = result[-1]
        result.append((a*x + (a*a-1)*y, x+a*y))
    return result


def main():
    tested_tuples = 0
    complete_witnesses = []
    margin_checks = 0
    for w in (4, 6, 8, 10):
        b = w//2
        # Test close to the weaker theorem threshold, not only at the
        # much larger A supplied by the actual shared-power frame.
        a = w**3+2
        pairs = pell(a, w+2)
        v = pairs[w][1]
        candidates = []
        for j in range(b+3):
            x, y = pairs[j]
            candidates.extend((j, sx*x, sy*y)
                              for sx, sy in itertools.product((-1, 1), repeat=2))
        for e in range(1, b):
            require((pairs[b+1][1]-e)**2 > v, 'next-index square separation')
            margin_checks += 1
        for count in (1, 2):
            for targets in itertools.product(range(1, b), repeat=count):
                good_error = sum((pairs[e][0]-1)**2 + (pairs[e][1]-e)**2
                                 for e in targets)
                numerator = v-w-good_error
                require(numerator > 0 and numerator % (a-1) == 0,
                        'constructive completeness quotient')
                complete_witnesses.append({
                    'W': w, 'A': a, 'targets': list(targets),
                    'Q': numerator//(a-1),
                })
                for chosen in itertools.product(candidates, repeat=count):
                    error = sum((x-1)**2+(y-e)**2
                                for (_, x, y), e in zip(chosen, targets))
                    numerator = v-w-error
                    accepted = numerator >= 0 and numerator % (a-1) == 0
                    canonical = all(x == pairs[e][0] and y == pairs[e][1]
                                    for (_, x, y), e in zip(chosen, targets))
                    require(accepted == canonical, 'bounded signed tuple audit')
                    tested_tuples += 1
        require((w-2)*(4+(w-1)**2) < w**3 < a-1,
                'whole signed error bound')

    w, a, e, j = 4, 66, 1, 66
    pairs = pell(a, j)
    v = pairs[w][1]
    x, y = pairs[j]
    wrong_numerator = v-w-(x-1)**2-(y-e)**2
    require(wrong_numerator < 0 and wrong_numerator % (a-1) == 0,
            'unrestricted quotient counterexample')
    x, y = pairs[e]
    correct_q = (v-w-(x-1)**2-(y-e)**2)//(a-1)
    require(correct_q == 35315, 'small complete witness')
    result = {
        'status': 'pass',
        'scope': 'finite exact diagnostics, not an unbounded proof or consistency test',
        'signed_candidate_tuples_checked': tested_tuples,
        'canonical_witness_lists_checked': len(complete_witnesses),
        'square_separation_checks': margin_checks,
        'explicit_small_witness': {'W':4, 'A':66, 'e':1, 'X':66, 'Y':1,
                                   'V':v, 'Q':correct_q},
        'negative_quotient_counterexample': {'W':w, 'A':a, 'requested_index':e,
                                            'actual_index':j, 'Q_sign':'negative'},
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
