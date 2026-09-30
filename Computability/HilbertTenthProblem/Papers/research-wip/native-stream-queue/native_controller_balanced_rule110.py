"""Balanced zero-endpoint controllers and zero-preserving Rule110 codes.

The all-length obstruction is mathematical. This checker audits its symbolic
elimination and literal source, then exhausts the reduced exact rail-assignment
problem through block length three. It does not search bounded coefficients.
"""
import argparse
from fractions import Fraction
from functools import reduce
from itertools import product
import hashlib
import json
from math import gcd, lcm
from pathlib import Path
import sympy as sp

TRANSITIONS = ((0, 0, 0, 0), (0, 1, 1, 1), (1, 0, 1, 0),
               (1, 1, 1, 2), (2, 0, 1, 0), (2, 1, 0, 2))


def rail_words(word, length):
    result = [0]
    for j in range(length):
        digit = word // 3**j % 3
        if digit == 1:
            result = [r + bit * 3**j for r in result for bit in (0, 1)]
        elif digit == 2:
            result = [r + 3**j for r in result]
    return sorted(result)


def symbolic_audit():
    radix, state_b, state_c, mu, nu, r_b, r_c, r2, r3, a2 = sp.symbols(
        'radix state_b state_c mu nu r_b r_c r2 r3 a2')
    # Four of the required edges, with append-weight difference normalized to1.
    eq_b0 = state_b + mu + r_b
    eq_c0 = state_c + mu + r_c
    eq_b1 = radix*state_c - state_b - nu + r2 - mu - a2
    eq_c1 = (radix-1)*state_c - nu + r3
    consequence = state_c - r3 + r2 - a2 + r_b
    assert sp.expand(eq_b1 - eq_c1 + eq_b0 - consequence) == 0
    mu_formula = r2-a2+r_b-r_c-r3
    assert sp.expand((eq_c0-consequence) - (mu-mu_formula)) == 0

    f0, f1, f2, f3, mask, v, b, c = sp.symbols('F0 F1 F2 F3 Q v b c')
    append = f0+f1-mask
    read = f2+f3-mask
    original = (v+b)*f0+b*f1+(c-v)*f2+c*f3-(b+c)*mask
    rewritten = v*(f0-f2)+b*append+c*read
    assert sp.expand(original-rewritten) == 0
    schedule = [('balance_delta', '-', 'F0', 'F2'),
                ('balance_rail', '*', 'v', 'balance_delta'),
                ('balance_append', '*', 'b', 'A'),
                ('balance_read', '*', '-c', 'D'),
                ('balance_left', '+', 'balance_rail', 'balance_append')]
    env = dict(F0=f0, F2=f2, v=v, b=b, A=append, D=read)
    env['-c'] = -c
    for target, op, left, right in schedule:
        assert target not in env
        lhs, rhs = env[left], env[right]
        env[target] = lhs*rhs if op == '*' else lhs+rhs if op == '+' else lhs-rhs
    assert sp.expand(env['balance_left']-env['balance_read']-original) == 0
    return dict(operations=5, multiplications=3, additions_subtractions=2,
                instructions=[list(row) for row in schedule],
                equality=['balance_left', 'balance_read'],
                inherited_quantities=['A=F0+F1-Q', 'D=F2+F3-Q'],
                coefficient_restriction='append=(v+b,b), read=(c-v,c), h=cs=cf=0',
                source=str(sp.expand(original)),
                integral_state_consequence=str(consequence))


def audit_code(word, length):
    radix = 3**length
    rails = rail_words(word, length)
    # r1/r2/r3 are read-rail0 words on A1/B1/C1. a1/a2 are
    # append-rail0 words on A1/B1. r_b/r_c belong to B0/C0 outputs.
    pairs = {}
    triples = {}
    for a1, a2 in product(rails, repeat=2):
        pairs.setdefault(2*a2-a1, []).append((a1, a2))
    for r1, r2, r3 in product(rails, repeat=3):
        triples.setdefault(r1+r3-2*r2, []).append((r1, r2, r3))
    vectors = set()
    count = 0
    for r_b, r_c in product(rails, repeat=2):
        if r_b == r_c:
            continue  # These two selected zero-read edges force B=C.
        target = (radix+2)*r_b-(radix+1)*r_c
        for x, read_choices in triples.items():
            for a1, a2 in pairs.get(target-x, []):
                for r1, r2, r3 in read_choices:
                    mu = r2-a2+r_b-r_c-r3
                    nu = r3-(radix-1)*(mu+r_c)
                    state_b, state_c = -mu-r_b, -mu-r_c
                    if state_b == 0 or state_c == 0:
                        continue
                    assert state_b != state_c and state_c == r3-r2+a2-r_b
                    assert nu < 0 or nu > word
                    b = Fraction(mu, word)
                    c = Fraction(nu, word)
                    weights = (c-1, c, b+1, b)  # read, then append
                    assert weights[0]*weights[1] > 0
                    selected = ((0, 0), (r1, a1), (0, r_b),
                                (r2, a2), (0, r_c), (r3, 0))
                    states = (0, state_b, state_c)
                    for (old, bit, out, new), (rd, ap) in zip(TRANSITIONS, selected):
                        words = (rd, word*bit-rd, ap, word*out-ap)
                        assert radix*states[new] == states[old]+sum(
                            weight*digit for weight, digit in zip(weights, words))
                    vector = states+weights
                    den = lcm(*(value.denominator if isinstance(value, Fraction) else 1
                                for value in vector))
                    vector = tuple(int(value*den) for value in vector)
                    divisor = reduce(gcd, vector)
                    vector = tuple(value//divisor for value in vector)
                    if next(value for value in vector if value) < 0:
                        vector = tuple(-value for value in vector)
                    vectors.add(vector)
                    count += 1
    payload = json.dumps(sorted(vectors), separators=(',', ':')).encode()
    return dict(code_word=word, rail_splits=len(rails), nondegenerate_assignments=count,
                primitive_vectors=len(vectors), all_read_weights_same_strict_sign=True,
                vector_sha256=hashlib.sha256(payload).hexdigest())


def verify():
    counts = []
    records = []
    for length in (1, 2, 3):
        rows = [audit_code(word, length) for word in range(1, 3**length)]
        totals = dict(length=length, codes=len(rows),
                      assignments=sum(row['nondegenerate_assignments'] for row in rows),
                      vectors=sum(row['primitive_vectors'] for row in rows))
        counts.append(totals)
        records.append(dict(length=length, codes=rows))
    assert counts == [dict(length=1, codes=2, assignments=0, vectors=0),
                      dict(length=2, codes=8, assignments=50, vectors=24),
                      dict(length=3, codes=26, assignments=1640, vectors=420)]
    return dict(status='PASS_BALANCED_ZERO_CODE_RULE110_OBSTRUCTION',
                literal_source=symbolic_audit(), totals=counts, rail_assignment_audit=records,
                theorem_scope=('Every fixed block length, zero codeword all0, one fixed '
                               'nonzero ternary codeword, three distinct carry states, '
                               'balanced weights and zero offset/endpoints. All six required '
                               'Rule110 edges force same-sign read weights, hence bounded '
                               'ordinary inputs even when every uncoded edge is allowed.'),
                finite_scope=('Exact complete reduced rail-assignment enumeration through '
                              'length3; this evidence is not the proof for arbitrary lengths.'),
                established_complete_universal_bound=76)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = verify()
    receipt = Path(__file__).with_suffix('.json')
    if args.write:
        receipt.write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    else:
        assert json.loads(receipt.read_text()) == result, 'receipt mismatch'
    print(json.dumps({key: value for key, value in result.items()
                      if key != 'rail_assignment_audit'}, indent=2))
