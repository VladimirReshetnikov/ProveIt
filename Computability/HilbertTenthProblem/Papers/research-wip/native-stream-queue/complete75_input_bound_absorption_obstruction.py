"""Exact input-translation obstruction to the apparent 87-operation rewrite."""
import argparse
from collections import Counter
from math import gcd
import json
from pathlib import Path
import random

import complete75_coupled_index_linear88 as original
import complete75_linear_input_modulus89 as linear

eliminated = original.eliminated
VARIANTS = {'discriminant_87': (original, 87), 'linear_modulus_88': (linear, 88)}


def sources(name):
    parent, cost = VARIANTS[name]
    _, old, comparisons, _ = parent.sources()
    assert ('marked_rhs', '-', 'C_after_alpha', 'scaled_t') in old
    def alias(value):
        return 'C_after_alpha' if value == 'marked_rhs' else value
    certificate = [(key, op, alias(left), alias(right))
                   for key, op, left, right in old if key != 'marked_rhs']
    polynomial = certificate+[('polynomial', '-', 'eight_units', 1)]
    assert len(polynomial) == cost
    return certificate, comparisons, polynomial


def modulus(name, values):
    q = (values['B']-1)*values['Jrep']+1
    a = values['w']*values['s']*q**6+values['s']*q**3
    return (a+2)**2-1 if name == 'discriminant_87' else a+1


def source_checks(name):
    parent, cost = VARIANTS[name]
    certificate, comparisons, polynomial = sources(name)
    old = parent.sources()[3]
    available = set(parent.RETAINED+eliminated.baseline.prior.CONSTANTS+['x'])
    available.update(('Bm1', 'Kconstant', 'twice_cell_bits'))
    for key, op, left, right in polynomial:
        assert key not in available and op in ('+', '-', '*')
        assert all(isinstance(v, int) or v in available for v in (left, right))
        available.add(key)
    assert [key for key, _, left, right in polynomial if 'x' in (left, right)] == ['scaled_t']
    assert [key for key, _, left, right in polynomial if 'scaled_t' in (left, right)] == ['odd_index']
    counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in polynomial)
    assert counts == {'M': 47, 'A': cost-47}
    rng, evidence = random.Random(87000+cost), Counter()
    for case in range(512):
        signed = case >= 384
        values = {key: rng.randrange(-7, 8) if signed else rng.randrange(1, 8)
                  for key in parent.RETAINED+['x']}
        # Keep the modulus positive, independently of other signed fields.
        values.update(Jrep=rng.randrange(1, 8), w=rng.randrange(1, 8), s=rng.randrange(1, 8))
        B = rng.choice((16,32,64,256))
        d = B.bit_length()-1
        values.update(B=B, cell_bits=d, inner_bits=3, DC=3, DR=5, MC=B-2, MF=4)
        values['delta'] = 2*d+rng.randrange(1, 8)
        # Forward absorption from any original supplied assignment.
        absorbed = {**values, 'alpha': values['alpha']+2*d*values['x']}
        oldenv = eliminated.run(old, eliminated.fixed_inputs(values))
        env = eliminated.run(polynomial, eliminated.fixed_inputs(absorbed))
        assert env['polynomial'] == oldenv['polynomial']
        assert all(env[key] == oldenv[key] for key in parent.FACTOR_NAMES)
        assert env['C_after_alpha'] == oldenv['marked_rhs']
        M = modulus(name, values)
        common = gcd(2*d, M)
        shifted = {**absorbed, 'x': absorbed['x']+M//common,
                   'delta': absorbed['delta']-2*d//common}
        newenv = eliminated.run(polynomial, eliminated.fixed_inputs(shifted))
        assert newenv['polynomial'] == env['polynomial']
        assert all(newenv[key] == env[key] for key in parent.FACTOR_NAMES)
        assert all(newenv[key] == env[key] for key, _, _, _ in certificate
                   if key not in ('scaled_t','odd_index','index_product'))
        assert shifted['delta'] > 0 and shifted['x'] > absorbed['x']
        if not signed:
            assert all(shifted[key] > 0 for key in parent.RETAINED+['x'])
        evidence['signed_cases' if signed else 'positive_cases'] += 1
        evidence['forward_absorption_identities'] += 1
        evidence['full_source_translation_identities'] += 1
    return dict(status='REJECTED: exact input-translation symmetry contradicts universality for nonempty finite languages.',
                operations=cost, multiplications=47, additions_subtractions=cost-47,
                witnesses=19, equations=1, comparisons=comparisons,
                deleted_gate=['marked_rhs','-','C_after_alpha','scaled_t'],
                source=polynomial, evidence=dict(evidence))


def pell_growth_checks():
    count = 0
    for A in range(3, 26):
        Delta = A*A-1
        for d in range(4, 13):
            for x in range(1, 5):
                for b in (1,3,7):
                    u = 2*d*x+b
                    _, ordinate = original.pell(A, u)
                    assert (ordinate-u) % Delta == 0
                    quotient = (ordinate-u)//Delta
                    assert quotient >= u*(u-1)//2 > 2*d
                    for M in (Delta, A-1):
                        assert (ordinate-u) % M == 0
                        delta = (ordinate-u)//M
                        common = gcd(2*d, M)
                        shift = 2*d//common
                        assert delta-shift > 0
                        assert 2*d*(x+M//common)+b+(delta-shift)*M == ordinate
                    count += 1
    return dict(odd_input_Pell_cases=count,
                scope='Input Pell coordinates only; complete compiler zeros follow existentially from the established compiler theorem.')


def verify():
    return dict(variants={name:source_checks(name) for name in VARIANTS},
                pell_growth=pell_growth_checks())


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write-receipt', action='store_true')
    args = parser.parse_args()
    result = verify()
    path = Path(__file__).with_suffix('.json')
    if args.write_receipt:
        path.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    else:
        assert json.loads(path.read_text()) == json.loads(json.dumps(result))
    print('input-bound absorption: apparent87/88 schedules rejected by exact positive input translation; PASS')
