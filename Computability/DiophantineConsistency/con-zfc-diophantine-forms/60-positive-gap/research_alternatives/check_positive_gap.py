#!/usr/bin/env python3
"""Independent symbolic check of the positive-gap source transformation.

Reads the existing 60-operation source as data; imports no project code.
It verifies the changed residuals, factorial-weighted records, and every
target extraction against a complete degree-0/1/2 monomial basis.
"""
from pathlib import Path
from itertools import combinations_with_replacement
from collections import defaultdict
import argparse
import hashlib
import json

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / 'upstream31/quartic31/quartic31_system60.json'
RECORDS = ROOT / 'research_nine/candidate/data/parent_source.json'
LAYOUT = ROOT / 'research_nine/candidate/data/split_code.json'


def require(test, message):
    if not test:
        raise ValueError(message)


def add(a,b,scale=1):
    out = dict(a)
    for monomial,coefficient in b.items():
        out[monomial] = out.get(monomial,0) + scale*coefficient
        if out[monomial] == 0:
            del out[monomial]
    return out


def multiply(a,b):
    out = {}
    for am,ac in a.items():
        for bm,bc in b.items():
            m = tuple(x+y for x,y in zip(am,bm))
            out[m] = out.get(m,0) + ac*bc
            if out[m] == 0:
                del out[m]
    return out


def scaled(a,n):
    return {m:n*c for m,c in a.items() if n*c}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source',type=Path,default=SOURCE)
    parser.add_argument('--records',type=Path,default=RECORDS)
    parser.add_argument('--layout',type=Path,default=LAYOUT)
    parser.add_argument('--output',type=Path,
                        default=Path(__file__).with_name('positive_gap_independent_check.json'))
    args = parser.parse_args()
    source = json.loads(args.source.read_text())
    variables = source['variables']
    constants = source['constants']
    all_names = variables+constants
    zero = (0,)*len(all_names)
    integer = lambda n: {zero:n} if n else {}
    names = {x:{tuple(int(i == all_names.index(x)) for i in range(len(all_names))):1}
             for x in all_names}
    def evaluate(inputs):
        env = inputs.copy()
        value = lambda a: integer(a) if type(a) is int else env[a]
        for name, operation, left, right in source['source']:
            a, b = value(left), value(right)
            env[name] = multiply(a,b) if operation == '*' else add(a,b,-1 if operation == '-' else 1)
        return [add(value(a),value(b),-1) for a,b in source['comparisons']]
    original = evaluate(names)
    require(len(original) == 22, 'source equation count')
    require([i+1 for i,r in enumerate(original) if any(m[variables.index('P')] for m in r)]
            == [7,8], 'unexpected occurrence of P')
    require([i+1 for i,r in enumerate(original) if any(m[variables.index('tau')] for m in r)]
            == [8], 'unexpected occurrence of tau')
    k = add(names['eta'],names['zeta'])
    replacements = names.copy()
    replacements['P'] = add(names['P'],k)
    replacements['tau'] = add(names['P'],names['tau'])
    replacements['L'] = add(names['L'],integer(1),-1)
    # The imported 60-gate source names its transport variable z_old-1.
    # The weighted source under review uses z_old itself. This explicit
    # substitution accounts for its extra +beta*J in residual 15.
    replacements['z'] = add(names['z'],integer(1),-1)
    changed = evaluate(replacements)
    p,t,E,c,eta = (names[n] for n in ['P','tau','E','c','eta'])
    require(changed[6] == add(p,multiply(E,add(c,eta,-1)),-1), 'gap row 7')
    expected8 = add(add(add(multiply(t,t),scaled(multiply(p,t),2)),multiply(k,p),-1),integer(1),-1)
    require(changed[7] == expected8, 'gap row 8')
    changed[13] = add(changed[13],changed[1])
    changed[14] = add(changed[14],changed[2])

    reconstructed = {}
    polynomial_terms = {}
    for row, residual in enumerate(changed,1):
        polynomial_terms[row] = {}
        unweighted = defaultdict(dict)
        for monomial,coefficient in residual.items():
            alpha,port_powers = monomial[:31],monomial[31:]
            unweighted[alpha][port_powers] = coefficient
        for alpha,coef in unweighted.items():
            degree = sum(alpha)
            require(degree <= 2,'source not quadratic')
            monomial = tuple(i for i,n in enumerate(alpha) for _ in range(n))
            weight = 1 if degree == 2 and len(set(monomial)) == 2 else 2
            reconstructed[row,monomial] = scaled(coef,weight)
            polynomial_terms[row][monomial] = scaled(coef,2)
    actual = {}
    for record in json.loads(args.records.read_text()):
        key = record['row'],tuple(record['monomial'])
        require(key not in actual, 'duplicate weighted record')
        actual[key] = {tuple(t['powers']):t['coefficient'] for t in record['coefficient']}
    if actual != reconstructed:
        differences = [(str(key),actual.get(key),reconstructed.get(key))
                       for key in sorted(set(actual)|set(reconstructed))
                       if actual.get(key) != reconstructed.get(key)]
        raise ValueError('weighted source records differ: '+str(differences[:8]))
    require(len(actual) == 86, 'expected 86 records')

    layout = json.loads(args.layout.read_text())
    weights = layout['weights']
    target = dict(zip(layout['order'],layout['targets']))
    require(len(weights) == 31 and set(target) == set(range(1,23)), 'layout shape')
    require(len(set(weights)) == 31, 'input exponent collision')
    require(len(set(target.values())) == 22, 'target collision')
    basis = {0:[()],1:[(i,) for i in range(31)],
             2:list(combinations_with_replacement(range(31),2))}
    kernels = {d:defaultdict(dict) for d in range(3)}
    extracted = {row:defaultdict(dict) for row in target}
    interactions = 0
    accidental = []
    target_reverse = {v:k for k,v in target.items()}
    for (row,monomial),coef in reconstructed.items():
        degree = len(monomial)
        encoded = target[row] - sum(weights[i] for i in monomial)
        require(encoded >= 0, 'negative kernel exponent')
        coefficient = coef
        kernels[degree][encoded] = add(kernels[degree][encoded],coefficient)
        for other in basis[degree]:
            interactions += 1
            hit = target_reverse.get(encoded+sum(weights[i] for i in other))
            if hit is None:
                continue
            factor = 2 if degree == 2 and other[0] != other[1] else 1
            extracted[hit][other] = add(extracted[hit][other],scaled(coefficient,factor))
            if hit != row or other != monomial:
                accidental.append((row,monomial,hit,other))
    for row in target:
        found = {m:c for m,c in extracted[row].items() if c}
        require(found == polynomial_terms[row], 'incorrect target extraction')
    require(not accidental, 'unexpected source interaction')
    kernel_degrees = [max(e for e,c in kernels[d].items() if c) for d in range(3)]
    require(kernel_degrees == layout['kernel_degrees'],'kernel degrees')
    height = max(kernel_degrees[d]+d*max(weights) for d in range(3))
    require(height == layout['convolution_height'],'convolution height')
    head = kernels[2][kernel_degrees[2]]
    require(head == {(0,)*4:1},'quadratic kernel head is not +1')
    normalization = {}
    for monomial,coefficient in changed[4].items():
        normalization = add(normalization,{monomial[31:]:coefficient})
    require(normalization == {(0,)*4:1},'all-one normalization')
    coefficient_bounds = {}
    for label,bits,expected in (
        ('original31',(1064921,1070004,1064921,1064922),2134927),
        ('native44',(590069,592884,590069,590070),1182955),
    ):
        bounds = [sum(abs(c)*(1 << sum(e*b for e,b in zip(m,bits)))
                      for m,c in polynomial.items())
                  for kernel in kernels.values() for polynomial in kernel.values()
                  if polynomial]
        exponent = max(bounds).bit_length()
        require(exponent == expected,'unexpected coefficient bound for '+label)
        kappa = exponent+12
        threshold_exponent = 8*kappa-11
        # Symbolic in k: 2272*(kappa+2k)-30k-22 equals
        # 2*(threshold_exponent+k+1128*(kappa+2k)).
        require(2272*kappa-22 == 2*(threshold_exponent+1128*kappa),
                'population calibration constant')
        require(2*2272-30 == 2*(1+2*1128),
                'population calibration slope')
        coefficient_bounds[label] = {
          'port_bit_lengths':list(bits),
          'coefficient_bound_exponent':exponent,
          'base_scale_exponent':kappa,
          'threshold_scale_exponent':threshold_exponent,
          'threshold_B_power':1128,
          'population_calibration':'identity in the arbitrary nonnegative binary logarithm k'
        }
    report = {
      'status':'PASS',
      'source_sha256':hashlib.sha256(args.source.read_bytes()).hexdigest(),
      'record_sha256':hashlib.sha256(args.records.read_bytes()).hexdigest(),
      'layout_sha256':hashlib.sha256(args.layout.read_bytes()).hexdigest(),
      'source_variables':31,
      'transport_conversion':'source31 shifted z = target unshifted z - 1; the matching +beta*J in row 15 is explicitly reconstructed',
      'square_register_conversion':'source L = target L - 1; target L=q^2>1 implies positive inverse',
      'quadratic_residuals':22,
      'weighted_records':len(actual),
      'exhaustive_degree_matched_interactions':interactions,
      'unexpected_target_interactions':len(accidental),
      'maximum_input_exponent':max(weights),
      'maximum_target_exponent':max(target.values()),
      'kernel_degrees':kernel_degrees,
      'convolution_height':height,
      'quadratic_kernel_leading_coefficient':1,
      'all_one_row5_value':1,
      'coherent_tuple_coefficient_bounds':coefficient_bounds,
      'proof_scope':'Exact symbolic source transformation, weighting, target isolation and degree data. Positivity bijection proved separately; no unbounded compiler or consistency claim from computation.'
    }
    args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__ == '__main__':
    main()
