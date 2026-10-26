#!/usr/bin/env python3
"""Independently replay integral monic-contraction certificates.

No producer modules are imported. Monomials are exponent dictionaries,
represented canonically as tuples of (coordinate, exponent), rather than
the repeated-index representation used by the producer. Every step is
checked in the exact integer polynomial ring before the literal endpoint
is compared. Sum-of-squares expansions are collected independently.
"""
from __future__ import annotations
import argparse
import copy
import hashlib
import json
from collections import Counter
from pathlib import Path


def demand(condition, message):
    if not condition:
        raise ValueError(message)


def read_polynomial(terms, dimension):
    demand(isinstance(terms, list), 'terms must be a list')
    result = {}
    for term in terms:
        demand(isinstance(term, list) and len(term) == 2, 'malformed term')
        coefficient, indices = term
        demand(type(coefficient) is int and coefficient != 0,
               'nonzero integer coefficient required')
        demand(isinstance(indices, list), 'monomial must be a list')
        demand(all(type(j) is int and 0 <= j < dimension for j in indices),
               'coordinate outside source ambient space')
        key = tuple(sorted(Counter(indices).items()))
        demand(key not in result, 'uncollected duplicate monomial')
        result[key] = coefficient
    return result


def sparse_sum(*polynomials):
    total = Counter()
    for polynomial in polynomials:
        for powers, coefficient in polynomial.items():
            total[powers] += coefficient
    return {powers: coefficient for powers, coefficient in total.items()
            if coefficient}


def monomial_product(left, right):
    powers = dict(left)
    for variable, exponent in right:
        powers[variable] = powers.get(variable, 0) + exponent
    return tuple(sorted(powers.items()))


def sparse_product(left, right):
    total = Counter()
    for lp, lc in left.items():
        for rp, rc in right.items():
            total[monomial_product(lp, rp)] += lc * rc
    return {powers: coefficient for powers, coefficient in total.items()
            if coefficient}


def substitute_coordinate(polynomial, variable, replacement):
    """Expand each monomial independently by repeated convolution."""
    total = Counter()
    for powers, coefficient in polynomial.items():
        exponent = dict(powers).get(variable, 0)
        unaffected = tuple((j, e) for j, e in powers if j != variable)
        expanded = {unaffected: coefficient}
        for _ in range(exponent):
            expanded = sparse_product(expanded, replacement)
        for key, value in expanded.items():
            total[key] += value
    return {key: value for key, value in total.items() if value}


def degree(polynomial):
    return max((sum(e for _, e in powers) for powers in polynomial), default=-1)


def variables_of(polynomial):
    return {j for powers in polynomial for j, _ in powers}


def serialize(polynomial):
    entries = []
    for powers, coefficient in polynomial.items():
        repeated = tuple(j for j, e in powers for _ in range(e))
        entries.append((repeated, coefficient))
    return [[coefficient, list(repeated)]
            for repeated, coefficient in sorted(entries)]


def collect_squares(rows):
    total = Counter()
    for polynomial in rows.values():
        terms = list(polynomial.items())
        for i, (left, lc) in enumerate(terms):
            for j in range(i, len(terms)):
                right, rc = terms[j]
                total[monomial_product(left, right)] += lc * rc * (1 if i == j else 2)
    return {key: value for key, value in total.items() if value}


def replay(source, certificate, with_expansion=True):
    demand(source.get('domain') == 'unrestricted integers',
           'this integer-bijection verifier requires unrestricted integers')
    demand(source.get('polynomial') == 'sum(square(row) for row in residuals)',
           'source must use the stated sum-of-squares convention')
    dimension = len(source['variables'])
    rows = {r: read_polynomial(item['terms'], dimension)
            for r, item in enumerate(source['residuals'])}
    alive = set(range(dimension))
    cap = certificate['cap']
    demand(type(cap) is int and cap >= 1, 'invalid residual degree bound')
    demand(max(map(degree, rows.values())) <= cap, 'source exceeds degree cap')
    source_live = set().union(*(variables_of(row) for row in rows.values()))
    demand(source_live == alive, 'source has unused ambient coordinates')
    replay_steps = []

    for number, step in enumerate(certificate['steps']):
        row_id, variable, coefficient = (step[k] for k in ('row','variable','coefficient'))
        demand(type(row_id) is int and row_id in rows,
               f'step {number}: pivot row missing or previously deleted')
        demand(type(variable) is int and variable in alive,
               f'step {number}: variable missing or previously deleted')
        demand(type(coefficient) is int and coefficient in (-1, 1),
               f'step {number}: pivot coefficient is not an integer unit')
        row = rows[row_id]
        unit_monomial = ((variable, 1),)
        demand(row.get(unit_monomial) == coefficient,
               f'step {number}: declared pivot coefficient is wrong')
        other = {powers: value for powers, value in row.items()
                 if powers != unit_monomial}
        demand(variable not in variables_of(other),
               f'step {number}: pivot variable occurs nonlinearly or twice')
        expected = {powers: -coefficient * value for powers, value in other.items()}
        restoration = read_polynomial(step['restoration'], dimension)
        demand(restoration == expected,
               f'step {number}: restoration polynomial differs from unit pivot')
        demand(variables_of(restoration) <= alive - {variable},
               f'step {number}: restoration has a stale or self dependency')
        demand(substitute_coordinate(row, variable, restoration) == {},
               f'step {number}: pivot does not become the zero polynomial')

        # Deliberately substitute through every remaining row, independent of
        # the producer's occurrence lists, heuristics, and degree estimates.
        new_rows = {j: substitute_coordinate(polynomial, variable, restoration)
                    for j, polynomial in rows.items() if j != row_id}
        demand(all(variable not in variables_of(row) for row in new_rows.values()),
               f'step {number}: eliminated variable survives substitution')
        maximum = max(map(degree, new_rows.values()), default=-1)
        demand(maximum <= cap, f'step {number}: actual degree exceeds cap')
        alive.remove(variable)
        demand(all(variables_of(row) <= alive for row in new_rows.values()),
               f'step {number}: inactive coordinate survives')
        rows = new_rows
        replay_steps.append({'number':number,'source_row':row_id,
                             'variable':variable,'coefficient':coefficient,
                             'restoration_degree':degree(restoration),
                             'maximum_residual_degree':maximum})

    claimed_rows = {}
    for item in certificate['rows']:
        row_id = item['source_row']
        demand(type(row_id) is int and row_id not in claimed_rows,
               'duplicate or invalid endpoint source-row identifier')
        claimed_rows[row_id] = read_polynomial(item['terms'], dimension)
    demand(rows == claimed_rows, 'literal endpoint differs from exact substitutions')
    actual_live = set().union(*(variables_of(row) for row in rows.values()))
    demand(actual_live == alive, 'remaining ambient dimension includes unused variables')
    demand(all(rows.values()), 'endpoint contains a zero residual counted as live')

    metrics = {
        'variables_remaining':len(alive),
        'residuals_remaining':len(rows),
        'residual_terms':sum(len(row) for row in rows.values()),
        'residual_height':max(abs(c) for row in rows.values() for c in row.values()),
        'maximum_residual_degree':max(map(degree, rows.values())),
    }
    for name in ('variables_remaining','residuals_remaining','residual_terms','residual_height'):
        demand(certificate.get(name) == metrics[name], 'endpoint metric differs: '+name)
    demand(dimension-len(certificate['steps']) == len(alive), 'variable count mismatch')
    demand(len(source['residuals'])-len(certificate['steps']) == len(rows), 'residual count mismatch')

    expanded = collect_squares(rows) if with_expansion else None
    if expanded is not None:
        demand(degree(expanded) == 2*metrics['maximum_residual_degree'],
               'sum-of-squares total degree differs from the exact expected degree')
        metrics['polynomial_degree'] = degree(expanded)
        metrics['polynomial_terms'] = len(expanded)
        metrics['polynomial_height'] = max(map(abs, expanded.values()))
        canonical = json.dumps(serialize(expanded), separators=(',',':')).encode()
        metrics['expanded_terms_compact_json_sha256'] = hashlib.sha256(canonical).hexdigest()
    return {'metrics':metrics,'retained_original_variables':sorted(alive),
            'retained_original_rows':sorted(rows),'checked_steps':replay_steps}, expanded


def corruption_controls(source, certificate):
    demand(certificate['steps'], 'mutation controls need a nonempty contraction')
    mutations = []
    wrong_sign = copy.deepcopy(certificate)
    wrong_sign['steps'][0]['coefficient'] *= -1
    mutations.append(('pivot unit sign', wrong_sign))
    wrong_restoration = copy.deepcopy(certificate)
    restoration = wrong_restoration['steps'][0]['restoration']
    if restoration:
        restoration[0][0] += 1 if restoration[0][0] != -1 else -1
    else:
        restoration.append([1, []])
    mutations.append(('restoration coefficient', wrong_restoration))
    wrong_endpoint = copy.deepcopy(certificate)
    wrong_endpoint['rows'][0]['terms'][0][0] += 1 if wrong_endpoint['rows'][0]['terms'][0][0] != -1 else -1
    mutations.append(('endpoint coefficient', wrong_endpoint))
    rejected = []
    for label, mutant in mutations:
        try:
            replay(source, mutant, with_expansion=False)
        except ValueError as error:
            rejected.append({'mutation':label,'rejection':str(error)})
        else:
            raise ValueError('corrupted certificate accepted: '+label)
    return rejected


def verify_path(certificate_path, source_override=None, expanded_dir=None):
    certificate_data = certificate_path.read_bytes()
    certificate = json.loads(certificate_data)
    source_path = source_override or Path(certificate['source'])
    if not source_path.is_absolute():
        source_path = certificate_path.parent / source_path
    source_data = source_path.read_bytes()
    demand(hashlib.sha256(source_data).hexdigest() == certificate['source_sha256'],
           'source bytes do not match the certificate pin')
    source = json.loads(source_data)
    result, expanded = replay(source, certificate)
    result.update(certificate=str(certificate_path),
                  certificate_sha256=hashlib.sha256(certificate_data).hexdigest(),
                  source_sha256=hashlib.sha256(source_data).hexdigest(),
                  corruptions_rejected=corruption_controls(source, certificate))
    if expanded_dir:
        expanded_dir.mkdir(parents=True,exist_ok=True)
        target = expanded_dir/(certificate_path.stem+'.expanded.json')
        payload = {'indices':'original source coordinates',
                   'source_sha256':result['source_sha256'],
                   'certificate_sha256':result['certificate_sha256'],
                   'terms':serialize(expanded),'metrics':result['metrics']}
        target.write_text(json.dumps(payload,indent=2)+'\n')
        result['expanded_file'] = str(target)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificates',type=Path,nargs='+')
    parser.add_argument('--source',type=Path)
    parser.add_argument('--receipt',type=Path)
    parser.add_argument('--expanded-dir',type=Path)
    args = parser.parse_args()
    results = [verify_path(p,args.source,args.expanded_dir) for p in args.certificates]
    receipt = {'verifier':'independent exponent-map polynomial replay',
               'semantics':'polynomial bijection on unrestricted integer zero sets',
               'results':results}
    if args.receipt:
        args.receipt.parent.mkdir(parents=True,exist_ok=True)
        args.receipt.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps([{'certificate':r['certificate'],**r['metrics'],
                       'checked_unit_projections':len(r['checked_steps']),
                       'corruptions_rejected':len(r['corruptions_rejected'])}
                      for r in results],indent=2))


if __name__ == '__main__':
    main()
