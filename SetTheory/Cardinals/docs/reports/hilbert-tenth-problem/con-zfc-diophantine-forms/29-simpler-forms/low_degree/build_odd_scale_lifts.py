#!/usr/bin/env python3
"""Combine the wave-3 odd-scale theorem with the delivered integer lifts.

This script checks only polynomial identities and the exact size/degree ledger.
The existential-solvability theorem is proved in ODD_SCALE_LIFTS_PROOF.md.
"""
from pathlib import Path
import hashlib
import json
import sys

ROOT = Path(__file__).resolve().parent
UP = ROOT / 'upstream/20-root12/domains'
sys.path.insert(0, str(UP))
from sparse_poly import Poly

PIN = 'ae3007ca4467011e0e051c84acb4a1dd13971b0e'
PARAMS = {'s_pos1', 's_pos2', 's_pos3'}
SOURCES = ['integer54_quartic.json', 'integer45_degree6.json', 'integer39_degree8.json']
OUT = ROOT / 'generated'
OUT.mkdir(exist_ok=True)
results = []

def evaluate(p, values):
    total = 0
    for monomial, coefficient in p.terms.items():
        term = coefficient
        for variable, exponent in monomial:
            term *= values[variable] ** exponent
        total += term
    return total

for filename in SOURCES:
    path = UP / filename
    packet = json.loads(path.read_text())
    constants = packet.get('fixed_numerals', packet.get('fixed_integer_coefficients'))
    if isinstance(constants, dict):
        constants = list(constants)
    names = packet['variables']
    env = {name: Poly.var(name) for name in names + constants}
    residuals = [eval(item, {'__builtins__': {}}, env) for item in packet['residuals']]
    s = Poly.var('s')
    x, y, z = [Poly.var('s_pos' + str(j)) for j in (1, 2, 3)]
    guard = s - 1 - x*x - y*y - z*(z+1)
    guard_indices = [j for j, p in enumerate(residuals) if p == guard or p == -guard]
    assert len(guard_indices) == 1
    guard_index = guard_indices[0]
    assert all(not (p.symbols & PARAMS) for j, p in enumerate(residuals) if j != guard_index)
    new_names = [('v_scale' if name == 's' else name) for name in names if name not in PARAMS]
    new_scale = 2*Poly.var('v_scale') + 1
    kept = [p for j, p in enumerate(residuals) if j != guard_index]
    new_residuals = [p.substitute({'s': new_scale}) for p in kept]
    n = len(new_names)
    assert n == len(names) - 3 and len(set(new_names)) == n
    assert set().union(*(p.symbols for p in new_residuals)) == set(new_names + constants)
    degrees = [p.degree(new_names) for p in new_residuals]
    polynomial = sum((p*p for p in new_residuals), Poly(0))
    degree = polynomial.degree(new_names)
    assert degree == packet.get('exact_degree', packet.get('exact_total_degree'))
    assert degree == 2 * max(degrees)
    assert all(p.substitute({'s': new_scale}) == r for p, r in zip(kept, new_residuals))
    if degree == 4:
        monomial = (('tau', 4),)
        assert polynomial.terms[monomial] == 1
        certificate = {'variable_monomial': 'tau^4', 'coefficient': '1'}
    elif degree == 6:
        monomial = (('Bm1', 2), ('Jrep', 2), ('L', 2), ('v_scale', 2))
        assert polynomial.terms[monomial] == 4
        certificate = {'variable_monomial': 'Jrep^2 L^2 v_scale^2', 'coefficient': '4 Bm1^2 > 0'}
    else:
        monomial = (('Bm1', 6), ('Jrep', 6), ('v_scale', 2))
        assert polynomial.terms[monomial] == 4
        certificate = {'variable_monomial': 'Jrep^6 v_scale^2', 'coefficient': '4 Bm1^6 > 0'}
    # These signed evaluations are diagnostics for transcription only.
    for trial in range(32):
        values = {name: ((trial+3)*(i+5) % 23)-11 for i, name in enumerate(new_names + constants)}
        old_values = values | {'s': 2*values['v_scale'] + 1}
        assert [evaluate(p, old_values) for p in kept] == [evaluate(p, values) for p in new_residuals]
    # Transfer the entire compiler tuple, including both masks and beta.
    # The theorem in ODD_SCALE_LIFTS_PROOF.md checks the full odd-scale
    # interface for this smaller, materialized package-19 tuple.
    binding_path = ROOT / 'upstream/19-wang943/COEFFICIENT_BINDING.json'
    chosen = json.loads(binding_path.read_text())
    binding = {
        'tuple_id': chosen['variant'],
        'manifest': '../upstream/19-wang943/COEFFICIENT_BINDING.json',
        'aliases': chosen['port_aliases'],
        'numeric_encoding': chosen['encoding'],
        'numeric_coefficients': {
            p['name']: {
                'gzip_file': '../upstream/19-wang943/' + p['path'] + '.gz',
                'bit_length': p['bit_length'],
                'size_bytes': p['bytes'],
                'sha256': p['sha256'],
                'gzip_sha256': p['gzip_sha256'],
            } for p in chosen['files']
        },
        'transfer_proof': '../ODD_SCALE_LIFTS_PROOF.md, Section 3',
        'note': 'Whole compact943 tuple. MF is the shifted source port. Original4094 tuple in source packets is provenance only.',
    }
    artifact = {
        'name': f'integer{n}_degree{degree}_odd_scale',
        'domain': 'unrestricted integers',
        'variables': new_names,
        'variable_count': n,
        'fixed_numerals': constants,
        'coefficient_binding': binding,
        'repository_pin': PIN,
        'parent_file': '../upstream/20-root12/domains/' + filename,
        'parent_sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
        'removed_positive_guard': 's = 1+s_pos1^2+s_pos2^2+s_pos3(s_pos3+1)',
        'odd_scale_substitution': 's = 2 v_scale + 1',
        'deleted_parent_residual_index_zero_based': guard_index,
        'residuals': [str(p) for p in new_residuals],
        'equation_count': len(new_residuals),
        'residual_degrees': degrees,
        'exact_degree': degree,
        'single_polynomial': 'sum of squares of the listed residuals',
        'exact_degree_certificate': certificate,
        'expanded_symbolic_terms': len(polynomial.terms),
        'proof': '../ODD_SCALE_LIFTS_PROOF.md',
        'scope': 'Exact symbolic construction; ordinary proof depends on the stated existing Pell/compiler results, not a new Lean or Rocq proof.',
    }
    (OUT / (artifact['name']+'.json')).write_text(json.dumps(artifact, indent=2)+'\n')
    result = {key: artifact[key] for key in ['name', 'variable_count', 'equation_count', 'exact_degree', 'residual_degrees', 'expanded_symbolic_terms', 'exact_degree_certificate']}
    result['parent_variables'] = len(names)
    result['parent_equations'] = len(residuals)
    result['identity_checks'] = len(new_residuals)
    result['signed_transcription_trials'] = 32
    results.append(result)

(OUT / 'ODD_SCALE_LIFTS_CHECKS.json').write_text(json.dumps({'results': results, 'no_semantic_claim_from_testing': True}, indent=2)+'\n')
print(json.dumps(results, indent=2))
