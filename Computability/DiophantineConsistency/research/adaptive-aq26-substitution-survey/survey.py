#!/usr/bin/env python3
"""Check 14 direct witness bindings among the AQ26 residuals."""
import hashlib
import json
from pathlib import Path
import runpy

if not __debug__:
    raise RuntimeError('optimized Python is not supported')

D = Path(__file__).resolve().parent
parent = D.parent / 'adaptive-square-sums26-degree8'
pins = {
    'candidate.json': 'd8e80e15d74271ba62877e841198a85729c0c4a74a5927927591b9ec2204b1a5',
    'verify_degree.py': 'fb848e76c60c9533a1262b5a60f10222d4a37055d6e5e9c740315427fdd30dfb',
}
for name, expected in pins.items():
    if hashlib.sha256((parent / name).read_bytes()).hexdigest() != expected:
        raise ValueError(('parent pin', name))

# Each triple substitutes the value forced by one named square residual.
# These include both orientations of every residual that binds a witness to
# a named DAG row; qValueVariable has two distinct bindings.
choices = [
    ('scaleVariable', 'M', 'scaleDifference', 8),
    ('mainScaleVariable', 'U', 'mainScaleDifference', 6),
    ('rankVariable', 'R', 'rankDifference', 5),
    ('cVariable', 'c', 'cDifference', 5),
    ('ellVariable', 'ell', 'ellDifference', 8),
    ('cSquareVariable', 'c2', 'cSquareDifference', 6),
    ('zValueVariable', 'ZComputed', 'zDifference', 8),
    ('dValueVariable', 'DstarComputed', 'dDifference', 6),
    ('vValueVariable', 'VComputed', 'vDifference', 9),
    ('deltaVariable', 'DeltaComputed', 'deltaDifference', 5),
    ('qSquareVariable', 'q2', 'qSquareDifference', 5),
    ('productVariable2', 'E', 'product2Difference', 5),
    ('qValueVariable', 'QComputed', 'qSignedDifference', 5),
    ('qValueVariable', 'g71', 'g72', 6),
]
ns = runpy.run_path(str(parent / 'verify_degree.py'))
P, graph, names = ns['P'], ns['g'], ns['names']
factors, rows = ns['factors_names'], ns['rows']
if names[26:] != ['beta', 'K0', 'MC', 'MF']:
    raise ValueError('unexpected port order')
if (len(choices) != 14 or len({(v, r) for v, _, r, _ in choices}) != 14 or
        set(factors) - {removed for _, _, removed, _ in choices} !=
        {'A0', 'A1', 'auxResidual'}):
    raise ValueError('residual coverage')
declared = set()
for factor in factors:
    _, op, left, right = rows[factor]
    if op != '-':
        raise ValueError(('residual is not a difference', factor))
    for witness, expression in ((left, right), (right, left)):
        if witness in names[:26] and isinstance(expression, str):
            declared.add((witness, expression, factor))
if declared != {(v, r, d) for v, r, d, _ in choices}:
    raise ValueError(('immediate binding coverage', sorted(declared)))

result = []
for var, replacement, removed, expected_degree in choices:
    if rows[removed] not in ([removed, '-', var, replacement],
                            [removed, '-', replacement, var]):
        raise ValueError(('binding mismatch', var))
    i = names.index(var)
    value = graph[replacement]
    if any(m[i] for m in value.d):
        raise ValueError(('self-dependent replacement', var))
    powers = [P.lift(1)]

    def substitute(poly):
        out = P.lift(0)
        for monomial, coefficient in poly.d.items():
            exponent = monomial[i]
            while exponent >= len(powers):
                powers.append(powers[-1] * value)
            base = list(monomial)
            base[i] = 0
            out = out + P({tuple(base): coefficient}) * powers[exponent]
        return out

    if substitute(graph[removed]).d:
        raise ValueError(('deleted residual is nonzero', removed))
    polys = {name: substitute(graph[name]) for name in factors if name != removed}
    degrees = {name: max((sum(m[:26]) for m in poly.d), default=-1)
               for name, poly in polys.items()}
    maximum = max(degrees.values())
    if maximum != expected_degree or maximum <= 4:
        raise ValueError(('unexpected residual degree', var, maximum))

    # Certify survival after fixing the ports: find a maximum-degree witness
    # monomial whose entire coefficient is a nonzero integer times beta^k.
    # The actual beta = (2^47)^2011 - 1 is positive, so no specialization
    # cancellation can remove that coefficient.
    certificate = None
    for name, poly in polys.items():
        if degrees[name] != maximum:
            continue
        groups = {}
        for monomial, coefficient in poly.d.items():
            if sum(monomial[:26]) == maximum:
                groups.setdefault(monomial[:26], []).append((monomial[26:], coefficient))
        for witness, terms in sorted(groups.items()):
            if len(terms) == 1 and terms[0][1] and terms[0][0][1:] == (0, 0, 0):
                certificate = {'residual': name, 'witness_exponents': list(witness),
                               'beta_exponent': terms[0][0][0], 'coefficient': terms[0][1]}
                break
        if certificate:
            break
    if certificate is None:
        raise ValueError(('no beta-only leading certificate', var))
    result.append({'variable': var, 'replacement': replacement, 'removed': removed,
                   'max_residual_degree': maximum, 'sum_of_squares_degree': 2 * maximum,
                   'leading_certificate': certificate})

output = {'status': 'PASS_DIRECT_SUBSTITUTION_SURVEY', 'parent_sha256': pins['candidate.json'],
          'scope': '14 direct residual substitutions only; not a model proof or minimality result',
          'results': result}
print(json.dumps(output, indent=2, sort_keys=True))
