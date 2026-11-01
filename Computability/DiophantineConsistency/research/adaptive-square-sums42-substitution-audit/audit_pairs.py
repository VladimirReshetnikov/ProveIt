#!/usr/bin/env python3
"""Audit pairs of direct named-coordinate substitutions in the quartic graph."""
import contextlib
import hashlib
import io
import itertools
import runpy
from pathlib import Path

D = Path(__file__).resolve().parent
base = D / 'audit.py'
if hashlib.sha256(base.read_bytes()).hexdigest() != 'a65f09ba02f02843c9b268179d650fab4635f9109d9121a83924c672d63282cd':
    raise ValueError('single-substitution verifier drift')
with contextlib.redirect_stdout(io.StringIO()):
    data = runpy.run_path(str(base))
graph, names, m, vals = data['D'], data['names'], data['m'], data['v']
factors, substitute = data['factors'], data['substitute']
specs = []
for name, op, left, right in graph['source']:
    if not name.endswith('Difference') or not isinstance(left, str) or left not in graph['witnesses'] or not isinstance(right, str):
        continue
    j, expression = names.index(left), vals[right]
    if any(monomial[j] for monomial in expression):
        raise ValueError(('self-dependent definition', left))
    specs.append((left, name, j, expression))
if len(specs) != 29:
    raise ValueError(('definition count', len(specs)))
blocked = 0
for first, second in itertools.combinations(specs, 2):
    first_depends_second = any(monomial[second[2]] for monomial in first[3])
    second_depends_first = any(monomial[first[2]] for monomial in second[3])
    if first_depends_second and second_depends_first:
        raise ValueError(('cyclic definitions', first[0], second[0]))
    if second_depends_first:
        first, second = second, first
    def apply_both(poly):
        return substitute(substitute(poly, first[2], first[3]), second[2], second[3])
    if apply_both(vals[first[1]]) or apply_both(vals[second[1]]):
        raise ValueError(('removed defining residual does not vanish', first[0], second[0]))
    for square, residual in factors:
        if residual in (first[1], second[1]):
            continue
        transformed = apply_both(vals[residual])
        groups = {}
        for monomial, coefficient in transformed.items():
            if sum(monomial[:m]) > 2:
                groups.setdefault(monomial[:m], []).append((monomial[m:], coefficient))
        witness = next(((monomial, terms[0]) for monomial, terms in groups.items()
                        if len(terms) == 1 and not any(terms[0][0][1:]) and terms[0][1]), None)
        if witness:
            monomial, (portpowers, coefficient) = witness
            support = [(names[i], power) for i, power in enumerate(monomial) if power]
            print('BLOCKED', first[0], second[0], 'by', residual,
                  'degree', sum(monomial), 'coefficient', coefficient,
                  'beta_power', portpowers[0], 'monomial', support)
            blocked += 1
            break
    else:
        raise ValueError(('no nonzero pure-beta degree witness', first[0], second[0]))
if blocked != 406:
    raise ValueError(('pair count', blocked))
print('PASS: all 406 direct-substitution pairs leave a residual of degree >2 when beta is nonzero')
