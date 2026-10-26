#!/usr/bin/env python3
"""Emit the prime-supported-spacing quartic from the frozen P210 source.

Only Python's standard library is required.  Semantic changes are proved in
the report; this deterministic emitter does not itself establish them.
"""
import copy
import hashlib
import json
import math
from pathlib import Path
import zipfile

ROOT = Path(__file__).resolve().parents[1]
PARENT_ZIP = ROOT / 'inherited/ConZFC_Pell_Growth_210_2026-10-25.zip'
MEMBER = 'ConZFC_Pell_Growth_210_2026-10-25/equations/principal210/equation.json'
C = 524309


def canonical(obj):
    return (json.dumps(obj, sort_keys=True, indent=2) + '\n').encode()


def polynomial(terms):
    result = {}
    for coefficient, monomial in terms:
        key = tuple(sorted(monomial))
        result[key] = result.get(key, 0) + coefficient
    return {m: v for m, v in result.items() if v}


def terms(p):
    return [[v, list(m)] for m, v in sorted(p.items()) if v]


def add(*ps):
    out = {}
    for p in ps:
        for m, c in p.items():
            out[m] = out.get(m, 0) + c
    return {m: c for m, c in out.items() if c}


def mul(p, q):
    out = {}
    for m, c in p.items():
        for n, d in q.items():
            key = tuple(sorted(m + n))
            out[key] = out.get(key, 0) + c * d
    return {m: c for m, c in out.items() if c}


def collect(equation):
    out = {}
    for row in equation['residuals']:
        p = polynomial(row['terms'])
        out = add(out, mul(p, p))
    return out


def profile(equation, expansion):
    return {
        'variables': len(equation['variables']),
        'squared_residuals': len(equation['residuals']),
        'degree': max(map(len, expansion)),
        'monomials': len(expansion),
        'coefficient_height': max(map(abs, expansion.values())),
        'maximum_residual_coefficient': max(abs(c) for r in equation['residuals'] for c, _ in r['terms']),
        'residual_monomials': sum(len(r['terms']) for r in equation['residuals']),
    }


def formatted(p, latex=False):
    pieces = []
    for monomial, coefficient in sorted(p.items(), key=lambda kv: (len(kv[0]), kv[0])):
        powers = {}
        for index in monomial:
            powers[index] = powers.get(index, 0) + 1
        if latex:
            body = ' '.join('x_{%d}' % i + ('^{%d}' % k if k != 1 else '') for i, k in powers.items())
        else:
            body = '*'.join('x%d' % i + ('^%d' % k if k != 1 else '') for i, k in powers.items())
        number = str(abs(coefficient)) if abs(coefficient) != 1 or not body else ''
        separator = '' if latex or not number or not body else '*'
        item = number + separator + body
        sign = '-' if coefficient < 0 else '+'
        pieces.append((sign, item))
    if not pieces:
        return '0'
    return ''.join((('-' if s == '-' else '') if i == 0 else ' ' + s + ' ') + b for i, (s, b) in enumerate(pieces))


def build():
    with zipfile.ZipFile(PARENT_ZIP) as z:
        raw = z.read(MEMBER)
        parent = json.loads(raw)
        license_bytes = z.read('ConZFC_Pell_Growth_210_2026-10-25/LICENSE')
    if len(parent['variables']) != 210 or len(parent['residuals']) != 150:
        raise ValueError('Wrong parent dimensions')
    expected_names = {0: 't0', 2: 'growth.F', 3: 'choose0.output',
                      4: 'beta.y_plus_one', 178: 'cofinal.horizon_root',
                      206: 'beta.odd_multiplier_half', 207: 'growth_pell.X',
                      208: 'growth_pell.tF', 209: 'growth_pell.odd_half'}
    for i, name in expected_names.items():
        if parent['variables'][i]['name'] != name:
            raise ValueError(('Wrong parent binding', i, name))
    if any(C % p == 0 for p in range(2, math.isqrt(C) + 1)):
        raise ValueError('Growth modulus must be prime')
    old = [polynomial(r['terms']) for r in parent['residuals']]
    changes = {
        # Undo the parent's row3 <- row3 + beta shear before modifying beta.
        3: add(old[3], {m: -v for m, v in old[146].items()}),
        125: polynomial([[1, [0]], [-32, []], [-128, [178]], [-128, [178, 178]]]),
        146: polynomial([[1, [4]], [-1, []], [-1, [2, 3]]]),
        147: polynomial([[1, [208]], [-C, [0, 2]]]),
        148: polynomial([[1, [207, 207]], [-1, [208, 208]], [-2, [2, 208]], [-1, []]]),
        149: polynomial([[1, [2]], [1, [0]], [-C, [0, 209]]]),
    }
    rows = [changes.get(i, p) for i, p in enumerate(old)]
    live = sorted({j for row in rows for monomial in row for j in monomial})
    if live != [i for i in range(210) if i != 206]:
        raise ValueError('Unexpected liveness after spacing replacement')
    renumber = {old_i: new_i for new_i, old_i in enumerate(live)}
    new_variables = [copy.deepcopy(parent['variables'][i]) for i in live]
    new_variables[207]['name'] = 'growth_pell.c_t_F'
    new_variables[208]['name'] = 'growth_pell.congruence_quotient'
    new_variables[178]['name'] = 'horizon.odd_square_parameter'
    new_rows = []
    for i, p in enumerate(rows):
        label = parent['residuals'][i]['label']
        if i == 146:
            label = 'beta.binomial_spacing'
        if i == 149:
            label = 'growth_pell.oriented_residue'
        q = {tuple(renumber[j] for j in m): v for m, v in p.items()}
        if max(map(len, q)) > 2:
            raise ValueError('Nonquadratic residual')
        new_rows.append({'label': label, 'terms': terms(q)})
    equation = {
        'schema': 'conzfc-prime-supported-spacing-v1',
        'domain': 'unrestricted integers',
        'polynomial': 'sum(square(row) for row in residuals)',
        'variables': new_variables,
        'residuals': new_rows,
        'growth_modulus': C,
        'parent_equation_sha256': hashlib.sha256(raw).hexdigest(),
    }
    expansion = collect(equation)
    metrics = profile(equation, expansion)
    parent_metrics = profile(parent, collect(parent))
    certificate = {
        'schema': 'prime-supported-spacing-semantic-change-v1',
        'parent_archive_sha256': hashlib.sha256(PARENT_ZIP.read_bytes()).hexdigest(),
        'parent_member': MEMBER,
        'parent_equation_sha256': hashlib.sha256(raw).hexdigest(),
        'growth_modulus': C,
        'horizon': 't = 32*(2*z+1)^2',
        'completeness_horizons': 't = 32*c^(2*k), k >= 1',
        'new_spacing': 'y = F*B, B = binom(F+t,t)',
        'deleted_coordinate': 206,
        'old_to_new': [[i, renumber[i]] for i in live],
        'changed_rows_before_renumbering': [
            {'row': i, 'before': terms(old[i]), 'after': terms(changes[i]),
             'status': 'invertible residual-row operation' if i == 3 else 'semantic change; see report'}
            for i in sorted(changes)
        ],
    }
    eqdir = ROOT / 'equations'
    eqdir.mkdir(exist_ok=True)
    files = {
        'equation.json': equation,
        'expanded_polynomial.json': {'schema': 'sparse-polynomial-v1', 'variables': 209, 'terms': terms(expansion)},
        'metrics.json': metrics,
        'parent_metrics.json': parent_metrics,
        'transformation.json': certificate,
    }
    for name, obj in files.items():
        (eqdir / name).write_bytes(canonical(obj))
    (ROOT / 'inherited/LICENSE.parent').write_bytes(license_bytes)
    text_rows = ['R%d = %s' % (i, formatted(polynomial(r['terms']))) for i, r in enumerate(new_rows)]
    (eqdir / 'residuals.txt').write_text('\n'.join(text_rows) + '\n')
    (eqdir / 'variables.tsv').write_text('index\tname\tkind\n' + ''.join('%d\t%s\t%s\n' % (i, v['name'], v['kind']) for i, v in enumerate(new_variables)))
    latex_rows = ['% Literal quadratic residuals for the 209-variable equation.', r'\begingroup\small', r'\setlength{\jot}{2pt}']
    for i, row in enumerate(new_rows):
        p = polynomial(row['terms'])
        # Chunk by terms, keeping each expression on a page if possible.
        ordered = sorted(p.items(), key=lambda kv: (len(kv[0]), kv[0]))
        chunks = [ordered[k:k+5] for k in range(0, len(ordered), 5)]
        latex_rows.append(r'\begin{align*}')
        for j, chunk in enumerate(chunks):
            s = formatted(dict(chunk), latex=True)
            if j:
                s = ('+ ' + s) if not s.startswith('-') else s
            prefix = 'R_{%d} ={}& ' % i if j == 0 else '&{} '
            suffix = r' \\' if j < len(chunks)-1 else ''
            latex_rows.append(prefix + s + suffix)
        latex_rows.append(r'\end{align*}')
    latex_rows.append(r'\endgroup')
    (ROOT / 'report/residuals.tex').write_text('\n'.join(latex_rows) + '\n')
    macros = {'NumVariables': metrics['variables'], 'NumRows': metrics['squared_residuals'],
              'NumMonomials': metrics['monomials'], 'PolyHeight': metrics['coefficient_height'],
              'RowHeight': metrics['maximum_residual_coefficient'], 'GrowthPrime': C,
              'NumResidualTerms': metrics['residual_monomials']}
    (ROOT / 'report/metrics.tex').write_text('\n'.join(r'\newcommand{\%s}{%s}' % (k,v) for k,v in macros.items()) + '\n')
    print(json.dumps({'new': metrics, 'parent': parent_metrics}, indent=2))


if __name__ == '__main__':
    build()
