#!/usr/bin/env python3
"""Generate the report's exact metric and literal-residual inputs.

Standard library only. Run from any working directory. The authoritative
equation is portable/equations/primary/natural/equation.json.
"""
from pathlib import Path
from collections import Counter
import hashlib
import json

ROOT = Path(__file__).resolve().parents[1]


def tex_term(coefficient, monomial, first):
    sign = ('-' if coefficient < 0 else '') if first else (' - ' if coefficient < 0 else ' + ')
    c = abs(coefficient)
    factors = []
    width = 8.0
    for index, power in sorted(Counter(monomial).items()):
        factors.append('z_{%d}' % index + ('^{%d}' % power if power != 1 else ''))
        width += 6 + 3.7 * len(str(index)) + (4 if power != 1 else 0)
    literal = str(c) if c != 1 or not factors else ''
    width += 4.7 * len(literal)
    return sign + literal + ''.join(factors), width


def main():
    eqpath = ROOT / 'portable/equations/primary/natural/equation.json'
    polypath = eqpath.with_name('expanded_polynomial.json')
    eq = json.loads(eqpath.read_text())
    sparse = json.loads((ROOT / 'portable/equations/sparse/natural/equation.json').read_text())
    raw = json.loads((ROOT / 'portable/equations/primary/raw/equation.json').read_text())
    m, s = eq['metrics'], sparse['metrics']
    values = {
        'LastVar': len(eq['variables']) - 1,
        'NumVars': len(eq['variables']), 'NumRows': len(eq['residuals']),
        'LastRow': len(eq['residuals']) - 1,
        'NumTerms': f"{m['expanded_monomials']:,}",
        'CoeffHeight': f"{m['max_abs_expanded_coefficient']:,}",
        'SavedVars': 349 - len(eq['variables']),
        'SparseVars': len(sparse['variables']),
        'SparseTerms': f"{s['expanded_monomials']:,}",
        'SparseRows': len(sparse['residuals']),
        'SparseHeight': f"{s['max_abs_expanded_coefficient']:,}",
        'Horizon': 12, 'SeedCount': 16, 'DerivedCount': 1, 'PowerCount': 19,
        'RawVars': len(raw['variables']), 'RawRows': len(raw['residuals']),
        'Eliminations': m['nonnegative_certified_eliminations'],
        'IntegerVars': 3 * len(eq['variables']),
        'EquationHash': hashlib.sha256(eqpath.read_bytes()).hexdigest(),
        'PolynomialHash': hashlib.sha256(polypath.read_bytes()).hexdigest(),
    }
    metrics = '% Generated from exact JSON by code/generate_report_inputs.py.\n'
    metrics += ''.join('\\newcommand{\\%s}{%s}\n' % item for item in values.items())
    (ROOT / 'report/metrics.tex').write_text(metrics)
    lines = ['% Complete literal residuals, generated from the frozen JSON.']
    for i, row in enumerate(eq['residuals']):
        chunks, chunk, width = [], '', 0.0
        for j, (coefficient, monomial) in enumerate(row['terms']):
            term, term_width = tex_term(coefficient, monomial, j == 0)
            if chunk and width + term_width > 385:
                chunks.append(chunk)
                chunk, width = '', 0.0
            chunk += term
            width += term_width
        chunks.append(chunk or '0')
        lines.append('\\begin{align*}')
        lines.append('r_{%d} &= %s' % (i, chunks[0]) + (' \\\\' if len(chunks) > 1 else ''))
        for j, chunk in enumerate(chunks[1:], 1):
            lines.append('&\\quad ' + chunk + (' \\\\' if j + 1 < len(chunks) else ''))
        lines.append('\\end{align*}')
    (ROOT / 'report/residuals.tex').write_text('\n'.join(lines) + '\n')
    print(json.dumps({'residuals': len(eq['residuals']), 'terms_in_residuals': sum(len(r['terms']) for r in eq['residuals']), 'generated': ['report/metrics.tex', 'report/residuals.tex']}, indent=2))


if __name__ == '__main__':
    main()
