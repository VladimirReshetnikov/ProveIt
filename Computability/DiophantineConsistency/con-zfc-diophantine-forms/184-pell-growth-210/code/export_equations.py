#!/usr/bin/env python3
"""Render the exact residuals; never change the authoritative coefficient JSON.

The inherited independent strict TeX parser checks this generated output back
against all literal coefficients. No mathematical statement is inferred from
the typography.
"""
from collections import Counter
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parents[1]


def term(c, monomial, tex=False, first=False):
    sign = ('-' if c < 0 else '') if first else (' - ' if c < 0 else ' + ')
    powers = sorted(Counter(monomial).items())
    if tex:
        variables = ' '.join('x_{'+str(i)+'}' + ('^{'+str(k)+'}' if k > 1 else '')
                             for i, k in powers)
    else:
        variables = '*'.join('x'+str(i) + ('^'+str(k) if k > 1 else '')
                              for i, k in powers)
    coefficient = str(abs(c)) if abs(c) != 1 or not monomial else ''
    join = '*' if coefficient and variables and not tex else ''
    return sign + coefficient + join + variables


def export(profile):
    folder = ROOT/'equations'/profile
    eq = json.loads((folder/'equation.json').read_text())
    metrics = json.loads((folder/'metrics.json').read_text())
    lines = ['Domain: all coordinates independently range over the integers.',
             f'P(x0,...,x{metrics["variables"]-1}) = sum(Rj^2 for j=0,...,{metrics["rows"]-1}).',
             'The equation is P=0. All residuals below are literal polynomials.', '']
    tex = ['% Literal residuals; checked independently against equation.json.',
           r'{\small', r'\setlength{\jot}{2pt}', r'\allowdisplaybreaks[0]']
    for j, row in enumerate(eq['residuals']):
        terms = sorted(row['terms'], key=lambda item: item[1])
        lines.append(f'R{j} = '+''.join(term(c, m, first=i == 0)
                                      for i, (c, m) in enumerate(terms)))
        tex.extend([f'% BEGIN RESIDUAL {j}', r'\begin{align*}'])
        for start in range(0, len(terms), 6):
            expression = ''.join(term(c, m, tex=True, first=start+i == 0)
                                 for i, (c, m) in enumerate(terms[start:start+6]))
            prefix = 'R_{'+str(j)+'} ={}& ' if start == 0 else '&{} '
            tex.append(prefix+expression+(r' \\' if start+6 < len(terms) else ''))
        tex.extend([r'\end{align*}', f'% END RESIDUAL {j}'])
    tex.append('}')
    (folder/'residuals.txt').write_text('\n'.join(lines)+'\n')
    (folder/'residuals.tex').write_text('\n'.join(tex)+'\n')
    (folder/'variables.tsv').write_text('index\thistorical_coordinate_name\n'+''.join(
        f'{i}\t{v["name"]}\n' for i, v in enumerate(eq['variables'])))
    if profile == 'principal210':
        (ROOT/'report/residuals.tex').write_text('\n'.join(tex)+'\n')
        macros = {'NV':metrics['variables'], 'LastVar':metrics['variables']-1,
                  'NR':metrics['rows'], 'LastRow':metrics['rows']-1,
                  'NT':metrics['monomials'], 'Height':metrics['height']}
        (ROOT/'report/metrics.tex').write_text('% Exact literal metrics.\n'+''.join(
            '\\newcommand{\\'+key+'}{'+str(value)+'}\n' for key, value in macros.items()))
    return {'profile':profile, **metrics}


if __name__ == '__main__':
    print(json.dumps([export(name) for name in ['principal210','balanced214']], indent=2))
