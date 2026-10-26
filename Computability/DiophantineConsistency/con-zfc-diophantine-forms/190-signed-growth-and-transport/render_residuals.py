#!/usr/bin/env python3
"""Print every sparse quartic residual in TeX; no symbolic algebra package."""
from collections import Counter
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parent


def term(coefficient, monomial, first):
    sign = '-' if coefficient < 0 else ('' if first else '+')
    absolute = abs(coefficient)
    scalar = str(absolute) if absolute != 1 or not monomial else ''
    factors = ''
    for index, exponent in sorted(Counter(monomial).items()):
        factors += rf'\xi_{{{index}}}'
        if exponent != 1:
            factors += rf'^{{{exponent}}}'
    return sign + scalar + factors


def make_text():
    equation = json.loads((ROOT/'quartic/equations/affine209_F64/equation.json').read_text())
    out = [r'''\section{The complete 209-variable quartic}
\label{app:residuals}

The unknowns are exactly \(\xi_0,\ldots,\xi_{208}\in\Z\). The following
149 residuals define \(Q_{209}=\sum_{j=0}^{148}R_j^2\). Products are
ordinary multiplication; every residual has degree at most two.
The independent archive checker parses every displayed coefficient and
monomial below and compares them with the literal JSON equation.
The fully collected 5,486-term expansion is supplied as data.

The lower-height companion is also completely specified by this list.
First replace every \(\xi_2\) by \(2\xi_2\), then divide residual 148
by two (its coefficients after substitution are all even). Call the
resulting residuals \(\widetilde R_j\). Set
\[
 S_{98}=\widetilde R_{98}+4\widetilde R_{135},\qquad
 S_{124}=\widetilde R_{124}+6\widetilde R_{135},
\]
and \(S_j=\widetilde R_j\) for every other index. The second equation
is \(\sum_{j=0}^{148}S_j^2=0\). This transformation gives its full
6,654-term expansion without any additional choice of constants.

\begingroup
\small
\setlength{\jot}{2pt}
''']
    for j, row in enumerate(equation['residuals']):
        terms = [term(c, m, k == 0) for k, (c, m) in enumerate(row['terms'])]
        # Estimate typeset width in character units, not TeX source bytes.
        lines, current, width = [], [], 0
        for t, (c, m) in zip(terms, row['terms']):
            new_width = len(str(abs(c))) + 5 * len(m) + 2
            if current and width + new_width > 84:
                lines.append(''.join(current)); current, width = [], 0
            current.append(t); width += new_width
        if current:
            lines.append(''.join(current))
        out += [f'% residual {j}\n', '\\[\n\\begin{aligned}\n',
                f' R_{{{j}}}={{}}&' + lines[0]]
        for line in lines[1:]:
            out.append('\\\\\n &{}' + line)
        out.append(f'\n\\end{{aligned}}\n\\]\n% end residual {j}\n')
    out.append('\\endgroup\n')
    return ''.join(out)


if __name__ == '__main__':
    path = ROOT/'report/quartic_residuals.tex'
    path.write_text(make_text())
    print(path)
