#!/usr/bin/env python3
"""Print every quadratic residual of the 577-coordinate equation in LaTeX."""
from collections import Counter
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
data = json.loads((ROOT/'quotient_frame/support8/equation.json').read_bytes())


def term_text(coefficient, monomial):
    factors = []
    estimated = 0.0
    for index, power in sorted(Counter(monomial).items()):
        factors.append('x_{'+str(index)+'}'+('^{'+str(power)+'}' if power != 1 else ''))
        estimated += 8 + 2.7*len(str(index)) + (4 if power != 1 else 0)
    magnitude = abs(coefficient)
    head = str(magnitude) if magnitude != 1 or not factors else ''
    estimated += 3.6*len(head) + 8
    return head + ''.join(factors), estimated


def expression(terms):
    lines = []
    line = ''
    width = 0.0
    for c, m in terms:
        if not c:
            continue
        text, w = term_text(c, m)
        sign = '-' if c < 0 else '+'
        if not lines and not line and sign == '+':
            sign = ''
        if line and width+w > 386:
            lines.append(line)
            line = ''
            width = 0
        line += sign + text
        width += w
    if line:
        lines.append(line)
    return r'\\[-1pt] &'.join(lines) or '0'


text = r'''\section{Complete residual list for the 577-variable equation}\label{app:rows}
The unknowns are exactly \(x_0,\ldots,x_{576}\in\Z\). The single equation is
\[
P_{577}=\sum_{j=0}^{362}r_j^2=0.
\]
Every quadratic residual is printed below. No other symbols in this list
stand for unknowns or unprinted coefficients. The row order is identical to
\code{quotient_frame/support8/equation.json}. The fully expanded 7,326-term
polynomial is supplied separately in the adjacent JSON file.

\begingroup
\fontsize{8.5}{10.5}\selectfont
\setlength{\tabcolsep}{3pt}
\renewcommand{\arraystretch}{1.13}
\begin{longtable}{@{}r p{0.92\linewidth}@{}}
\toprule
Row & Quadratic residual\\
\midrule
\endfirsthead
\toprule
Row & Quadratic residual (continued)\\
\midrule
\endhead
\bottomrule
\endfoot
'''
for i, row in enumerate(data['residuals']):
    text += '$r_{'+str(i)+'}=$ & $\\begin{aligned}[t]&'+expression(row['terms'])+'\\end{aligned}$ \\\\[2pt]\n'
text += '\\end{longtable}\n\\endgroup\n'
(ROOT/'sections/equation_rows.tex').write_text(text)
print(json.dumps({'rows':len(data['residuals']), 'variables':len(data['variables']),
                  'path':'sections/equation_rows.tex'}))
