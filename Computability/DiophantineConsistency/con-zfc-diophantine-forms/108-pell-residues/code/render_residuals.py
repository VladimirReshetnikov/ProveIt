#!/usr/bin/env python3
"""Generate all printed quartic residuals and report metrics from literal JSON."""
from collections import Counter
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parents[1]


def load(path):
    return json.loads(path.read_text())


def term(coefficient, monomial, first):
    sign = ('-' if coefficient < 0 else ('' if first else '+'))
    coefficient = abs(coefficient)
    letters = []
    width = 7 if sign else 0
    for index, power in sorted(Counter(monomial).items()):
        part = f'x_{{{index}}}'
        width += 7+len(str(index))*3
        if power > 1:
            part += f'^{{{power}}}'
            width += 4
        letters.append(part)
    numeral = str(coefficient) if coefficient != 1 or not monomial else ''
    width += len(numeral)*4.3
    return sign+numeral+''.join(letters), width


def render(name, label, destination):
    equation = load(ROOT/'equations'/name/'equation.json')
    out = [r'\begingroup\footnotesize',r'\setlength{\tabcolsep}{3pt}',
           r'\begin{longtable}{r@{\hspace{0.8em}}l}',r'\toprule',
           r'Residual & Polynomial (set each to zero)\\',r'\midrule',
           r'\endfirsthead',r'\toprule',r'Residual & Polynomial (continued)\\',
           r'\midrule',r'\endhead',r'\bottomrule\endfoot']
    for i, row in enumerate(equation['residuals']):
        lines = []
        current = ''
        width = 0
        for j, (coefficient, monomial) in enumerate(row['terms']):
            part, size = term(coefficient, monomial, j == 0)
            if current and width+size > 380:
                lines.append(current)
                current, width = part, size
            else:
                current += part
                width += size
        if current:
            lines.append(current)
        math = r'\begin{aligned}[t]&'+r'\\ &'.join(lines)+r'\end{aligned}'
        out.append(f'${label}_{{{i}}}$ & ${math}$\\\\[3pt]')
    out += [r'\end{longtable}',r'\endgroup','']
    (ROOT/'appendix'/destination).write_text('\n'.join(out))
    polynomial = load(ROOT/'equations'/name/'expanded_polynomial.json')
    metrics = {'vars':len(equation['variables']), 'rows':len(equation['residuals']),
               'terms':len(polynomial['terms']),
               'height':max(abs(c) for c,m in polynomial['terms'])}
    return metrics


def main():
    values = {}
    for prefix,name,label,destination in (
        ('n','natural395','R','natural_rows.tex'),
        ('z','integer663','S','integer_rows.tex'),
        ('s','integer687','T','small_rows.tex')):
        m=render(name,label,destination)
        values.update({prefix+k:v for k,v in m.items()})
        values[prefix+'last']=m['rows']-1
        values[prefix+'varlast']=m['vars']-1
    values['guardcount']=96
    values['nreduction']=f'{100*(407-values["nvars"])/407:.2f}'
    values['zreduction']=f'{100*(888-values["zvars"])/888:.2f}'
    lines=[]
    for name,value in values.items():
        if name.endswith(('terms','height')):
            value=format(value,',').replace(',',r'{,}')
        lines.append(f'\\newcommand{{\\{name}}}{{{value}}}')
    (ROOT/'metrics.tex').write_text('\n'.join(lines)+'\n')
    print(json.dumps(values,indent=2,sort_keys=True))


if __name__=='__main__':
    main()
