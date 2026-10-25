#!/usr/bin/env python3
"""Generate the printable complete residual list from authoritative JSON."""
import argparse
import collections
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

def monomial(indices):
    counts = collections.Counter(indices)
    return ''.join('X_{%d}' % i + ('^{%d}' % n if n > 1 else '')
                   for i,n in sorted(counts.items()))

def term(coefficient, indices, first=False):
    sign = '-' if coefficient < 0 else ('' if first else '+')
    c = abs(coefficient)
    return sign + (str(c) if c != 1 or not indices else '') + monomial(indices)

def weight(coefficient, indices):
    return 2 + (len(str(abs(coefficient))) if abs(coefficient) != 1 or not indices else 0) + 5*len(indices)

def make_appendix(equation):
    result = [r'\begingroup', r'\fontsize{9}{11}\selectfont',
              r'\setlength{\abovedisplayskip}{5pt}',r'\setlength{\belowdisplayskip}{5pt}']
    for i,row in enumerate(equation['residuals']):
        pieces=[]; current=[]; used=10
        for j,(c,indices) in enumerate(row['terms']):
            w=weight(c,indices)
            if current and used+w>100:
                pieces.append(''.join(current));current=[];used=10
            current.append(term(c,indices,j==0));used+=w
        if current:pieces.append(''.join(current))
        if not pieces:pieces=['0']
        result.append(r'\begin{align*}')
        for j,piece in enumerate(pieces):
            prefix=(r'r_{%d}&=' % i) if j==0 else r'&\quad '
            result.append(prefix+piece+(r'\\' if j+1<len(pieces) else ''))
        result.append(r'\end{align*}')
    result.append(r'\endgroup')
    return '\n'.join(result)+'\n'

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--check',action='store_true')
    args=parser.parse_args()
    eq=json.loads((ROOT/'equations/balanced239/equation.json').read_text())
    text=make_appendix(eq)
    target=ROOT/'report/residuals239.tex'
    if args.check:
        if target.read_text()!=text:raise ValueError('Printed residual appendix differs from JSON')
    else:target.write_text(text)
    print(json.dumps({'residuals':len(eq['residuals']),'variables':len(eq['variables']),'tex_bytes':len(text.encode()),'check':args.check}))

if __name__=='__main__':main()
