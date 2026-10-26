#!/usr/bin/env python3
"""Produce the complete literal TeX appendix, or compare it byte for byte."""
import argparse
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]

def term(c, monomial):
    factors=[]
    for i in sorted(set(monomial)):
        n=monomial.count(i)
        factors.append('x_{'+str(i)+'}'+('^{'+str(n)+'}' if n>1 else ''))
    body=''.join(factors)
    if not body or abs(c)!=1:body=str(abs(c))+body
    return ('-' if c<0 else '+')+body

def render(eq):
    lines=['% Generated from the canonical quadratic residuals. All 153 are printed.',
           '\\begingroup','\\fontsize{8.6}{10.4}\\selectfont',
           '\\setlength{\\jot}{3pt}','\\allowdisplaybreaks[4]','\\begin{align*}']
    for i,row in enumerate(eq['residuals']):
        chunks=[];current=[];width=0
        for c,monomial in sorted(row['terms'],key=lambda pair:pair[1]):
            token=term(c,monomial)
            weight=2+len(str(abs(c)))+sum(3+len(str(j)) for j in monomial)
            if current and width+weight>92:
                chunks.append(current);current=[];width=0
            current.append(token);width+=weight
        if current:chunks.append(current)
        for j,chunk in enumerate(chunks):
            expression=' '.join(chunk)
            if j==0 and expression.startswith('+'):expression=expression[1:]
            left='\\mathcal R_{'+str(i)+'} &=' if j==0 else '&\\quad'
            # Keep every wrapped residual on a single page in the PDF.
            ending = r' \\*' if j+1 < len(chunks) else r' \\'
            lines.append(left+' '+expression+ending)
    lines+=['\\end{align*}','\\endgroup','']
    return '\n'.join(lines)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args()
    eq=json.loads((ROOT/'direct/diagonal214/equation.json').read_text())
    content=render(eq);target=ROOT/'residuals.tex'
    if a.check:
        if target.read_text()!=content:raise SystemExit('printed residual appendix differs from canonical source')
        print('PASS: all 153 displayed residuals match the canonical source')
    else:
        target.write_text(content)
        print('Wrote complete residual appendix')

if __name__=='__main__':main()
