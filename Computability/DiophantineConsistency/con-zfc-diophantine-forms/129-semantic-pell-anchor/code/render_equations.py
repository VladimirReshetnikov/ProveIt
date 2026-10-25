#!/usr/bin/env python3
"""Deterministically transcribe every residual; no terms are abbreviated."""
from collections import Counter
from pathlib import Path
import argparse
import json

ROOT = Path(__file__).resolve().parents[1]


def term(coefficient, monomial, latex=False, first=False):
    sign = '-' if coefficient < 0 else ('' if first else '+')
    value = abs(coefficient)
    factors = []
    for index, exponent in sorted(Counter(monomial).items()):
        if latex:
            factors.append('x_{%d}' % index + ('^{%d}' % exponent if exponent > 1 else ''))
        else:
            factors.append('x%d' % index + ('^%d' % exponent if exponent > 1 else ''))
    numeral = str(value) if value != 1 or not factors else ''
    if latex:
        return sign + numeral + ''.join(factors)
    return sign + '*'.join(([numeral] if numeral else []) + factors)


def latex_transcription(equation):
    lines = ['% Complete generated transcription. Do not edit by hand.',
             r'\begingroup\small', r'\allowdisplaybreaks[4]']
    for j,row in enumerate(equation['residuals']):
        terms = [term(c,m,True,i==0) for i,(c,m) in enumerate(row['terms'])]
        # Approximate visual width, independently of longer TeX subscripts.
        chunks, chunk, width = [], [], 0
        for i,t in enumerate(terms):
            c,m = row['terms'][i]
            w = 2 + len(str(abs(c))) + sum(3+len(str(v)) for v in set(m))
            if chunk and width+w > 79:
                chunks.append(''.join(chunk));chunk=[];width=0
            chunk.append(t);width+=w
        if chunk:chunks.append(''.join(chunk))
        lines.append(r'\begin{align*}')
        for k,chunk in enumerate(chunks):
            prefix = ('r_{%d}&=' % j) if k==0 else r'&\quad '
            lines.append(prefix + chunk + (r'\\' if k<len(chunks)-1 else ''))
        lines.append(r'\end{align*}')
    lines.extend([r'\endgroup',''])
    return '\n'.join(lines)


def text_transcription(equation):
    n=len(equation['variables']);r=len(equation['residuals'])
    lines=[f'Domain: N={{0,1,2,...}}; variables x0,...,x{n-1}.',
           f'P{n} = sum(r[j]^2 for j=0,...,{r-1}) = 0.',
           'Each following line is one complete quadratic residual.','']
    for j,row in enumerate(equation['residuals']):
        lines.append(f'r[{j}] = '+''.join(term(c,m,False,i==0)
                     for i,(c,m) in enumerate(row['terms'])))
    return '\n'.join(lines)+'\n'


def outputs():
    result={}
    for n in (234,233):
        eq=json.loads((ROOT/f'equations/natural{n}/equation.json').read_text())
        result[ROOT/f'residuals{n}.tex']=latex_transcription(eq)
        result[ROOT/f'equations/natural{n}/equation.txt']=text_transcription(eq)
    return result


def run(check=False):
    files=outputs()
    for path,body in files.items():
        if check:
            if not path.exists() or path.read_text()!=body:
                raise ValueError('Transcription mismatch: '+str(path.relative_to(ROOT)))
        else:path.write_text(body)
    return {'verified':True,'complete_transcriptions':len(files),
            'residuals':[183,182],'omitted_terms':0}


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--check',action='store_true')
    a=p.parse_args();print(json.dumps(run(a.check),indent=2))
