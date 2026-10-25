#!/usr/bin/env python3
"""Readable exact transcriptions of the two fixed quadratic systems."""
from pathlib import Path
from collections import Counter
import argparse
import json
import re

ROOT=Path(__file__).resolve().parent


def term_tex(coefficient,monomial,first=False):
    counts=Counter(monomial)
    factors=''.join('x_{'+str(i)+'}'+('^{'+str(power)+'}' if power>1 else '')
        for i,power in sorted(counts.items()))
    absolute=abs(coefficient)
    body=(str(absolute) if not factors or absolute!=1 else '')+factors
    prefix='-' if coefficient<0 else ('' if first else '+')
    return prefix+body


def tex(equation):
    lines=['% Generated from the complete literal equation.json; no arithmetic macros.']
    for index,row in enumerate(equation['residuals']):
        lines.extend(['\\begin{align*}',f'r_{{{index}}}&='])
        current=''
        for j,(coefficient,monomial) in enumerate(row['terms']):
            term=term_tex(coefficient,monomial,j==0)
            if current and len(current)+len(term)>112:
                lines.append(current+' \\\\')
                current='&\\quad '+term
            else:
                current+=term
        lines.append(current)
        lines.append('\\end{align*}')
    return '\n'.join(lines)+'\n'


def parse_tex(payload):
    records=[]
    blocks=re.findall(r'\\begin\{align\*\}(.*?)\\end\{align\*\}',payload,re.S)
    for expected,block in enumerate(blocks):
        prefix=f'r_{{{expected}}}&='
        expression=''.join(block.split())
        if not expression.startswith(prefix):
            raise ValueError('Residual index transcription')
        expression=expression[len(prefix):].replace('\\\\','').replace('&\\quad','')
        terms=[]
        for match in re.finditer(r'([+-]?)([^+-]+)',expression):
            sign,body=match.groups()
            factor_matches=list(re.finditer(r'x_\{(\d+)\}(?:\^\{(\d+)\})?',body))
            coefficient_text=body[:factor_matches[0].start()] if factor_matches else body
            coefficient=int(coefficient_text or '1')*(-1 if sign=='-' else 1)
            monomial=[]
            end=len(coefficient_text)
            for factor in factor_matches:
                if factor.start()!=end:
                    raise ValueError('Unparsed mathematical text')
                monomial.extend([int(factor.group(1))]*int(factor.group(2) or '1'))
                end=factor.end()
            if end!=len(body):
                raise ValueError('Unparsed trailing mathematical text')
            terms.append([coefficient,monomial])
        records.append(terms)
    return records


def render(check=False):
    receipts={}
    for size in (221,222):
        folder=ROOT/'equations'/('natural'+str(size))
        equation=json.loads((folder/'equation.json').read_text())
        payload=tex(equation)
        actual=parse_tex(payload)
        if actual!=[r['terms'] for r in equation['residuals']]:
            raise ValueError('Exact TeX round-trip failed')
        dest=ROOT/'transcriptions'/('residuals'+str(size)+'.tex')
        if check:
            if dest.read_text()!=payload:
                raise ValueError('Stored TeX differs')
        else:
            dest.parent.mkdir(parents=True,exist_ok=True)
            dest.write_text(payload)
            variable_text='index\tname\n'+''.join(f"{i}\t{v['name']}\n" for i,v in enumerate(equation['variables']))
            (dest.parent/('variables'+str(size)+'.tsv')).write_text(variable_text)
            plain=[]
            for i,row in enumerate(equation['residuals']):
                pieces=[]
                for c,m in row['terms']:
                    pieces.append(str(c)+('*'+'*'.join('x'+str(j) for j in m) if m else ''))
                plain.append('r'+str(i)+' = '+' + '.join(pieces))
            plain.append('P = '+' + '.join('r'+str(i)+'^2' for i in range(len(plain))))
            (dest.parent/('equation'+str(size)+'.txt')).write_text('\n'.join(plain)+'\n')
        receipts[str(size)]={'parsed_residuals':len(actual),'tex_bytes':len(payload.encode())}
    return receipts


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--check',action='store_true')
    args=parser.parse_args()
    print(json.dumps(render(args.check),indent=2))
