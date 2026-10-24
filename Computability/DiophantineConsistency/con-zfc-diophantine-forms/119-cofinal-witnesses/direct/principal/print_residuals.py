#!/usr/bin/env python3
"""Render every literal quadratic residual as a LaTeX appendix fragment."""
from collections import Counter
from pathlib import Path
import argparse, json

HERE = Path(__file__).resolve().parent

def render(equation):
    n = len(equation['variables'])
    lines = [f'% Generated exactly from equation.json; display variables z_1,...,z_{n}.',
             r'\begingroup',r'\small',r'\allowdisplaybreaks[4]',r'\begin{align*}']
    for i,row in enumerate(equation['residuals'],1):
        terms = []
        for j,(coefficient,monomial) in enumerate(row['terms']):
            powers = Counter(monomial)
            variable = ''.join('z_{'+str(v+1)+'}'+('^{'+str(k)+'}' if k>1 else '')
                               for v,k in sorted(powers.items()))
            magnitude = abs(coefficient)
            body = (str(magnitude)+(r'\,' if variable else '') if magnitude!=1 or not variable else '')+variable
            sign = '-' if coefficient<0 else ('' if j==0 else '+')
            terms.append(sign+body)
        for start in range(0,len(terms),4):
            prefix = 'R_{'+str(i)+r'}={}&' if start==0 else '&'
            suffix = r'\\[2pt]' if start+4>=len(terms) else r'\\'
            lines.append(prefix+' '.join(terms[start:start+4])+suffix)
    lines.extend([r'\end{align*}',r'\endgroup'])
    return '\n'.join(lines)+'\n'

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--root',type=Path,default=HERE)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    equation=json.loads((args.root/'equation.json').read_text())
    output=args.output or args.root/'residuals508.tex'
    output.write_text(render(equation))
    print(f"Rendered {len(equation['residuals'])} residuals in {len(equation['variables'])} coordinates.")

if __name__=='__main__':main()
