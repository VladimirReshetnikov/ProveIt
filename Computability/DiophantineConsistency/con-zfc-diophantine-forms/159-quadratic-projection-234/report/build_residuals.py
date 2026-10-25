#!/usr/bin/env python3
from pathlib import Path
from collections import Counter
import json
ROOT=Path(__file__).resolve().parent.parent

def term(c,m,first):
    sign='-' if c<0 else ('' if first else '+')
    a=abs(c);factors=''.join('x_{'+str(i)+'}'+('^{'+str(k)+'}' if k>1 else '') for i,k in sorted(Counter(m).items()))
    return sign+(str(a) if not factors or a!=1 else '')+factors

def main():
    e=json.loads((ROOT/'equations/P234/equation.json').read_text());parts=['% Generated from the literal principal equation; independently parsed by verify_printed.py.']
    for i,row in enumerate(e['residuals']):
        ts=[term(c,m,j==0) for j,(c,m) in enumerate(row['terms'])]
        chunks=[''.join(ts[j:j+5]) for j in range(0,len(ts),5)]
        body='\\begin{align*}\n\\mathcal{Q}_{'+str(i)+'}={}&'+chunks[0]
        for chunk in chunks[1:]:body+='\\\\\n&'+chunk
        body+='\n\\end{align*}\n'
        parts.append(body)
    (ROOT/'report/residuals234.tex').write_text('\n'.join(parts))
if __name__=='__main__':main()
