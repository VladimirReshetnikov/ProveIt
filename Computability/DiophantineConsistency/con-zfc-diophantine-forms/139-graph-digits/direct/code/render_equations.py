#!/usr/bin/env python3
"""Readable text and TeX transcriptions of the literal residual lists."""
from pathlib import Path
from collections import Counter
import argparse,json
ROOT=Path(__file__).resolve().parents[1]

def monomial(m,tex=False):
    counts=Counter(m);parts=[]
    for i,k in sorted(counts.items()):
        x=('x_{'+str(i)+'}')if tex else('x'+str(i))
        if k>1:x+=('^{'+str(k)+'}')if tex else('^'+str(k))
        parts.append(x)
    return ('' if tex else '*').join(parts)
def terms(row,tex=False):
    out=[]
    for c,m in row:
        mag=abs(c);v=monomial(m,tex)
        coefficient=str(mag)if not m or mag!=1 else''
        text=coefficient+(''if tex or not coefficient or not v else'*')+v
        out.append(('-'if c<0 else'+' if out else'')+text)
    return out
def artifacts(eq):
    text=['All variables are nonnegative integers.','P(x) = sum_j R_j(x)^2. The equation is P(x)=0.','']
    tex=['% Generated directly from the canonical JSON; zero-based indices.','\\begingroup\\small']
    for j,r in enumerate(eq['residuals']):
        text.append('R'+str(j)+' = '+' '.join(terms(r['terms']))+'  # '+r['label'])
        chunks=[];line=''
        for term in terms(r['terms'],True):
            if line and len(line)+len(term)>95:chunks.append(line);line=''
            line+=term
        if line:chunks.append(line)
        tex.append('\\[\\begin{aligned}R_{'+str(j)+'}={}&'+chunks[0])
        tex.extend('\\\\&'+c for c in chunks[1:]);tex.append('\\end{aligned}\\]')
    tex.append('\\endgroup')
    variables='index\tname\tkind\n'+''.join(str(i)+'\t'+v['name']+'\t'+v['kind']+'\n' for i,v in enumerate(eq['variables']))
    return {'equation.txt':'\n'.join(text)+'\n','residuals.tex':'\n'.join(tex)+'\n','variables.tsv':variables}
def run(check=False):
    count=0
    for n in [226,227]:
        p=ROOT/'equations'/('natural'+str(n));eq=json.loads((p/'equation.json').read_text())
        for name,content in artifacts(eq).items():
            if check:
                if (p/name).read_text()!=content:raise ValueError('transcription mismatch: '+str(p/name))
            else:(p/name).write_text(content)
            count+=1
    return count
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args();print(run(a.check),'transcriptions checked' if a.check else 'transcriptions generated')
