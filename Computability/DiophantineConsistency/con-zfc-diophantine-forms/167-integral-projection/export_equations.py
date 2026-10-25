#!/usr/bin/env python3
"""Export and independently reparse the two complete printed equation tables."""
from pathlib import Path
from collections import Counter
import json,re,hashlib

ROOT=Path(__file__).resolve().parent

def term(c,mon,first=False):
    sign='-' if c<0 else ('' if first else '+')
    coefficient=str(abs(c)) if abs(c)!=1 or not mon else ''
    product=''.join('x_{'+str(i)+'}'+('^{'+str(e)+'}' if e>1 else '') for i,e in sorted(Counter(mon).items()))
    return sign+coefficient+product

def width(c,mon):
    counts=Counter(mon)
    return 8+(4.5*len(str(abs(c))) if abs(c)!=1 or not mon else 0)+sum(8+1.8*len(str(i))+(4 if e>1 else 0) for i,e in counts.items())

def export(eq,prefix,out):
    lines=['% Generated from the literal JSON. All rows are independently reparsed.']
    text=[]
    for i,row in enumerate(eq['residuals']):
        chunks=[];chunk='';w=0
        for j,(c,mon) in enumerate(row['terms']):
            t=term(c,mon,j==0);ww=width(c,mon)
            if chunk and w+ww>355:chunks.append(chunk);chunk='';w=0
            chunk+=t;w+=ww
        chunks.append(chunk)
        lines.extend([f'% BEGIN ROW {i}',r'\begin{align*}',f'{prefix}_{{{i}}}={{}}&'+chunks[0]+(r'\\' if len(chunks)>1 else '')])
        for j,c in enumerate(chunks[1:]):lines.append('{}&'+c+(r'\\' if j<len(chunks)-2 else ''))
        lines.extend([r'\end{align*}',f'% END ROW {i}'])
        text.append(prefix+str(i)+' = '+''.join(term(c,m,j==0) for j,(c,m) in enumerate(row['terms'])).replace('_{','').replace('^{','^').replace('}',''))
    out.write_text('\n'.join(lines)+'\n')
    out.with_suffix('.txt').write_text('\n'.join(text)+'\n')

def parse_term(s):
    sign=1
    if s.startswith('-'):sign=-1;s=s[1:]
    elif s.startswith('+'):s=s[1:]
    m=re.match(r'\d+',s);coefficient=int(m.group()) if m else 1
    if m:s=s[m.end():]
    mon=[]
    while s:
        m=re.match(r'x_\{(\d+)\}(?:\^\{(\d+)\})?',s)
        if not m:raise ValueError('Unrecognized typeset term: '+s)
        mon.extend([int(m.group(1))]*int(m.group(2) or 1));s=s[m.end():]
    return sign*coefficient,tuple(mon)

def audit(eq,out):
    source=out.read_text();blocks=re.findall(r'% BEGIN ROW (\d+)\n(.*?)% END ROW \1',source,re.S)
    if len(blocks)!=len(eq['residuals']):raise ValueError('Printed row count mismatch')
    total=0
    for i,(number,body) in enumerate(blocks):
        if int(number)!=i:raise ValueError('Row order mismatch')
        s=re.sub(r'\\(?:begin|end)\{align\*\}','',body)
        s=re.sub(r'[RS]_\{\d+\}=','',s)
        s=s.replace('{}','').replace('&','').replace('\\\\','')
        s=''.join(s.split())
        parsed={}
        for t in re.findall(r'[+-]?[^+-]+',s):
            c,m=parse_term(t);parsed[m]=parsed.get(m,0)+c
        expected={tuple(m):c for c,m in eq['residuals'][i]['terms']}
        if parsed!=expected:raise ValueError('Typeset coefficient mismatch at row '+str(i))
        total+=len(parsed)
    return {'file':out.name,'rows':len(blocks),'terms':total,'status':'PASS','sha256':hashlib.sha256(out.read_bytes()).hexdigest()}

def main():
    report=ROOT/'report';report.mkdir(exist_ok=True);receipts=[]
    for dirname,prefix,name in [('', 'R','residuals218'),('variants/220','S','residuals220')]:
        eq=json.loads((ROOT/dirname/'equation/equation.json').read_text());out=report/(name+'.tex')
        export(eq,prefix,out);receipts.append(audit(eq,out))
    (ROOT/'verification/printed_equations.json').write_text(json.dumps(receipts,indent=2)+'\n');print(json.dumps(receipts))
if __name__=='__main__':main()
