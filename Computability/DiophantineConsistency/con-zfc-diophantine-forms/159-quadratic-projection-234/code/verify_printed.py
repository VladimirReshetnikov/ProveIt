"""Independently parse the displayed polynomial syntax and compare coefficients."""
import json,re
from collections import defaultdict

def parse_expression(expr):
    expr=re.sub(r'\s+','',expr).replace('\\\\','').replace('&','')
    parts=re.findall(r'[+-]?[^+-]+',expr)
    if ''.join(parts)!=expr:raise ValueError('unparsed signs')
    poly=defaultdict(int)
    for part in parts:
        sign=-1 if part.startswith('-') else 1
        part=part.lstrip('+-');m=re.fullmatch(r'(\d*)(.*)',part)
        digits,tail=m.groups();co=sign*(int(digits) if digits else 1)
        tokens=list(re.finditer(r'x_\{(\d+)\}(?:\^\{(\d+)\})?',tail))
        if ''.join(t.group() for t in tokens)!=tail:raise ValueError('unparsed monomial '+tail)
        if not digits and not tokens:raise ValueError('empty term')
        mon=[]
        for token in tokens:
            power=int(token.group(2) or 1)
            if power not in (1,2):raise ValueError('unexpected exponent')
            mon.extend([int(token.group(1))]*power)
        poly[tuple(sorted(mon))]+=co
    return {m:c for m,c in poly.items() if c}

def verify(root):
    text=(root/'report/residuals234.tex').read_text()
    rows=re.findall(r'\\mathcal\{Q\}_\{(\d+)\}=\{\}&(.*?)\\end\{align\*\}',text,re.S)
    e=json.loads((root/'equations/P234/equation.json').read_text())
    if len(rows)!=len(e['residuals']):raise ValueError('printed row census')
    for k,((label,expr),r) in enumerate(zip(rows,e['residuals'])):
        if int(label)!=k:raise ValueError('printed row order')
        expected=defaultdict(int)
        for c,m in r['terms']:expected[tuple(sorted(m))]+=c
        expected={m:c for m,c in expected.items() if c}
        if parse_expression(expr)!=expected:raise ValueError('printed coefficient mismatch '+str(k))
    return {'status':'PASS','rows':len(rows),'method':'Independent restricted LaTeX polynomial parser, all coefficients compared.'}
