#!/usr/bin/env python3
"""Parse the printed polynomial definitions independently of their exporter."""
import json,re
from pathlib import Path

ROOT=Path(__file__).resolve().parent
def require(c,s):
    if not c:raise ValueError(s)
def source_poly(terms):
    p={}
    for c,m in terms:
        m=tuple(sorted(m));p[m]=p.get(m,0)+c
    return {m:c for m,c in p.items() if c}
def printed_poly(s):
    s=re.sub(r'\s+','',s);out={}
    for t in re.findall(r'[+-]?[^+-]+',s):
        factors=[]
        for ix,power in re.findall(r'z_\{(\d+)\}(?:\^\{(\d+)\})?',t):factors.extend([int(ix)]*int(power or '1'))
        scalar=re.sub(r'z_\{\d+\}(?:\^\{\d+\})?','',t)
        if scalar in ('','+'):c=1
        elif scalar=='-':c=-1
        else:
            require(bool(re.fullmatch(r'[+-]?\d+',scalar)),'non-polynomial printed term '+scalar)
            c=int(scalar)
        m=tuple(sorted(factors));out[m]=out.get(m,0)+c
    return {m:c for m,c in out.items() if c}
def split_definitions(s,letter):
    B=chr(92)
    for token in [B+'begin{align*}',B+'end{align*}',B+B+'[3pt]',B+B+'*',B+B,'&'+B+'quad{}']:s=s.replace(token,'')
    pattern=letter+r'_\{(\d+)\}&='
    matches=list(re.finditer(pattern,s));out=[]
    for j,m in enumerate(matches):
        part=s[m.end():matches[j+1].start() if j+1<len(matches) else len(s)]
        out.append((int(m.group(1)),printed_poly(part)))
    return out
def main():
    text=(ROOT/'P83_definition.tex').read_text();source=json.loads((ROOT/'source227.json').read_text());proj=json.loads((ROOT/'P83/projection.json').read_text())
    free_part,tail=text.split(chr(92)+'subsection*{Acyclic unit definitions}')
    unit_part,rest=tail.split(chr(92)+'subsection*{Retained residuals}')
    residual_part=rest.split(chr(92)+'endgroup')[0]
    free=[(int(a),int(b)) for a,b in re.findall(r'z_\{(\d+)\}&=x_\{(\d+)\}',free_part)]
    require(free==list(zip(proj['free'],range(83))),'printed free-coordinate assignment differs')
    defs={p['variable']:source_poly(p['restoration']) for p in proj['pivots']};known=set(proj['free'])
    printed=split_definitions(unit_part,'z');require(len(printed)==144,'printed pivot count')
    for v,p in printed:
        require(v not in known and v in defs and p==defs[v],'printed pivot differs')
        require(all(set(m)<=known for m in p),'printed definitions are not topologically ordered');known.add(v)
    require(len(known)==227,'printed definitions omit coordinates')
    rr=split_definitions(residual_part,'R');require([i for i,p in rr]==list(range(31)),'printed residual numbers differ')
    for (j,p),ri in zip(rr,proj['retained_rows']):require(p==source_poly(source['residuals'][ri]['terms']),'printed residual differs')
    print(json.dumps({'status':'PASS','free_assignments':83,'unit_definitions':144,'residuals':31,'all_coefficients_parsed':True}))

if __name__=='__main__':main()
