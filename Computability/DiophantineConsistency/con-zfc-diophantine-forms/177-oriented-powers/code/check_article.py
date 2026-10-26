#!/usr/bin/env python3
"""Parse the printed parent coefficients and all pivot pairs independently."""
import json,re
from pathlib import Path
ROOT=Path(__file__).resolve().parent.parent
def require(ok,msg):
    if not ok:raise ValueError(msg)
def main():
    rows=json.loads((ROOT/'sources/parent225.json').read_text())['residuals']
    text=(ROOT/'report/parent_residuals.tex').read_text()
    matches=re.findall(r'%BEGIN_RESIDUAL (\d+)\n(.*?)%END_RESIDUAL \1',text,re.S)
    require(len(matches)==len(rows),'parent row count')
    for expected_index,(index,body) in enumerate(matches):
        require(int(index)==expected_index,'parent row order')
        expr=body.split('={}&',1)[1].split(r'\end{aligned}',1)[0]
        expr=expr.replace('\\\\','').replace('&','');expr=re.sub(r'\s','',expr)
        terms=re.findall(r'[+-]?(?:\d+)?(?:x_\{\d+\}(?:\^\{\d+\})?)*',expr)
        terms=[s for s in terms if s]
        require(''.join(terms)==expr,'unparsed parent math')
        got={}
        for term in terms:
            sign=-1 if term.startswith('-') else 1;term=term.lstrip('+-')
            head=re.match(r'\d+',term);c=int(head.group()) if head else 1
            if head:term=term[head.end():]
            mon=[];parts=re.findall(r'x_\{(\d+)\}(?:\^\{(\d+)\})?',term)
            require(''.join('x_{'+v+'}'+('^{'+d+'}' if d else '') for v,d in parts)==term,'unparsed monomial')
            for v,d in parts:mon.extend([int(v)]*(int(d) if d else 1))
            mon=tuple(sorted(mon));got[mon]=got.get(mon,0)+sign*c
        require({m:c for m,c in got.items() if c}=={tuple(m):c for c,m in rows[expected_index]['terms']},'printed coefficient mismatch')
    text=(ROOT/'report/pivot_tables.tex').read_text()
    blocks=re.findall(r'%BEGIN_PIVOTS (\w+)\n(.*?)%END_PIVOTS \1',text,re.S)
    profiles={p.stem:json.loads(p.read_text()) for p in (ROOT/'certificates').glob('*.json')}
    require(set(n for n,b in blocks)==set(profiles),'printed profile set')
    count=0
    for name,body in blocks:
        pairs=[(int(a),int(b)) for a,b in re.findall(r'\$\((\d+),(\d+)\)\$',body)]
        expected=[(x['row'],x['variable']) for x in profiles[name]['steps']]
        require(pairs==expected,'printed pivot mismatch');count+=len(pairs)
    print(json.dumps({'status':'PASS','literal_parent_residuals_parsed':len(rows),'pivot_profiles_parsed':len(blocks),'pivot_pairs_parsed':count}))
if __name__=='__main__':main()
