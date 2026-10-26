#!/usr/bin/env python3
"""Read back every printed source polynomial and pivot table."""
import collections,json,re
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def need(c,m):
    if not c:raise ValueError(m)
def read_poly(s):
    s=re.sub(r'\s+','',s).replace('&','').replace(r'\\','')
    if s and s[0] not in '+-':s='+'+s
    out=collections.defaultdict(int)
    for sign,body in re.findall(r'([+-])([^+-]+)',s):
        match=re.match(r'\d+',body);coef=int(match[0]) if match else 1
        if match:body=body[len(match[0]):]
        factors=[]
        while body:
            match=re.match(r'x_\{([0-9]+)\}(?:\^\{([0-9]+)\})?',body)
            need(bool(match),'Unexpected printed token')
            factors += [int(match[1])]*int(match[2] or 1);body=body[len(match[0]):]
        out[tuple(sorted(factors))] += coef*(1 if sign=='+' else -1)
    return {m:c for m,c in out.items() if c}
def main():
    source=json.loads((ROOT/'inputs/source216.json').read_text())
    text=(ROOT/'report/residuals.tex').read_text()
    blocks=re.findall(r'% BEGIN_RESIDUAL (\d+)\s*\\begin\{align\*\}(.*?)\\end\{align\*\}\s*% END_RESIDUAL (\d+)',text,re.S)
    need(len(blocks)==153,'Source row count')
    for i,(head,body,tail) in enumerate(blocks):
        need(int(head)==int(tail)==i,'Printed row numbering')
        prefix=re.match(r'\s*r_\{'+str(i)+r'\}=\{\}',body);need(bool(prefix),'Printed row prefix')
        p=read_poly(body[prefix.end():]);need(p=={tuple(m):c for c,m in source['residuals'][i]['terms']},'Printed source polynomial '+str(i))
    pivot_text=(ROOT/'report/pivots.tex').read_text()
    sections=re.split(r'\\subsection\{(\d+) integers, degree (\d+)\}',pivot_text)[1:]
    count=0
    for j in range(0,len(sections),3):
        n,d,body=sections[j:j+3];cert=json.loads((ROOT/f'equations/integer{n}_degree{d}/projection.json').read_text())
        pairs=[{'row':int(r),'variable':int(v)} for r,v in re.findall(r'\$\((\d+),(\d+)\)\$',body)]
        need(pairs==[{'row':s['row'],'variable':s['variable']} for s in cert['steps']],'Printed pivot table')
        partition=r';\ '.join(','.join(map(str,p)) for p in cert['partition'])
        need('Block partition: $('+partition+')$.' in body,'Printed block partition')
        count+=len(pairs)
    master=(ROOT/'report/report.tex').read_text()
    flat=re.sub(r'\\input\{([^}]+)\}',lambda m:(ROOT/'report'/m[1]).read_text(),master)
    need(flat==(ROOT/'report/ConZFC_Mixed_Base_Pooling.tex').read_text(),'Standalone TeX equality')
    result=(ROOT/'report/results.tex').read_text()
    for p in sorted((ROOT/'equations').glob('*/projection.json')):
        met=json.loads((p.parent/'METRICS.json').read_text())
        line=f"{met['variables']} & {met['exact_total_degree']} & {met['residuals']} & $<2^{{{met['coefficient_height_strictly_less_than_2_power']}}}$ & {met['binary_operations']}"
        need(line in result,'Printed metrics')
    print(json.dumps({'status':'PASS','source_residuals':153,'source_terms':1429,'printed_pivots':count,'profiles':len(sections)//3,'standalone_tex_exact':True},sort_keys=True))
if __name__=='__main__':main()
