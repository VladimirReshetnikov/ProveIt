#!/usr/bin/env python3
"""Parse the printed principal definition back into exact polynomial data.

This checker imports neither the report exporter nor a polynomial producer.
It authenticates the source-row appendix, free indices, ordered unit pivots,
literal request table, and all measured profile rows.
"""
from pathlib import Path
from collections import defaultdict
import re,json,hashlib,argparse,copy
ROOT=Path(__file__).resolve().parents[1]

def require(test,message):
    if not test:raise ValueError(message)

VAR=re.compile(r'v_\{(\d+)\}(?:\^\{(\d+)\})?|v_(\d+)(?:\^\{(\d+)\})?')

def parse_polynomial(text):
    text=text.replace(r'2^{20}','1048576')
    text=re.sub(r'\s+','',text).replace('$','')
    require(text!='','empty polynomial')
    chunks=re.findall(r'[+-]?[^+-]+',text)
    require(''.join(chunks)==text,'polynomial tokenization')
    out=defaultdict(int)
    for term in chunks:
        sign=-1 if term[0]=='-' else 1
        if term[0] in '+-':term=term[1:]
        mon=[]
        for m in VAR.finditer(term):
            idx=int(m.group(1) or m.group(3));power=int(m.group(2) or m.group(4) or 1)
            require(power>=1,'positive printed exponent')
            mon.extend([idx]*power)
        numeral=VAR.sub('',term)
        require(numeral.isdigit() or (numeral=='' and mon),'unparsed printed token '+term)
        coeff=int(numeral) if numeral else 1
        out[tuple(sorted(mon))]+=sign*coeff
    return {m:c for m,c in out.items() if c}

def add(p,q,sign=1):
    d=dict(p)
    for m,c in q.items():d[m]=d.get(m,0)+sign*c
    return {m:c for m,c in d.items() if c}

def mul(p,q):
    d=defaultdict(int)
    for m,c in p.items():
        for n,e in q.items():d[tuple(sorted(m+n))]+=c*e
    return {m:c for m,c in d.items() if c}

def check(texts):
    source=json.loads((ROOT/'source/anchor219.json').read_text())
    program=json.loads((ROOT/'equations/integer85_degree16964.json').read_text())
    seed=json.loads((ROOT/'joint209.json').read_text())
    raw=texts['source_rows.tex']
    blocks=re.findall(r'R_\{(\d+)\}&=(.*?)(?=R_\{\d+\}&=|\\end\{align\*\})',raw,re.S)
    decoded={}
    for j,formula in blocks:
        formula=re.sub(r'\\\\(?:\[2pt\]|\*)?','',formula)
        formula=formula.replace(r'&\quad','')
        require(int(j) not in decoded,'duplicate printed row')
        decoded[int(j)]=parse_polynomial(formula)
    expected={j:{tuple(mon):cc for cc,mon in row['terms']} for j,row in enumerate(source['residuals']) if j not in program['source_removed_rows']}
    require(decoded==expected,'printed source polynomial mismatch')

    match=re.search(r'\\begin\{gathered\}(.*?)\\end\{gathered\}',texts['free_indices.tex'],re.S)
    require(match is not None,'free-index environment')
    free=list(map(int,re.findall(r'\d+',match.group(1))))
    require(free==program['retained_source_indices'],'free-index list mismatch')

    pivots=[]
    for line in texts['pivot_table.tex'].splitlines():
        if not re.match(r'^\d+ & ',line):continue
        values=list(map(int,re.findall(r'-?\d+',line)))
        require(len(values)==8,'pivot-table row shape')
        pivots.extend([values[:4],values[4:]])
    wanted=[]
    for step,d in enumerate(program['definitions'],1):
        j,v=d['source_row'],d['variable']
        coeff=next(cc for cc,mon in source['residuals'][j]['terms'] if mon==[v])
        wanted.append([step,v,j,coeff])
    require(pivots==wanted,'ordered printed reconstruction mismatch')

    source_map=[v['source_index'] if v.get('source_index') is not None else 219 for v in seed['variables']]
    cache={}
    def expand(i):
        if i in cache:return cache[i]
        n=seed['nodes'][i];op=n[0]
        if op=='const':p={():n[1]} if n[1] else {}
        elif op=='var':p={(source_map[n[1]],):1}
        elif op=='add':p=add(expand(n[1]),expand(n[2]))
        elif op=='sub':p=add(expand(n[1]),expand(n[2]),-1)
        elif op=='mul':p=mul(expand(n[1]),expand(n[2]))
        else:raise ValueError('unknown seed op')
        cache[i]=p;return p
    ports=[]
    for line in texts['requests_table.tex'].splitlines():
        if not re.match(r'^\d+ & ',line):continue
        fields=line.removesuffix(r'\\').split(' & ')
        require(len(fields)==7,'request table columns')
        row=int(fields[0]);group=int(fields[1]);ports.append((row,group,[parse_polynomial(t) for t in fields[2:]]))
    require(len(ports)==16,'request count')
    for j,(row,group,values) in enumerate(ports):
        req=seed['ports']['requests'][j]
        require(row==j and group==req['g'],'request row/group')
        require(values==[expand(req[k]) for k in ['m','k','D','Y','Z']],'printed request port mismatch')

    metrics=[]
    for line in texts['metrics_table.tex'].splitlines():
        if not (re.match(r'^\d',line) or line.startswith(r'\textbf{')):continue
        line=line.replace(r'\textbf{','').replace('}','').replace(r'\,','')
        values=list(map(int,re.findall(r'\d+',line)))
        if len(values)==5:metrics.append(values)
    wanted_metrics=[]
    for path in (ROOT/'equations').glob('integer*.json'):
        m=json.loads(path.read_text())['metrics']
        wanted_metrics.append([m[k] for k in ['variables','degree','residuals','live_binary_operations','coefficient_height_bound_exponent']])
    require(metrics==sorted(wanted_metrics),'printed metric comparison')
    return {'source_rows':len(decoded),'free_variables':len(free),'ordered_unit_pivots':len(pivots),'requests':len(ports),'profiles':len(metrics)}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--receipt',type=Path);args=ap.parse_args()
    names=['source_rows.tex','free_indices.tex','pivot_table.tex','requests_table.tex','metrics_table.tex']
    texts={n:(ROOT/'report'/n).read_text() for n in names}
    details=check(texts)
    mutations=[]
    t=dict(texts);t['source_rows.tex']=t['source_rows.tex'].replace('R_{0}&=','R_{1}&=',1);mutations.append(t)
    t=dict(texts);t['free_indices.tex']=t['free_indices.tex'].replace('3,5,','4,5,',1);mutations.append(t)
    t=dict(texts);t['requests_table.tex']=t['requests_table.tex'].replace('2^{20}v_0','2^{19}v_0',1);mutations.append(t)
    t=dict(texts);t['metrics_table.tex']=t['metrics_table.tex'].replace(r'16\,964',r'16\,965');mutations.append(t)
    for i,t in enumerate(mutations):
        try:check(t)
        except (ValueError,KeyError,StopIteration):continue
        raise ValueError('Accepted printed corruption '+str(i))
    result={'status':'PASS','definition':details,'rejected_mutations':len(mutations),'files':{n:hashlib.sha256((ROOT/'report'/n).read_bytes()).hexdigest() for n in names}}
    if args.receipt:args.receipt.parent.mkdir(parents=True,exist_ok=True);args.receipt.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,sort_keys=True))
if __name__=='__main__':main()
