#!/usr/bin/env python3
"""Reconstruct the fixed principal quartic and its complete printed residuals.

Python 3 standard library only. --check performs byte-exact comparisons
without rewriting the delivered data. The shear search is not needed.
"""
from collections import Counter, defaultdict
from pathlib import Path
import argparse, hashlib, json

ROOT = Path(__file__).resolve().parents[1]
DEST = ROOT / 'equations' / 'principal'

def need(ok, why):
    if not ok: raise ValueError(why)

def data_bytes(obj):
    return (json.dumps(obj, sort_keys=True, separators=(',', ':'))+'\n').encode()

def collect(terms):
    out = defaultdict(int)
    for c,m in terms:
        need(type(c) is int and all(type(v) is int for v in m), 'Nonintegral data')
        out[tuple(sorted(m))] += c
    return {m:c for m,c in out.items() if c}

def plus(p,m,c):
    m=tuple(sorted(m)); value=p.get(m,0)+c
    if value:p[m]=value
    else:p.pop(m,None)

def shear(p,i,j,k):
    out={}
    for m,c in p.items():
        block={():c}
        for v in m:
            nxt={}
            for mon,co in block.items():
                plus(nxt,mon+(v,),co)
                if v==j:plus(nxt,mon+(i,),k*co)
            block=nxt
        for mon,co in block.items():plus(out,mon,co)
    return out

def square_sum(rows):
    out={}
    for p in rows:
        terms=list(p.items())
        for index,(m,c) in enumerate(terms):
            plus(out,m+m,c*c)
            for n,d in terms[index+1:]:plus(out,m+n,2*c*d)
    return out

def terms(p):return [[c,list(m)] for m,c in sorted(p.items())]

def tex_atom(c,m,initial=False):
    powers=Counter(m)
    mon='\\,'.join('z_{'+str(v+1)+'}'+('^{'+str(d)+'}' if d>1 else '') for v,d in sorted(powers.items()))
    magnitude=str(abs(c)) if abs(c)!=1 or not mon else ''
    body=magnitude+('\\,' if magnitude and mon else '')+mon
    return ('-' if c<0 else ('' if initial else '+'))+body

def residual_tex(rows):
    lines=['% Generated from the complete final quadratic residual list.']
    for index,p in enumerate(rows,1):
        items=list(sorted(p.items()))
        lines.append('\\begin{equation*}\\begin{aligned}')
        for start in range(0,len(items),5):
            block=items[start:start+5]
            expression=' '.join(tex_atom(c,m,initial=(start==0 and t==0)) for t,(m,c) in enumerate(block))
            left='R_{'+str(index)+'}&=' if start==0 else '&\\quad '
            suffix=' \\\\' if start+5<len(items) else ''
            lines.append(left+expression+suffix)
        lines.append('\\end{aligned}\\end{equation*}')
    return '\n'.join(lines)+'\n'

def shear_tex(history):
    out=[r'There are '+str(len(history))+r' steps. At step $s$, the listed triple $(i,j,k)$ means',
         r'\[x^{(s-1)}_j=x^{(s)}_j+kx^{(s)}_i,\qquad x^{(s-1)}_v=x^{(s)}_v\ (v\ne j).\]',
         r'The final coordinates are $x^{('+str(len(history))+r')}_v=z_v$. Indices in this table are one-based.',
         r'\begin{center}']
    midpoint=(len(history)+1)//2
    for start,stop in ((0,midpoint),(midpoint,len(history))):
        if start:out.append(r'\hfill')
        out += [r'\begin{minipage}[t]{.46\linewidth}\centering',
                r'\begin{tabular}{rrrr}',r'\toprule Step & $i$ & $j$ & $k$\\\midrule']
        out += [f'{s+1}&{history[s]["i"]+1}&{history[s]["j"]+1}&{history[s]["k"]}\\\\' for s in range(start,stop)]
        out += [r'\bottomrule\end{tabular}\end{minipage}']
    out += [r'\end{center}']
    return '\n'.join(out)+'\n'

def run(check=False):
    source_path=ROOT/'certificate'/'merged_aggregate_centered'/'equation.json'
    source_bytes=source_path.read_bytes(); source=json.loads(source_bytes)
    record=json.loads((DEST/'shears.json').read_text());history=record['history']
    need(hashlib.sha256(source_bytes).hexdigest()==record['source_sha256'],'Source hash mismatch')
    n=len(source['variables']);need(n==260,'Wrong source dimension')
    original=[collect(r['terms']) for r in source['residuals']];rows=[r.copy() for r in original]
    matrix=[{v:1} for v in range(n)]
    for h in history:
        i,j,k=h['i'],h['j'],h['k']
        need(all(type(v) is int for v in (i,j,k)) and 0<=i<n and 0<=j<n and i!=j,'Invalid elementary shear')
        rows=[shear(r,i,j,k) for r in rows]
        need(all(len(m)<=2 for r in rows for m in r),'Quadratic degree exceeded')
        for form in matrix:
            c=form.get(j,0)
            if c:
                value=form.get(i,0)+k*c
                if value:form[i]=value
                else:form.pop(i,None)
    restored=[r.copy() for r in rows]
    for h in reversed(history):restored=[shear(r,h['i'],h['j'],-h['k']) for r in restored]
    need(restored==original,'Inverse shear identity failed')
    p=square_sum(rows);used={v for m in p for v in m}
    need(used==set(range(n)),'Unused or out-of-range final variable')
    metrics={'variables':n,'quadratic_residuals':len(rows),'degree':max(map(len,p)),
             'monomials':len(p),'coefficient_height':max(map(abs,p.values())),
             'residual_coefficient_height':max(abs(c) for r in rows for c in r.values()),
             'shear_steps':len(history),'coefficient_absolute_sum':sum(map(abs,p.values()))}
    need(metrics['degree']==4 and metrics['quadratic_residuals']==186,'Wrong principal endpoint')
    equation={'schema':'proveit-fixed-integer-quartic-v1','domain':'unrestricted integers',
              'source_commit':'e0c98c629bf10d30b695884f6b1d2ab361bdf513','polynomial':'sum_of_squares',
              'source_equation_sha256':record['source_sha256'],'coordinate_certificate':'shears.json',
              'variables':[{'name':f'z_{i+1}','kind':'unrestricted_integer','pre_shear_origin':v} for i,v in enumerate(source['variables'])],
              'residuals':[{'label':r['label'],'terms':terms(p0)} for r,p0 in zip(source['residuals'],rows)]}
    expanded={'schema':'collected-integer-polynomial-v1','domain':'unrestricted integers','variables':n,'terms':terms(p)}
    coordinate_map={'schema':'integral-shear-coordinate-map-v1','determinant':1,
                    'meaning':'Each old coordinate is the listed integral linear form in final zero-based coordinates.',
                    'old_coordinates_as_linear_forms':[[[c,v] for v,c in sorted(form.items())] for form in matrix]}
    files={DEST/'equation.json':data_bytes(equation),DEST/'expanded_polynomial.json':data_bytes(expanded),
           DEST/'metrics.json':data_bytes(metrics),DEST/'coordinate_map.json':data_bytes(coordinate_map),
           ROOT/'report'/'metrics.tex':('\\newcommand{\\FinalTerms}{'+format(metrics['monomials'],',')+'}\n'
               +'\\newcommand{\\FinalHeight}{'+format(metrics['coefficient_height'],',')+'}\n').encode(),
           ROOT/'report'/'residuals.tex':residual_tex(rows).encode(),ROOT/'report'/'shears.tex':shear_tex(history).encode()}
    for path,raw in files.items():
        if check:need(path.read_bytes()==raw,f'Reconstruction mismatch: {path.relative_to(ROOT)}')
        else:path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(raw)
    print(json.dumps({'status':'PASS','mode':'check' if check else 'build','metrics':metrics,
                      'source_sha256':record['source_sha256'],'exact_inverse_checked':True,'files_checked':len(files)},sort_keys=True))

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');run(ap.parse_args().check)
