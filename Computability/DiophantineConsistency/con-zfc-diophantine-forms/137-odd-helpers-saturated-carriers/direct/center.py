#!/usr/bin/env python3
"""Reviewed adapter of the pinned upstream finite integer-centering algorithm."""
import argparse,copy,json,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent
sys.dont_write_bytecode=True
sys.path.insert(0,str(HERE/'vendor'))
import terminal_elimination as E

def addto(out,p,s):
    for m,c in p.items():
        out[m]=out.get(m,0)+s*c
        if not out[m]:out.pop(m)
def center(source,outdir):
    eq=json.loads((source/'equation.json').read_text());initial=json.loads((source/'translation_certificate.json').read_text());base=json.loads((source/'projected.json').read_text())
    rows=[E.normalize(r['terms']) for r in eq['residuals']];squares=[E.multiply(p,p) for p in rows];total={}
    for p in squares:addto(total,p,1)
    shifts={};history=[]
    def score(p):return(max(map(abs,p.values())),len(p),sum(map(abs,p.values())))
    best=score(total)
    for stage in range(8):
        changes=0
        for v,meta in enumerate(eq['variables']):
            if meta['kind']=='integer_guard':continue
            hits=[r for r,p in enumerate(rows) if any(v in m for m in p)];options=[]
            for d in [-8,-4,-3,-2,-1,1,2,3,4,8]:
                nr={r:E.substitute(rows[r],v,{(v,):1,():d}) for r in hits};ns={r:E.multiply(p,p) for r,p in nr.items()};nt=total.copy()
                for r in hits:addto(nt,squares[r],-1);addto(nt,ns[r],1)
                s=score(nt)
                if s<best:options.append((s,abs(d),d,nr,ns,nt))
            if options:
                s,_,d,nr,ns,total=min(options,key=lambda x:x[:3]);best=s
                for r in hits:rows[r]=nr[r];squares[r]=ns[r]
                shifts[v]=shifts.get(v,0)+d;changes+=1;history.append({'pass':stage,'variable':v,'shift':d,'score':list(s)})
        print('pass',stage,'changes',changes,'score',best,flush=True)
        if not changes:break
    final=copy.deepcopy(eq);final.pop('metrics',None)
    for r,p in zip(final['residuals'],rows):r['terms']=E.as_terms(p)
    final['variant']+=':finite_centering';combined=dict(initial['shifts'])
    for v,d in shifts.items():combined[v]=combined.get(v,0)+d
    combined={v:d for v,d in combined.items() if d}
    for old,new in zip(base['residuals'],final['residuals']):
        p=E.normalize(old['terms'])
        for v,d in sorted(combined.items()):p=E.substitute(p,v,{(v,):1,():d})
        if E.as_terms(p)!=new['terms']:raise ValueError('composed translation mismatch')
    poly=E.expand(final);metrics={'variables':len(final['variables']),'rows':len(final['residuals']),'degree':max(len(m) for c,m in poly['terms']),'monomials':len(poly['terms']),'height':max(abs(c) for c,m in poly['terms']),'row_height':max(abs(c) for r in final['residuals'] for c,m in r['terms'])}
    cert={'schema':'integral_translation_v1','shifts':[[v,d] for v,d in sorted(combined.items())],'convention':'old=new+shift','search_history':history,'scope':'Eight coordinate-descent passes; no global optimum claim.'}
    outdir.mkdir(parents=True,exist_ok=True)
    for name in ['raw_equation','transformation_certificate','factored_source','factorization_certificate','projection_certificate','terminal_elimination_certificate','ENGINE','SOURCE_BINDING']:
        (outdir/(name+'.json')).write_bytes((source/(name+'.json')).read_bytes())
    (outdir/'SOURCE_PARENT.json').write_bytes(E.canonical_bytes({'plain_parent':'../'+source.name,'scope':'The local projection certificate starts at factored_source.json and ends at projected.json. The separate translation certificate maps projected.json to this chart. The old source metadata refers to local SOURCE_BINDING.json.'}))
    for n,x in [('equation.json',final),('expanded_polynomial.json',poly),('translation_certificate.json',cert),('METRICS.json',metrics),('projected.json',base)]:
        (outdir/n).write_bytes(E.canonical_bytes(x))
    print(metrics)
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('source',type=Path);p.add_argument('output',type=Path);a=p.parse_args();center(a.source,a.output)
