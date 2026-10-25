#!/usr/bin/env python3
"""Replay a fixed affine-exposure and integral projection certificate."""
from pathlib import Path
import argparse,copy,json,sys
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'parent/code'))
import terminal_elimination as E
import factor_horn as F

def put(path,obj):
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_bytes(E.canonical_bytes(obj))

SHEARS=[['mul.40',{'crt.encoded.a':-2,'crt.encoded.b':-2}],
    ['mul.53',{'add.50':-8}],['mul.148',{'add.145':-8}],
    ['mul.137',{'crt.encoded.a':-4,'crt.encoded.c':-5,'mul.64':-2,'mul.75':-1}],
    ['mul.75',{'crt.encoded.a':-1,'crt.encoded.c':-1}],
    ['mul.64',{'crt.encoded.b':-1,'crt.encoded.c':-1}]]
ROWS=[[21,6,-1],[73,71,-1],[73,70,-4],[73,68,-8],[119,117,-1]]
PROJECT=[(21,'add.145'),(73,'mul.346'),(119,'base4.T')]

def construct(old,certificate):
    eq=copy.deepcopy(old);rows=[E.normalize(r['terms']) for r in old['residuals']]
    names={v['name']:i for i,v in enumerate(old['variables'])}
    for target,inputs in certificate['coordinate_shears']:
        t=names[target];rest=F.add(F.V(t),{(names[n],):c for n,c in inputs.items()})
        rows=[E.substitute(r,t,rest) for r in rows]
    for i,j,k in certificate['row_operations']:
        rows[i]=F.add(rows[i],{m:k*c for m,c in rows[j].items()})
    removed_rows=[];removed_vars=[]
    for step in certificate['projections']:
        i,t=step['row'],step['variable'];q=E.normalize(step['replacement'])
        if E.degree(rows[i])>1 or E.candidate(rows[i],t,False)!=q:raise ValueError('bad affine projection')
        rows=[E.substitute(r,t,q) for r in rows]
        if rows[i]:raise ValueError('nonzero removed row')
        removed_rows.append(i);removed_vars.append(t)
    keep=[i for i in range(len(old['variables'])) if i not in removed_vars]
    ren={i:j for j,i in enumerate(keep)}
    rr=[(i,{tuple(ren[x] for x in m):c for m,c in r.items()}) for i,r in enumerate(rows) if i not in removed_rows]
    rows=[r for _,r in rr]
    for i,j,k in certificate.get('final_row_operations',[]):
        rows[i]=F.add(rows[i],{m:k*c for m,c in rows[j].items()})
    eq={'schema':'finite_quadratic_residuals_v1','domain':'unrestricted integers','variant':certificate['endpoint'],
        'polynomial':'sum(square(row) for row in residuals)',
        'variables':[old['variables'][i] for i in keep],
        'residuals':[{'label':old['residuals'][oi]['label'],'terms':E.as_terms(r)} for (oi,_),r in zip(rr,rows)]}
    poly=E.expand(eq)
    metrics={'variables':len(eq['variables']),'rows':len(eq['residuals']),
        'degree':max(len(m) for _,m in poly['terms']),'monomials':len(poly['terms']),
        'height':max(abs(c) for c,_ in poly['terms']),
        'row_height':max(abs(c) for r in eq['residuals'] for c,_ in r['terms'])}
    return eq,poly,metrics

def certificate(old,dense=False,parity=False,prefix=None):
    ops=[[i+1,j+1,k] for i,j,k in ROWS] if parity else ROWS
    proj=[(i+1,n) for i,n in PROJECT] if parity else PROJECT
    endpoint=(prefix or ('parity' if parity else 'common_odd_affine'))+str(len(old['variables'])-(4 if dense else 3))
    cert={'schema':'affine_exposure_v1','endpoint':endpoint,
        'coordinate_shears':SHEARS,'row_operations':ops,'projections':[],'final_row_operations':[]}
    names={v['name']:i for i,v in enumerate(old['variables'])}
    rows=[E.normalize(r['terms']) for r in old['residuals']]
    for target,inputs in SHEARS:
        t=names[target];rest=F.add(F.V(t),{(names[n],):c for n,c in inputs.items()})
        rows=[E.substitute(r,t,rest) for r in rows]
    for i,j,k in ops:rows[i]=F.add(rows[i],{m:k*c for m,c in rows[j].items()})
    for i,name in proj+([((91 if parity else 90),'add.380')] if dense else []):
        t=names[name];q=E.candidate(rows[i],t,False)
        if q is None or E.degree(q)>1:raise ValueError('affine exposure failed')
        cert['projections'].append({'row':i,'variable':t,'name':name,'replacement':E.as_terms(q)})
        rows=[E.substitute(r,t,q) for r in rows]
    return cert

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path,default=ROOT);p.add_argument('--certificate',type=Path)
    p.add_argument('--source',type=Path,default=ROOT/'common_odd250/equation.json');p.add_argument('--parity',action='store_true');p.add_argument('--prefix')
    a=p.parse_args();old=json.loads(a.source.read_text())
    cs=[json.loads(a.certificate.read_text())] if a.certificate else [certificate(old,dense,a.parity,a.prefix) for dense in [False,True]]
    for cert in cs:
        eq,poly,metric=construct(old,cert);out=a.output/cert['endpoint']
        for n,obj in [('certificate.json',cert),('equation.json',eq),('expanded_polynomial.json',poly),('METRICS.json',metric)]:put(out/n,obj)
        print(cert['endpoint'],json.dumps(metric))

if __name__=='__main__':main()
