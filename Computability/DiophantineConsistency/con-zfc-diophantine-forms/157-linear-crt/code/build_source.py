#!/usr/bin/env python3
"""Experimental linear CRT radius and semantic radix bootstrap."""
from pathlib import Path
import copy, json, sys, argparse

BASE=Path(__file__).resolve().parents[1]
PARENT=BASE/'inherited/factorial_free/direct'
sys.path.insert(0,str(PARENT/'parent/code'))
import terminal_elimination as E
import factor_horn as F
import translate_coordinates as T

def write(p,obj):
    p.parent.mkdir(parents=True,exist_ok=True)
    p.write_bytes(E.canonical_bytes(obj))

def run(out,support=16,linear_radius=True,free_radix=True,linear_beta=True,minimal_growth=False):
    old=json.loads((PARENT/'factorial_free_affine/raw_source.json').read_text())
    a=copy.deepcopy(old)
    n={v['name']:i for i,v in enumerate(a['variables'])}
    fv=n['crt.growth_majorant_F'];rv=n['mul.1'];cv=n['crt.encoded_index_minus_one']
    bv=n['choose0.output'];hv=n['self_radix.BH']
    sb=n['beta.odd_square_multiplier'];vb=n['beta.odd_square_root_half']
    tv=n['t0'];dv=n['growth.power_base'];hr=n['cofinal.horizon_root']
    reps=[n['crt.encoded.'+s] for s in ['a','b','c','d','S','Sp','u','vq']]+[cv]
    deletions=[];edits=[];rows=[]
    for i,row in enumerate(a['residuals']):
        p=E.normalize(row['terms'])
        if linear_radius and p=={(rv,):1,(fv,fv):-1}:
            deletions.append({'index':i,'row':row,'reason':'R=F replaces R=F^2 by alias'});continue
        if free_radix and row['label']=='radix.odd_square':
            deletions.append({'index':i,'row':row,'reason':'semantic nonunit-base bootstrap'});continue
        if linear_beta and row['label']=='beta.odd_square_multiplier':
            deletions.append({'index':i,'row':row,'reason':'odd affine beta multiplier'});continue
        if free_radix and row['label']=='self_radix.base_definition':
            p={(hv,):1,(bv,):-38}
            for r in reps:p[tuple(sorted([bv,r]))]=-4
        if minimal_growth and row['label']=='growth.base_definition':
            p={(dv,):1,(tv,):-1,():-16}
        if minimal_growth:p=E.substitute(p,hr,{(hr,):2})
        if linear_radius:p=E.substitute(p,rv,{(fv,):1})
        if free_radix:p=E.substitute(p,cv,{(cv,):2,():-1})
        if linear_beta:p=E.substitute(p,sb,{(vb,):2,():1})
        if E.degree(p)>2:raise RuntimeError(('degree',i))
        rr=dict(row,terms=E.as_terms(p))
        rows.append(rr)
        if rr!=row:edits.append({'index':i,'old':row,'new':rr})
    if len(deletions)!=int(linear_radius)+int(free_radix)+int(linear_beta):raise RuntimeError('deletion census')
    if free_radix:a['variables'][cv]['name']='crt.even_index_half'
    if linear_beta:a['variables'][vb]['name']='beta.odd_multiplier_half'
    a['residuals']=rows
    a['variant']='linear_radius_nonunit_majorant_experiment'
    factored,fc=F.transform(a)
    pr,pc,_=E.optimize(factored,max_support=support)
    E.verify(factored,pr,pc)
    oldpr=json.loads((PARENT/'parent/data/projected.json').read_text())
    oldtc=json.loads((PARENT/'parent/equation/translation_certificate.json').read_text())
    byname={oldpr['variables'][i]['name']:s for i,s in oldtc['shifts']}
    shifts={i:byname[v['name']] for i,v in enumerate(pr['variables']) if v['name'] in byname}
    eq=T.translate(pr,shifts)
    poly=E.expand(eq)
    metrics={'variables':len(eq['variables']),'rows':len(eq['residuals']),
        'degree':max(len(m) for _,m in poly['terms']),'monomials':len(poly['terms']),
        'height':max(abs(c) for c,_ in poly['terms']),
        'row_height':max(abs(c) for r in eq['residuals'] for c,_ in r['terms'])}
    payloads={'raw_source.json':a,'factored_source.json':factored,
        'factorization_certificate.json':fc,'projected.json':pr,
        'projection_certificate.json':pc,
        'translation_certificate.json':{'convention':'old=new+shift','shifts':sorted(shifts.items())},
        'equation.json':eq,'expanded_polynomial.json':poly,'METRICS.json':metrics,
        'mutation.json':{'deletions':deletions,'edits':edits,'linear_radius':linear_radius,'free_radix':free_radix,'linear_beta':linear_beta,'minimal_growth':minimal_growth}}
    for name,obj in payloads.items():write(out/name,obj)
    print(json.dumps(metrics,indent=2))

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--support',type=int,default=16);ap.add_argument('--keep-radius',action='store_true')
    ap.add_argument('--keep-radix',action='store_true');ap.add_argument('--keep-beta-square',action='store_true');ap.add_argument('--minimal-growth',action='store_true');args=ap.parse_args()
    run(args.output,args.support,not args.keep_radius,not args.keep_radix,not args.keep_beta_square,args.minimal_growth)
