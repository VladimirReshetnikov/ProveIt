#!/usr/bin/env python3
"""Strict horizon: unify five range denominators with the index denominator."""
from pathlib import Path
import argparse, copy, json, sys, hashlib
ROOT=Path(__file__).resolve().parent
BASE=ROOT.parent/'sources/factorial_free/direct'
sys.path.insert(0,str(BASE/'parent/code'))
import terminal_elimination as E
import factor_horn as H
import translate_coordinates as T

def build(support=16,base_offset=0,output=None):
    source=BASE/'factorial_free_affine/raw_source.json'
    old=json.loads(source.read_text());new=copy.deepcopy(old)
    names={v['name']:i for i,v in enumerate(new['variables'])}
    f=names['crt.growth_majorant_F']; t0=names['t0']; d=names['growth.power_base']
    q=names['pow2.output']; z=names['radix.odd_square_root_half']; radius=names['mul.1']
    qt=names['pow4.output'];qtp=names['pow6.output']
    removed=set(range(239,247))|{376}
    private=set(range(333,341))
    for i,r in enumerate(old['residuals']):
        if i not in removed and any(private.intersection(m) for _,m in r['terms']):
            raise ValueError(('live private coordinate',i,r['label']))
    if old['residuals'][376]['label']!='remainder_budget.ratio1':raise ValueError('ratio row')
    changes=[];rows=[]
    for i,r in enumerate(old['residuals']):
        if i in removed:continue
        p=E.normalize(r['terms']);label=r['label']
        if label=='growth.base_definition':p={(d,):1,(t0,):-1,():-16-base_offset}
        if label=='radix.odd_square':p={(q,):1,(z,):-4,():-1};label='radix.affine_class'
        if p=={(radius,):1,(f,f):-1}:p={(radius,):1,(f,):-1};label='crt.linear_radius'
        if label=='shared.frame_definition':
            # Remove the obsolete t+1 index and obsolete output, then remove
            # the duplicated base port when the base equals the index t.
            p=H.add(p,{(t0,t0):1,(t0,):34,():289,(qtp,qtp):1})
            if base_offset==0:p=H.add(p,{(d,d):1})
        p=E.substitute(p,qtp,H.V(qt))
        p=E.substitute(p,539,H.V(538))
        rr={'label':label,'terms':E.as_terms(p)}
        if rr!=r:changes.append({'row':i,'old':r,'new':rr})
        rows.append(rr)
    new['residuals']=rows;new['variant']+=':strict_horizon_ranges'
    fac,fc=H.transform(new);pr,pc,_=E.optimize(fac,max_support=support);E.verify(fac,pr,pc)
    op=json.loads((BASE/'parent/data/projected.json').read_text());ot=json.loads((BASE/'parent/equation/translation_certificate.json').read_text())
    byname={op['variables'][i]['name']:s for i,s in ot['shifts']}
    shifts={i:byname[v['name']] for i,v in enumerate(pr['variables']) if v['name'] in byname}
    eq=T.translate(pr,shifts);poly=E.expand(eq)
    metric={'variables':len(eq['variables']),'rows':len(eq['residuals']),'degree':max(len(m) for _,m in poly['terms']),
            'monomials':len(poly['terms']),'height':max(abs(c) for c,_ in poly['terms']),
            'row_height':max(abs(c) for r in eq['residuals'] for c,_ in r['terms'])}
    out=output or ROOT.parent/'direct/source';out.mkdir(parents=True,exist_ok=True)
    objects={'raw_source.json':new,'factorization_certificate.json':fc,'factored_source.json':fac,
             'projected.json':pr,'projection_certificate.json':pc,'equation.json':eq,
             'expanded_polynomial.json':poly,'METRICS.json':metric,
             'translation_certificate.json':{'convention':'old=new+shift','shifts':sorted(shifts.items())},
             'mutation.json':{'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
                              'removed_rows':sorted(removed),'removed_private_coordinates':sorted(private),
                              'range_aliases':[[qtp,qt],[539,538]],'changes':changes,'base_offset':base_offset,
                              'semantic_delta':'Four schema parameters and derived local label are <t. Index is <t as before.'}}
    for k,o in objects.items():(out/k).write_bytes(E.canonical_bytes(o))
    print(json.dumps(metric,indent=2))
if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,help='default: direct/source')
    args=parser.parse_args()
    build(output=args.output)
