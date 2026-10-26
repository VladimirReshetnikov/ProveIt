#!/usr/bin/env python3
"""A diagonal growth certificate and an affine, nonunit radix.

The ordinary mathematical proof is separate. This deterministic producer
records each raw edit and reuses the inherited exact polynomial compiler.
"""
from pathlib import Path
import argparse, copy, hashlib, json, sys

ROOT=Path(__file__).resolve().parent
BASE=ROOT/'baseline/direct'
sys.path.insert(0,str(BASE/'parent/code'))
import terminal_elimination as E
import factor_horn as F
import translate_coordinates as T

def write(p,obj):
    p.parent.mkdir(parents=True,exist_ok=True)
    p.write_bytes(E.canonical_bytes(obj))

def build(output):
    parent=BASE/'factorial_free_affine/raw_source.json'
    old=json.loads(parent.read_text())
    source=copy.deepcopy(old)
    name={v['name']:i for i,v in enumerate(source['variables'])}
    horizon=name['t0']
    root=name['cofinal.horizon_root']
    powerbase=name['growth.power_base']
    q=name['pow2.output']
    z=name['radix.odd_square_root_half']
    B=name['choose0.output']
    BH=name['self_radix.BH']
    y=name['y']
    majorant=name['crt.growth_majorant_F']
    oldshift=name['mul.1']
    beta_parameter=name['beta.odd_square_root_half']
    reps=['crt.encoded.a','crt.encoded.b','crt.encoded.c','crt.encoded.d',
          'crt.encoded.S','crt.encoded.Sp','crt.encoded.u','crt.encoded.vq',
          'crt.encoded_index_minus_one']
    replacements={
        'cofinal.horizon': {(horizon,):1,(root,root):-2},
        'growth.base_definition': {(powerbase,):1,(horizon,):-1,():-16},
        'radix.odd_square': {(q,):1,(z,):-6,():-3},
        'self_radix.base_definition': {(BH,):1,(B,):-57,
            **{tuple(sorted([B,name[r]])):-6 for r in reps}},
        'bootstrap.beta_base_square_product': {(y,):1,(majorant,):-1,
            tuple(sorted([majorant,beta_parameter])):-2},
    }
    edits=[]
    seen=set()
    for i,row in enumerate(source['residuals']):
        label=row['label']
        if label not in replacements: continue
        if label in seen:raise ValueError('nonunique row '+label)
        seen.add(label)
        rr={'label':label.replace('radix.odd_square','radix.nonunit_affine'),
            'terms':E.as_terms(replacements[label])}
        edits.append({'row':i,'before':copy.deepcopy(row),'after':rr})
        source['residuals'][i]=rr
    if seen!=set(replacements):raise ValueError('missing source edit')
    drop=[i for i,r in enumerate(source['residuals']) if r['label']=='beta.odd_square_multiplier']
    if len(drop)!=1:raise ValueError('beta square row is not unique')
    j=drop[0]
    edits.append({'row':j,'before':copy.deepcopy(source['residuals'][j]),'after':None})
    source['residuals'].pop(j)
    expected_shift={(oldshift,):1,(majorant,majorant):-1}
    hits=[i for i,r in enumerate(source['residuals']) if E.normalize(r['terms'])==expected_shift]
    if len(hits)!=1:raise ValueError('binomial shift square row is not unique')
    j=hits[0]
    alias_edit={'row_after_beta_drop':j,'before':copy.deepcopy(source['residuals'][j]),
        'alias_from':oldshift,'alias_to':majorant}
    source['residuals'].pop(j)
    for row in source['residuals']:
        row['terms']=E.as_terms(E.substitute(E.normalize(row['terms']),oldshift,F.V(majorant)))
    source['variant']='diagonal_growth_even_horizon_nonunit_affine_radix'
    source['variables'][powerbase]['name']='growth.diagonal_base'
    source['variables'][z]['name']='radix.odd_multiple_of_three_parameter'
    source['variables'][beta_parameter]['name']='beta.odd_multiplier_parameter'
    factored,fc=F.transform(source)
    projected,pc,_=E.optimize(factored,max_support=16)
    replay=E.verify(factored,projected,pc)
    oldprojected=json.loads((BASE/'parent/data/projected.json').read_text())
    oldtranslation=json.loads((BASE/'parent/equation/translation_certificate.json').read_text())
    shiftsbyname={oldprojected['variables'][i]['name']:s for i,s in oldtranslation['shifts']}
    shifts={i:shiftsbyname[v['name']] for i,v in enumerate(projected['variables']) if v['name'] in shiftsbyname}
    equation=T.translate(projected,shifts)
    poly=E.expand(equation)
    metrics={'variables':len(equation['variables']),'rows':len(equation['residuals']),
        'degree':max(len(m) for _,m in poly['terms']),'monomials':len(poly['terms']),
        'height':max(abs(c) for c,_ in poly['terms']),
        'row_height':max(abs(c) for r in equation['residuals'] for c,_ in r['terms'])}
    provenance={'parent':str(parent.relative_to(ROOT)),
        'parent_sha256':hashlib.sha256(parent.read_bytes()).hexdigest(),
        'new_semantics':['t=16+2*h^2','F=t^t','R=F','q=6*z+3','y=F*(2*v+1)',
            'H=3+6*sum(actual CRT representatives)','self_radix_base=B*H'],
        'edits':edits,
        'binomial_shift_alias':alias_edit,
        'proof_status':'ordinary proof in PROOF.md; finite compiler replay is not semantic proof'}
    for file,obj in [('raw_source.json',source),('source_delta.json',provenance),
        ('factored_source.json',factored),('factorization_certificate.json',fc),
        ('projected.json',projected),('projection_certificate.json',pc),
        ('projection_check.json',replay),('translation_certificate.json',{'convention':'old=new+shift','shifts':sorted(shifts.items())}),
        ('equation.json',equation),('expanded_polynomial.json',poly),('METRICS.json',metrics)]:write(output/file,obj)
    print(json.dumps(metrics,sort_keys=True))

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,default=ROOT/'diagonal_raw')
    build(ap.parse_args().output)
