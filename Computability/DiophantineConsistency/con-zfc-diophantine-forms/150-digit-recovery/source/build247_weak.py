#!/usr/bin/env python3
"""Build the raw 247-variable weak-product consistency equation.

The unbounded proof is in ../proofs/NEW_ARGUMENT.md and the accompanying
article. This script materializes the entire polynomial and all exact
integral elimination certificates.
"""
from pathlib import Path
import copy, hashlib, json, sys, argparse

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'inherited_common/code'))
import terminal_elimination as E
import factor_horn as F
import translate_coordinates as T

def sha(o): return hashlib.sha256(E.canonical_bytes(o)).hexdigest()
def put(path,o):
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_bytes(E.canonical_bytes(o))

def build(out,support=16,linear=True):
    inp=HERE/'inherited_common/data'
    old=json.loads((inp/'guarded.json').read_text())
    rc=json.loads((inp/'remainder_transformation.json').read_text())
    source=copy.deepcopy(old)
    names={v['name']:i for i,v in enumerate(source['variables'])}
    q=names['pow2.output']; o=names['choose0.oslack']
    gs=[g for g in rc['new_guards'] if g['kind']=='front_nonnegative' and g['coordinate']==o]
    if len(gs)!=1: raise ValueError('Guard is not unique')
    g=gs[0]; ri=g['row']; aux=g['auxiliary']
    p=E.normalize(source['residuals'][ri]['terms'])
    a,b,c=aux
    if p!={(o,):1,(a,a):-1,(b,b):-1,(c,c):-1,(c,):-1}:
        raise ValueError('Unexpected removed positivity row')
    for j,r in enumerate(source['residuals']):
        if j!=ri and any(v in m for _,m in r['terms'] for v in aux):
            raise ValueError('Guard auxiliaries are not private')
    deleted=source['residuals'].pop(ri)
    z=len(source['variables'])
    source['variables'].append({'name':'odd_radix.root','kind':'signed_witness'})
    newrow={'label':'odd_radix.square','terms':E.as_terms({(q,):1,(z,z):-36,(z,):-36,():-9})}
    source['residuals'].append(newrow)
    source['variant']+=':odd_square_multiple_three_radix'
    source.pop('metrics',None)
    meta=json.loads((inp/'parent_transform_certificate.json').read_text())
    A=names['shared.A']; H=names['cap.H']; f=names['cap.f']; R=names['cap.R']
    C=meta['cap_variables']['Y']; hq=names['cap.h']
    changes=[]
    replacements={
      'cap.comparison_constructor':('cap.deterministic_factor', F.add(F.V(f),F.neg(F.V(H)),E.multiply(F.V(A),F.V(H)))),
      'cap.index_residue':('cap.index_residue',F.add(F.V(R),F.neg(E.normalize(meta['anchor_index'])),F.neg(E.multiply(F.V(C),F.V(hq)))))
    }
    if linear:
        pool={}
        for seed in meta['seed_data']:
            X,Y=seed['pair']
            d=F.add(F.V(Y),F.neg(E.normalize(seed['exponent'])))
            pool=F.add(pool,E.multiply(d,d),{():1},F.neg(F.V(X)))
        pool=F.add(pool,F.neg(E.multiply(F.add(F.V(A),{():-1}),F.V(meta['pooled_quotient']))))
        replacements['cap.pooled_index_residue']=('cap.pooled_index_residue',pool)
    for i,r in enumerate(source['residuals']):
        if r['label'] in replacements:
            lab,p=replacements[r['label']]
            nr={'label':lab,'terms':E.as_terms(p)}
            changes.append({'row':i,'before':r,'after':nr})
            source['residuals'][i]=nr
    if len(changes)!=len(replacements):raise ValueError('Center row identities')
    source['variant']+=':deterministic_center_modC'+(':linear14' if linear else ':squared14')
    # The new signed bootstrap recovers B>0 before using the ceiling guard.
    # Then r*s>=0 and r+s=B-1 imply r,s>=0. The strengthened radix and
    # retained common-denominator ratio authenticate the factorial digit.
    r0=names['fact0.remainder'];s0=names['fact0.slack']
    front=[gg for gg in rc['new_guards'] if gg['kind']=='front_nonnegative' and gg['coordinate'] in [r0,s0]]
    if len(front)!=2:raise ValueError('Two ceiling guards required')
    drop_labels=set();ceiling_deleted=[]
    for gg in front:
        original_row=old['residuals'][gg['row']]
        a0,b0,c0=gg['auxiliary'];co=gg['coordinate']
        if E.normalize(original_row['terms'])!={(co,):1,(a0,a0):-1,(b0,b0):-1,(c0,c0):-1,(c0,):-1}:
            raise ValueError('Ceiling guard formula')
        drop_labels.add(original_row['label'])
        ceiling_deleted.append({'row':original_row,'coordinate':co,'private':gg['auxiliary']})
    source['residuals']=[rr for rr in source['residuals'] if rr['label'] not in drop_labels]
    aa=len(source['variables']);bb=aa+1;cc=aa+2
    source['variables'] += [{'name':'ceiling_product.'+v,'kind':'integer_guard'} for v in ('a','b','c')]
    guardrow={'label':'ceiling_product.weak_guard','terms':E.as_terms(F.add(E.multiply(F.V(r0),F.V(s0)),
        {(aa,aa):-1,(bb,bb):-1,(cc,cc):-1,(cc,):-1}))}
    source['residuals'].append(guardrow)
    source['variant']+=':weak_ceiling_interval_product'
    delta={'schema':'common_remainders_odd_square_v1','input_sha256':sha(old),
           'output_sha256':sha(source),'removed_row_index':ri,'removed_row':deleted,
           'removed_private_auxiliaries':aux,'added_variable':z,'added_row':newrow,
           'radix_coordinate':q,'output_slack_coordinate':o,'center_changes':changes,
           'linear_full_orientation':linear,'center_unused_coordinate':names['cap.d'],
           'parent_metadata_sha256':sha(meta),'radix_scale':3,
           'ceiling_deleted_guards':ceiling_deleted,'ceiling_guard_auxiliaries':[aa,bb,cc],
           'ceiling_added_rows':[guardrow],
           'ceiling_strict':False,
           'ceiling_identity':'r*s=a^2+b^2+c(c+1); B>0 recovered before guard interpretation'}
    factored,fc=F.transform(source)
    projected,pc,metrics=E.optimize(factored,max_support=support)
    verified=E.verify(factored,projected,pc)
    # Reuse the inherited accepted centering chart by coordinate NAME.
    # Every shift is an integer translation, so this is a bijection of Z^n.
    parent_proj=json.loads((inp/'projected.json').read_text())
    parent_tr=json.loads((HERE/'inherited_common/equation/translation_certificate.json').read_text())
    prior_shifts={parent_proj['variables'][i]['name']:d for i,d in parent_tr['shifts']}
    new_names={v['name']:i for i,v in enumerate(projected['variables'])}
    if any(n not in new_names for n in prior_shifts):
        raise ValueError('Centered coordinate deleted or renamed')
    shifts={new_names[n]:d for n,d in prior_shifts.items()}
    eq=T.translate(projected,shifts)
    poly=E.expand(eq)
    met={'variables':len(eq['variables']),'rows':len(eq['residuals']),
         'degree':max(len(m) for c,m in poly['terms']),
         'monomials':len(poly['terms']),'height':max(abs(c) for c,m in poly['terms']),
         'row_height':max(abs(c) for r in eq['residuals'] for c,m in r['terms'])}
    tr={'schema':'integral_translation_v1','input_sha256':sha(projected),
        'output_sha256':sha(eq),'shifts':[[i,d] for i,d in sorted(shifts.items())],
        'convention':'old=new+shift','source_translation_sha256':sha(parent_tr),
        'method':'inherited centering matched by coordinate names'}
    for n,o in [('source.json',source),('delta_certificate.json',delta),
                ('factored_source.json',factored),('factorization_certificate.json',fc),
                ('projected.json',projected),('projection_certificate.json',pc),
                ('translation_certificate.json',tr),('equation.json',eq),
                ('expanded_polynomial.json',poly),('METRICS.json',met),
                ('PROJECTION_CHECK.json',verified)]:
        put(out/n,o)
    print(json.dumps(met,indent=2))
    return met

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--out',type=Path,default=HERE/'equation247_weak')
    p.add_argument('--support',type=int,default=16)
    p.add_argument('--squared',action='store_true')
    a=p.parse_args();build(a.out,a.support,not a.squared)
