#!/usr/bin/env python3
"""Affine self-radix by the retained CRT index divisibility.

Semantic change: D = 2(C+F+1), q=D^x.  Soundness and completeness
are proved in AFFINE_RADIX_PROOF.md, not by polynomial identities alone.
This script uses the pinned incoming package's sparse arithmetic helpers.
"""
from pathlib import Path
import argparse,copy,hashlib,json,sys
ROOT=Path(__file__).resolve().parents[1]/'inherited/anchor'
sys.path.insert(0,str(ROOT/'code'))
from polynomial import *
import reduce_radical
import affine_search
import affine_project


def save(out,eq,cert=None):
    out.mkdir(parents=True,exist_ok=True)
    p=expand(eq)
    met={'variables':len(eq['variables']),'rows':len(eq['residuals']),'degree':degree(p),'monomials':len(p),'height':max(map(abs,p.values())),'row_height':max(abs(c) for r in eq['residuals'] for c,_ in r['terms'])}
    (out/'equation.json').write_bytes(canonical(eq))
    (out/'expanded_polynomial.json').write_bytes(canonical({'schema':'sparse-polynomial-v1','variables':len(eq['variables']),'terms':terms(p)}))
    (out/'metrics.json').write_bytes(canonical(met))
    if cert is not None:(out/'certificate.json').write_bytes(canonical(cert))
    print(out,met,flush=True)
    return met


def build(profile,out):
    inp=ROOT/'source'/profile/'uncontracted.json'
    raw=inp.read_bytes();old=json.loads(raw)
    if old['variables'][194]['name']!='self_radix.BH':raise ValueError('wrong base coordinate')
    # C is actual 2*x17 and F is x2.  These are before compaction.
    D=add(const(2),scale(2,var(2)),scale(4,var(17)))
    deleted=[i for i,r in enumerate(old['residuals']) if r['label']=='self_radix.base_definition']
    if len(deleted)!=1:raise ValueError('bad base-row count')
    eq=copy.deepcopy(old)
    eq['residuals']=[];changes=[]
    for i,r in enumerate(old['residuals']):
        if i in deleted:continue
        p=poly(r['terms']);new=subst(p,194,D)
        if degree(new)>2:raise ValueError('degree increase')
        if new!=p:changes.append({'row':i,'label':r['label'],'before':terms(p),'after':terms(new)})
        eq['residuals'].append(dict(r,terms=terms(new)))
    eq['variant']=old.get('variant','')+':affine_radix_2_C_F_1'
    eq['semantic_radix_base']='2*(C+F+1); C is twice crt.even_index_half'
    eq,ren=compact(eq)
    cert={'schema':'affine-self-radix-source-v1','input_sha256':hashlib.sha256(raw).hexdigest(),'input_profile':profile,'deleted_rows':deleted,'eliminated_coordinate':194,'replacement_original_coordinates':terms(D),'changed_rows':changes,'old_to_new':[[i,j] for i,j in ren.items()]}
    save(out/'source',eq,cert)
    reduced,pc=reduce_radical.reduce(eq)
    save(out/'radical',reduced,pc)
    search=affine_search.run(out/'radical/equation.json')
    (out/'affine_search.json').write_bytes(canonical(search))
    candidates=[]
    for rid,rel in enumerate(search['certified_relations']):
        for v in rel['unit_variables_after_content_normalization']:
            projected,ac=affine_project.project(reduced,rel,v)
            met=save(out/f'affine_r{rid}_v{v}',projected,ac)
            candidates.append((met['height'],met['monomials'],rid,v))
    (out/'summary.json').write_bytes(canonical({'profile':profile,'affine_candidates':candidates}))
    return eq

if __name__=='__main__':
    a=argparse.ArgumentParser();a.add_argument('--profile',choices=['anchor219','anchor220','anchor221'],default='anchor219');a.add_argument('--output',type=Path,required=True)
    v=a.parse_args();build(v.profile,v.output)
