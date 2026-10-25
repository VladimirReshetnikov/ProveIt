#!/usr/bin/env python3
"""Transport the inherited integral shears and row basis to strict horizons.

Original raw-row identities, rather than guessed offsets, transport the
row operations. Every affine pivot is then recomputed from its actual row.
"""
from pathlib import Path
import argparse, copy, hashlib, json, sys
ROOT=Path(__file__).resolve().parent
SOURCE=ROOT.parent/'direct/source'
PARENT=ROOT.parent/'sources/factorial_free/direct'
OUTPUT=ROOT.parent/'direct'

def load(p):return json.loads(p.read_text())
def put(p,o):p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(E.canonical_bytes(o))
def sourcekeys(raw,fc,raw_keys=None):
    keys=list(range(len(raw['residuals']))) if raw_keys is None else list(raw_keys)
    keys.append('factored_horn_appended')
    return [k for i,k in enumerate(keys) if i not in fc['deleted_rows']]
def metric(eq,poly):
    return {'variables':len(eq['variables']),'rows':len(eq['residuals']),'degree':max(len(m) for _,m in poly['terms']),'monomials':len(poly['terms']),'height':max(abs(c) for c,_ in poly['terms']),'row_height':max(abs(c) for r in eq['residuals'] for c,_ in r['terms'])}

def construct(dense=False):
    global E,F
    sys.path.insert(0,str(PARENT/'parent/code'))
    import terminal_elimination as E
    import factor_horn as F
    oldroot=PARENT/'factorial_free_affine'
    oldraw=load(oldroot/'raw_source.json');oldfc=load(oldroot/'factorization_certificate.json');oldpc=load(oldroot/'projection_certificate.json')
    newraw=load(SOURCE/'raw_source.json');newfc=load(SOURCE/'factorization_certificate.json');newpc=load(SOURCE/'projection_certificate.json');delta=load(SOURCE/'mutation.json')
    oldfk=sourcekeys(oldraw,oldfc)
    rawkeys=[i for i in range(len(oldraw['residuals'])) if i not in delta['removed_rows']]
    if len(rawkeys)!=len(newraw['residuals']):raise ValueError('raw provenance mismatch')
    newfk=sourcekeys(newraw,newfc,rawkeys)
    oldpk=[oldfk[i] for i in oldpc['retained_original_rows']]
    newpk=[newfk[i] for i in newpc['retained_original_rows']]
    key_to_new={k:i for i,k in enumerate(newpk)}
    maprow=lambda i:key_to_new[oldpk[i]]
    old=load(SOURCE/'equation.json');rows=[E.normalize(r['terms']) for r in old['residuals']]
    names={v['name']:i for i,v in enumerate(old['variables'])}
    parent_tag='factorial_free_affine'+('241' if dense else '242')+'_balanced'
    ac=load(PARENT/parent_tag/'certificate.json')
    cert={'schema':'strict_horizon_affine_exposure_v1','source_sha256':hashlib.sha256((SOURCE/'equation.json').read_bytes()).hexdigest(),'parent_certificate_sha256':hashlib.sha256((PARENT/parent_tag/'certificate.json').read_bytes()).hexdigest(),'coordinate_shears':ac['coordinate_shears'],'row_operations':[],'projections':[],'final_row_operations':[],'omitted_parent_final_operations':[],'raw_row_provenance_before_projection':newpk}
    for target,inputs in ac['coordinate_shears']:
        t=names[target];replacement=F.add(F.V(t),{(names[n],):c for n,c in inputs.items()})
        rows=[E.substitute(p,t,replacement) for p in rows]
    for i,j,k in ac['row_operations']:
        ni,nj=maprow(i),maprow(j);rows[ni]=F.add(rows[ni],{m:k*c for m,c in rows[nj].items()})
        cert['row_operations'].append([ni,nj,k])
    removed_rows=set();removed_vars=set()
    for st in ac['projections']:
        ri=maprow(st['row']);v=names[st['name']];replacement=E.candidate(rows[ri],v,False)
        if replacement is None or E.degree(replacement)>1:raise ValueError(('failed affine pivot',ri,st['name']))
        cert['projections'].append({'row':ri,'variable':v,'name':st['name'],'replacement':E.as_terms(replacement)})
        rows=[E.substitute(p,v,replacement) for p in rows]
        if rows[ri]:raise ValueError('removed row nonzero')
        removed_rows.add(ri);removed_vars.add(v)
    keep=[i for i in range(len(old['variables'])) if i not in removed_vars]
    ren={v:i for i,v in enumerate(keep)}
    remain_rows=[i for i in range(len(rows)) if i not in removed_rows]
    finalkeys=[newpk[i] for i in remain_rows]
    rows=[{tuple(ren[x] for x in m):c for m,c in rows[i].items()} for i in remain_rows]
    parent_removed={st['row'] for st in ac['projections']}
    parent_finalkeys=[k for i,k in enumerate(oldpk) if i not in parent_removed]
    final_key_to_new={k:i for i,k in enumerate(finalkeys)}
    for op in ac['final_row_operations']:
        i,j,k=op;ki,kj=parent_finalkeys[i],parent_finalkeys[j]
        if ki not in final_key_to_new or kj not in final_key_to_new:
            cert['omitted_parent_final_operations'].append({'operation':op,'raw_target':ki,'raw_input':kj})
            continue
        ni,nj=final_key_to_new[ki],final_key_to_new[kj]
        rows[ni]=F.add(rows[ni],{m:k*c for m,c in rows[nj].items()})
        cert['final_row_operations'].append([ni,nj,k])
    eq={'schema':'finite_quadratic_residuals_v1','domain':'unrestricted integers','variant':'strict_horizon_'+('235' if dense else '236'),'polynomial':'sum(square(row) for row in residuals)','variables':[old['variables'][i] for i in keep],'residuals':[dict(old['residuals'][i],terms=E.as_terms(p)) for i,p in zip(remain_rows,rows)]}
    cert['retained_variables']=keep;cert['retained_rows']=remain_rows;cert['raw_row_provenance_final']=finalkeys
    poly=E.expand(eq);m=metric(eq,poly)
    out=OUTPUT/('dense235' if dense else 'principal236')
    for name,obj in [('equation.json',eq),('expanded_polynomial.json',poly),('METRICS.json',m),('certificate.json',cert)]:put(out/name,obj)
    return m,cert['omitted_parent_final_operations']

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--source',type=Path,default=SOURCE)
    ap.add_argument('--parent',type=Path,default=PARENT)
    ap.add_argument('--output',type=Path,default=OUTPUT)
    a=ap.parse_args();SOURCE=a.source.resolve();PARENT=a.parent.resolve();OUTPUT=a.output.resolve()
    print(json.dumps({k:construct(v) for k,v in [('principal',False),('dense',True)]},indent=2))
