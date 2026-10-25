#!/usr/bin/env python3
"""Transfer the published affine-exposure identities to the bootstrap quartic."""
import argparse,copy,json
from pathlib import Path
ROOT=Path(__file__).resolve().parent
def add(*ps):
    d={}
    for p in ps:
        for m,c in p.items():d[m]=d.get(m,0)+c
    return {m:c for m,c in d.items() if c}
def scale(p,k):return {m:k*c for m,c in p.items() if k*c}
def mul(a,b):
    d={}
    for m,c in a.items():
        for n,e in b.items():
            k=tuple(sorted(m+n));d[k]=d.get(k,0)+c*e
    return {m:c for m,c in d.items() if c}
def sub(p,v,replacement):
    out={}
    for m,c in p.items():
        w={():c}
        for i in m:w=mul(w,replacement if i==v else {(i,):1})
        out=add(out,w)
    return out
def terms(p):return [[c,list(m)] for m,c in sorted(p.items()) if c]
def decoded(r):return {tuple(m):c for c,m in r['terms']}
def canonical(o):return (json.dumps(o,sort_keys=True,indent=2)+'\n').encode()
SHEARS=[
 ('mul.40',{'crt.encoded.a':-2,'crt.encoded.b':-2}),
 ('mul.53',{'add.50':-8}),
 ('mul.148',{'add.145':-8}),
 ('mul.137',{'crt.encoded.a':-4,'crt.encoded.c':-5,'mul.64':-2,'mul.75':-1}),
 ('mul.75',{'crt.encoded.a':-1,'crt.encoded.c':-1}),
 ('mul.64',{'crt.encoded.b':-1,'crt.encoded.c':-1})]
EXPOSURE=[(21,6,-1),(73,71,-1),(73,70,-4),(73,68,-8),(119,117,-1)]
PROJECTIONS=[(21,'add.145'),(73,'mul.346'),(119,'base4.T')]

def construct(dense=False,affine_radix=False):
    parent_directory='candidate244' if affine_radix else 'candidate245'
    original=json.loads((ROOT/parent_directory/'equation.json').read_text())
    names={v['name']:i for i,v in enumerate(original['variables'])}
    rows=[decoded(r) for r in original['residuals']]
    maps=[{(i,):1} for i in range(len(original['variables']))]
    shears=[]
    for name,inputs in SHEARS:
        v=names[name];replacement={(v,):1}|{(names[n],):k for n,k in inputs.items()}
        rows=[sub(r,v,replacement) for r in rows];maps=[sub(p,v,replacement) for p in maps]
        shears.append({'variable':v,'name':name,'replacement':terms(replacement)})
    for i,j,k in EXPOSURE:rows[i]=add(rows[i],scale(rows[j],k))
    projections=[];deleted_rows=[];deleted_vars=[]
    selected=PROJECTIONS+([(90,'add.380')] if dense else [])
    for ri,name in selected:
        vi=names[name];p=rows[ri];co=p.get((vi,),0)
        if co not in (-1,1) or max(map(len,p),default=0)>1:raise ValueError('Not unit affine '+name)
        replacement=scale({m:c for m,c in p.items() if m!=(vi,)},-co)
        if sub(p,vi,replacement):raise ValueError('Projection equation mismatch')
        rows=[sub(r,vi,replacement) for r in rows];maps=[sub(p,vi,replacement) for p in maps]
        projections.append({'row':ri,'variable':vi,'name':name,'replacement':terms(replacement)})
        deleted_rows.append(ri);deleted_vars.append(vi)
    keep=[i for i in range(len(original['variables'])) if i not in deleted_vars];ren={i:j for j,i in enumerate(keep)}
    def renumber(p):return {tuple(ren[i] for i in m):c for m,c in p.items()}
    rows=[renumber(r) for i,r in enumerate(rows) if i not in deleted_rows];maps=[renumber(p) for p in maps]
    poly=add(*(mul(r,r) for r in rows))
    count=len(keep);e={'schema':'finite_quadratic_residuals_v1','domain':'unrestricted integers','polynomial':'sum(square(row) for row in residuals)','variant':'unified_bootstrap_affine'+str(count),'variables':[original['variables'][i] for i in keep],'residuals':[{'label':f'row.{i:03d}','terms':terms(r)} for i,r in enumerate(rows)]}
    metric={'variables':count,'rows':len(rows),'degree':max(map(len,poly)),'monomials':len(poly),'height':max(map(abs,poly.values())),'row_height':max(abs(c) for r in rows for c in r.values()),'row_support':sum(map(len,rows))}
    cert={'parent_directory':parent_directory,'coordinate_shears':shears,'affine_exposure_row_operations':[list(x) for x in EXPOSURE],'affine_projections':projections,'retained_parent_coordinates':keep,'final_row_operations':[],'inherited_method':'Residual_Bases_Denominator_Engineering/quartic/PROOF.md, applied to the new unified-bootstrap source'}
    restoration={'original_coordinate_count':len(original['variables']),'final_coordinate_count':count,'original_in_final_coordinates':[terms(p) for p in maps]}
    return e,{'schema':'expanded_integer_polynomial_v1','terms':terms(poly)},metric,cert,restoration
def main():
    p=argparse.ArgumentParser();p.add_argument('--dense',action='store_true');p.add_argument('--affine-radix',action='store_true');a=p.parse_args()
    data=construct(a.dense,a.affine_radix);out=ROOT/(('candidate240_affine' if a.dense else 'candidate241_affine') if a.affine_radix else ('candidate241' if a.dense else 'candidate242'));out.mkdir(exist_ok=True)
    for n,o in zip(['equation.json','expanded_polynomial.json','METRICS.json','transformation.json','RESTORATION.json'],data):(out/n).write_bytes(canonical(o))
    print(json.dumps(data[2],sort_keys=True))
if __name__=='__main__':main()
