#!/usr/bin/env python3
"""Independent polynomial-identity audit of affine projections and row bases."""
import argparse,copy,json,sys
from pathlib import Path
from verify249 import read,need,sparse,terms,plus,multiply
ROOT=Path(__file__).resolve().parent

def scale(p,k):return {m:k*c for m,c in p.items() if k*c}
def subst(p,v,replacement):
    result={}
    for m,c in p.items():
        term={():c}
        for j in m:term=multiply(term,replacement if j==v else {(j,):1})
        result=plus(result,term)
    return result
def simultaneous(p,images):
    result={}
    for m,c in p.items():
        term={():c}
        for j in m:term=multiply(term,images[j])
        result=plus(result,term)
    return result

def audit(e,poly,metric,cert,restoration):
    parent=cert.get('parent_directory','candidate245')
    need(parent in ['candidate245','candidate244'],'Unrecognized parent')
    original=read(ROOT/parent/'equation.json');rows=[sparse(r['terms']) for r in original['residuals']]
    maps=[{(j,):1} for j in range(len(original['variables']))]
    for op in cert['coordinate_shears']:
        v=op['variable'];replacement=sparse(op['replacement'])
        need(original['variables'][v]['name']==op['name'],'Coordinate name mismatch')
        need(replacement.get((v,))==1 and max(map(len,replacement),default=0)<=1,'Invalid affine shear')
        need(all(m==(v,) or v not in m for m in replacement),'Target in shear remainder')
        inverse=plus({(v,):2},scale(replacement,-1))
        need(subst(replacement,v,inverse)=={(v,):1},'Shear inverse identity fails')
        rows=[subst(r,v,replacement) for r in rows];maps=[subst(p,v,replacement) for p in maps]
    for i,j,k in cert['affine_exposure_row_operations']:
        need(i!=j and isinstance(k,int),'Nonunimodular row action')
        old=rows[i];rows[i]=plus(rows[i],scale(rows[j],k))
        need(plus(rows[i],scale(rows[j],-k))==old,'Row inverse fails')
    deleted_rows=[];deleted_vars=[]
    for op in cert['affine_projections']:
        i,v=op['row'],op['variable'];replacement=sparse(op['replacement']);p=rows[i]
        need(v not in deleted_vars and i not in deleted_rows,'Repeated projection')
        need(original['variables'][v]['name']==op['name'],'Projection name mismatch')
        need(max(map(len,p),default=0)<=1 and p.get((v,)) in (-1,1),'Projection not unit affine')
        need(all(v not in m for m in replacement) and max(map(len,replacement),default=0)<=1,'Bad restoration expression')
        need(not subst(p,v,replacement),'Projected row does not vanish identically')
        rows=[subst(r,v,replacement) for r in rows];maps=[subst(p,v,replacement) for p in maps]
        need(not rows[i],'Deleted row is nonzero');deleted_rows.append(i);deleted_vars.append(v)
    keep=[j for j in range(len(original['variables'])) if j not in deleted_vars]
    need(cert['retained_parent_coordinates']==keep,'Coordinate restriction differs')
    ren={v:i for i,v in enumerate(keep)}
    def renum(p):
        need(not any(v in deleted_vars for m in p for v in m),'Deleted coordinate survives')
        return {tuple(ren[v] for v in m):c for m,c in p.items()}
    allrows=[renum(r) for r in rows];maps=[renum(p) for p in maps]
    need(restoration['original_in_final_coordinates']==[terms(p) for p in maps],'Complete affine restoration map differs')
    need(restoration['original_coordinate_count']==len(original['variables']) and restoration['final_coordinate_count']==len(keep),'Restoration dimensions differ')
    # Undo the exposure rows and compare every original residual after the
    # complete affine coordinate restoration: a universal identity check.
    pullbacks=copy.deepcopy(allrows)
    for i,j,k in reversed(cert['affine_exposure_row_operations']):pullbacks[i]=plus(pullbacks[i],scale(pullbacks[j],-k))
    for i,r in enumerate(original['residuals']):
        need(simultaneous(sparse(r['terms']),maps)==pullbacks[i],'Original-row pullback identity fails')
    rows=[r for i,r in enumerate(allrows) if i not in deleted_rows]
    for i,j,k in cert['final_row_operations']:
        need(i!=j and isinstance(k,int),'Invalid final row action')
        old=rows[i];rows[i]=plus(rows[i],scale(rows[j],k))
        need(plus(rows[i],scale(rows[j],-k))==old,'Final row inverse fails')
    need(e['variables']==[original['variables'][i] for i in keep],'Final variable list differs')
    need(e['residuals']==[{'label':f'row.{i:03d}','terms':terms(r)} for i,r in enumerate(rows)],'Final residual list differs')
    acc={}
    for r in rows:
        need(max(map(len,r),default=0)<=2,'Residual degree increased')
        acc=plus(acc,multiply(r,r))
    need(sparse(poly['terms'])==acc,'Collected quartic differs')
    need({v for m in acc for v in m}==set(range(len(keep))),'Inactive final variable')
    actual={'variables':len(keep),'rows':len(rows),'degree':max(map(len,acc)),'monomials':len(acc),'height':max(map(abs,acc.values())),'row_height':max(abs(c) for r in rows for c in r.values()),'row_support':sum(map(len,rows))}
    need(metric==actual,'Metric mismatch')
    return {'metrics':actual,'coordinate_shears':len(cert['coordinate_shears']),'exposure_row_actions':len(cert['affine_exposure_row_operations']),'affine_projections':len(cert['affine_projections']),'final_row_actions':len(cert['final_row_operations']),'original_row_pullbacks_checked':len(original['residuals'])}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--profile',default='equation242');ap.add_argument('--no-controls',action='store_true');a=ap.parse_args()
    base=ROOT/a.profile;names=['equation.json','expanded_polynomial.json','METRICS.json','transformation.json','RESTORATION.json'];obs=[read(base/n) for n in names];report=audit(*obs)
    mutations=[]
    if not a.no_controls:
        x=copy.deepcopy(obs);x[3]['coordinate_shears'][0]['replacement'][0][0]+=1;mutations.append(('coordinate shear',x))
        x=copy.deepcopy(obs);x[3]['affine_exposure_row_operations'][0][2]+=1;mutations.append(('row exposure',x))
        x=copy.deepcopy(obs);x[3]['affine_projections'][0]['replacement'][0][0]+=1;mutations.append(('unit affine restoration',x))
        x=copy.deepcopy(obs);x[4]['original_in_final_coordinates'][0][0][0]+=1;mutations.append(('composed restoration',x))
        x=copy.deepcopy(obs);x[0]['residuals'][3]['terms'][0][0]+=1;mutations.append(('final row coefficient',x))
        x=copy.deepcopy(obs);x[1]['terms'][10][0]+=1;mutations.append(('quartic coefficient',x))
        if obs[3]['final_row_operations']:
            x=copy.deepcopy(obs);x[3]['final_row_operations'][0][2]+=1;mutations.append(('final row shear',x))
    rejected=[]
    for name,x in mutations:
        try:audit(*x)
        except ValueError:rejected.append(name)
        else:raise ValueError('Accepted mutation: '+name)
    report.update({'status':'PASS','profile':a.profile,'optimized':bool(sys.flags.optimize),'rejected_controls':rejected,'scope':'Exact bijective integer coordinate maps, reversible residual row operations, all original-row pullback identities, and full SOS coefficient collection.'})
    print(json.dumps(report,indent=2))
if __name__=='__main__':main()
