#!/usr/bin/env python3
"""Independent strict-output fusion and three complete literal quartics."""
from check_pair_guards import *

def main():
    for item in load('SOURCE_PROVENANCE.json')['files']:
        raw=(HERE/item['local']).read_bytes()
        need(hashlib.sha256(raw).hexdigest()==item['sha256'],'whole copied source '+item['local'])
        need(hashlib.sha1(f'blob {len(raw)}\0'.encode()+raw).hexdigest()==item['git_blob_sha'],'immutable Git source '+item['local'])
    # Includes all six actual source-row pairs and full old/new domains.
    parent69,domain69=check_domain('raw','pair69')
    d69=load('pair69/domain.json');new=load('fused68/parent.json');d68=load('fused68/domain.json')
    n,nr=d69['baseline_body_variables'],d69['baseline_body_rows']
    need(new['domain']==parent69['domain']=='unrestricted integers','integer domain retained')
    need(new['variables'][:n]==parent69['variables'][:n]and new['residuals'][:nr]==parent69['residuals'][:nr],'whole body unchanged by strict-output fusion')
    preds=[g['predicate']for g in d69['guards']if not(g['predicate']['kind']=='retained_scalar'and g['predicate']['raw_variables'][0]in {3,6})]
    need(len(preds)==67,'precisely two old scalar predicates removed')
    preds.append(dict(kind='strict_power_output',raw_variables=[6],terms=[[1,[6]],[-1,[]]]))
    need([g['predicate']for g in d68['guards']]==preds,'strict output bound and all67 retained predicates')
    need(len(new['variables'])==n+204 and len(new['residuals'])==nr+68,'literal68-predicate dimensions')
    for j,(g,p)in enumerate(zip(d68['guards'],preds)):
        a,b,c=range(n+3*j,n+3*j+3)
        need(g['auxiliary']==[a,b,c],'fresh68 guard triple')
        want=p['terms']+[[-1,[a,a]],[-1,[b,b]],[-1,[c,c]],[-1,[c]]]
        need(new['residuals'][nr+j]['terms']==want,'whole68 guard row')
        need(new['variables'][a:c+1]==[dict(kind='nonnegative_guard',name=f'fused68_guard.{j}.{s}')for s in ['a','b','c']],'68guard metadata')
    need(d68['repeated_square_rows']==list(range(2,24))and d68['carrier_rows']==[24,25],'all22 square transitions and carrier rows')
    for row in d68['repeated_square_rows']:
        need(poly(new['residuals'][row]['terms'])==poly([[-1,[row+4,row+4]],[1,[row+5]]]),'literal repeated-square transition')
    got=add(*(poly(new['residuals'][j]['terms'])for j in [24,25]))
    need(got==poly([[1,[28]],[-1,[3]],[-1,[]]]),'complete carrier identity')
    profiles={}
    for name in ['support8','support16_affine2','support32_quadratic_first']:
        path='fused68/'+name;eq=load(path+'/equation.json');cert=load(path+'/projection.json');p=load(path+'/polynomial.json')
        projection=verify(new,eq,cert);need(cert['unconstrained_removed']==[],'no unconstrained lost coordinates')
        expanded=sos(eq);need(expanded==poly(p['terms']),'complete literal fused68 quartic')
        need(p['variables']==len(eq['variables'])and p['domain']==eq['domain']=='unrestricted integers','literal polynomial slots/domain')
        need({v for monomial in expanded for v in monomial}==set(range(len(eq['variables']))),'all and only the declared coordinates occur')
        degree=max(map(len,expanded));need(degree==4,'exact degree4')
        result=dict(variables=len(eq['variables']),quadratic_rows=len(eq['residuals']),degree=degree,monomials=len(expanded),height=max(map(abs,expanded.values())),projection=projection)
        profiles[name]=result;print(name,result,flush=True)
    result=dict(status='PASS',source_commit='84e16e43092614bae262ca59651cb9d77e31a255',old_domain_recovery=domain69,strict_output_fusion=dict(removed_scalar_guards=[3,6],replacement='raw6-1>=0',square_steps=22,source_carrier_identity='raw28=raw3+1'),profiles=profiles,scope='Exact domain and literal-coefficient verification. Unbounded positivity follows by22 square implications plus the proved shared-remainder lemma. Parent75 ordinary C222 calibration is inherited; no new Lean/object-ZFC theorem.')
    (HERE/'CHECK_FUSED68.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print('PASS: fused68')

if __name__=='__main__':main()
