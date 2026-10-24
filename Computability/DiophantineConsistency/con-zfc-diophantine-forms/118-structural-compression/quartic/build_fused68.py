#!/usr/bin/env python3
"""Fuse the carrier/output signs after the six shared-remainder cuts."""
from build_pair_guards import *

def main():
    old=read('pair69/parent.json');domain=read('pair69/domain.json')
    n,nr=domain['baseline_body_variables'],domain['baseline_body_rows']
    preds=[g['predicate']for g in domain['guards']if not(g['predicate']['kind']=='retained_scalar'and g['predicate']['raw_variables'][0]in {3,6})]
    preds.append(dict(kind='strict_power_output',raw_variables=[6],terms=[[1,[6]],[-1,[]]]))
    if len(preds)!=68:raise ValueError('68 predicate boundary')
    new=dict(schema='quadratic_sum_squares_v1',domain='unrestricted integers',variant='shared_modulus_pair68_raw',variables=copy.deepcopy(old['variables'][:n]),residuals=copy.deepcopy(old['residuals'][:nr]))
    guards=[]
    for j,p in enumerate(preds):
        a,b,c=range(len(new['variables']),len(new['variables'])+3)
        new['variables'].extend(dict(kind='nonnegative_guard',name=f'fused68_guard.{j}.{s}')for s in ['a','b','c'])
        new['residuals'].append(dict(label=f'fused68_guard.{j}',terms=p['terms']+[[-1,[a,a]],[-1,[b,b]],[-1,[c,c]],[-1,[c]]]))
        guards.append(dict(predicate=p,auxiliary=[a,b,c]))
    write('fused68/parent.json',new)
    write('fused68/domain.json',dict(baseline_body_variables=n,baseline_body_rows=nr,guards=guards,removed_scalar_indices=[3,6],introduced_lower_bound=[6,1],repeated_square_rows=list(range(2,24)),carrier_rows=[24,25]))
    census={}
    for name,cap,affine,qfirst in [('support8',8,None,False),('support16_affine2',16,2,False),('support32_quadratic_first',32,None,True)]:
        out,cert,metrics=engine.optimize(new,max_support=cap,affine_support=affine,quadratic_first=qfirst)
        normalize_projection_metadata(out,cert)
        engine.verify(new,out,cert)
        if cert['unconstrained_removed']:raise ValueError('unconstrained deletion')
        path='fused68/'+name
        write(path+'/equation.json',out);write(path+'/projection.json',cert);write(path+'/polynomial.json',engine.expand(out))
        census[path]=metrics;print(path,metrics,flush=True)
    write('FUSED_CENSUS.json',census)

if __name__=='__main__':main()
