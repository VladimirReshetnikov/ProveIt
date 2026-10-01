"""Compose zero-based controller geometry with shared physical packing."""
import argparse
from collections import Counter
import json
from pathlib import Path
import random

import group_projective_reindexed_edge_geometry as geometry
import group_projective_shared_selector_pack as packing

execute=geometry.execute
residuals=geometry.residuals


def build(codes,alpha=24,beta=12,variant='joint',controller_mask=False,compute_length=False):
    old=geometry.build(codes,alpha,beta,variant,controller_mask,compute_length)
    return packing.rewrite(old)


def polynomial_source(packet):return geometry.polynomial_source(packet)


def degree_top(packet,weights):return geometry.degree_top(packet,weights)


def verify():
    rng=random.Random(2453504);records=[];cases=signed=aliases=0;example=None
    tables=[(),((1,),),((8,),),((1,2),),((1,2,3),),((1,2),(3,4)),
            (tuple(range(1,9)),),((8,6,4,2,7,5,3,1),),
            ((1,2,3,4,5,6,7,8,1,2),),((1,),(2,3,4),(5,)),
            (tuple(1+i%8 for i in range(16)),),((1,2,3),(4,5),(6,7,8))]
    for codes in tables:
      for variant in ('four','six','shifted','strong','joint'):
       for reuse in (False,True):
        if reuse and geometry.parent.build(codes)['m']<8:continue
        for comp in (False,True):
            old=geometry.build(codes,variant=variant,controller_mask=reuse,compute_length=comp)
            packet=packing.rewrite(old)
            source,out=polynomial_source(packet);prior,prior_out=geometry.polynomial_source(old)
            assert packet['comparisons']==old['comparisons'] and packet['auxiliaries']==old['auxiliaries']
            assert packet['operations']<=old['operations']
            candidates=packet.get('shared_selector_candidates',[])
            alias_plans=[plan for plan in candidates if plan.get('aliases')]
            if alias_plans:
                assert packet['shared_selector_plan']=='anchor correction'
                assert packet['shared_selector_base']==packet['shared_selector_anchor']==0
                assert min(plan['operations'] for plan in alias_plans)==0
                assert 'selection__Sbatch' not in {row[0] for row in packet['source']}
                aliases+=1
            for case in range(24):
                positive=case<16
                values={name:rng.randrange(1,6) if positive else rng.randrange(-3,4)
                        for name in packet['parameters']+packet['auxiliaries']}
                env,before=execute(source,values),execute(prior,values)
                assert all(env[name]==before[name] for name,_,_,_ in source if name in before)
                assert residuals(packet,env)==residuals(old,before) and env[out]==before[prior_out]
                cases+=1;signed+=not positive
            weights={name:1+i%3 for i,name in enumerate(packet['parameters']+packet['auxiliaries'])}
            weights['selection__tau_gap']=1
            for e,name in enumerate(packet['controller_edge_coordinates']):weights[name]=1<<e
            degree,top=degree_top(packet,weights)[:2]
            assert (degree,top)==geometry.degree_top(old,weights)[:2] and top
            counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
            records.append(dict(codes=codes,old_m=old['old_geometry_m'],m=packet['m'],variant=variant,
                controller_mask=reuse,compute_length=comp,reindexed=old['reindexed_edges'],
                geometry_saving=old['reindexed_saving'],packing_plan=packet['shared_selector_plan'],
                packing_saving=packet['shared_selector_saving'],has_alias_plan=bool(alias_plans),
                certificate_operations=packet['operations'],polynomial_operations=len(source),
                polynomial_M=counts['M'],polynomial_A=counts['A'],equations=packet['equations'],
                positive_witnesses=packet['positive_witnesses'],exact_degree=degree))
            if codes==tables[8] and variant=='joint' and reuse and comp:
                example=dict(packet,polynomial_finalizer=source[packet['operations']:],polynomial_output=out)
                assert (packet['operations'],len(source),counts['M'],counts['A'],degree)==(228,245,104,141,3504)
    assert aliases>0
    return dict(status='PASS_GROUP_PROJECTIVE_REINDEXED_SHARED_PACK',records=records,source_example=example,
                complete_source_identity_cases=cases,signed_cases=signed,zero_cost_alias_ledgers=aliases,
                scope='The shared-pack rewrite is an all-integer identity of the reindexed geometry source. '
                      'Geometry reindexing preserves the existential input predicate through fresh native witnesses. '
                      'No numerical universal alphabet or improvement of the separate75/88 frontier is claimed.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])
