#!/usr/bin/env python3
"""Reproduce exhaustive and seeded independent checks. Standard library only."""
import sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
import json,time,random,platform
from itertools import product
from pivotwidth import Instance,Decomposition,optimize,replay
from pivotwidth.verify import transport
from pivotwidth.transfer import power_certificate,expand,compile_transfer
from pivotwidth.transfer_verify import verify_power,reference_transfer
from scripts.oracles import subset_value,positive_value,alternating_value,private_value
from examples.templates import defect_tile,path_tile


def run():
    start=time.perf_counter();counts={};maxwidth=0;maxstates=0
    for m,n,alphabet in [(2,4,3),(3,3,3),(4,2,3),(4,3,2)]:
        count=0
        for vv in product(range(alphabet),repeat=m*n):
            a=[list(vv[i*n:(i+1)*n]) for i in range(m)]
            inst=Instance.from_dense(a);out=optimize(inst);oracle=subset_value(a)
            assert out['retained_weight']==oracle,(a,out,oracle)
            replay(a,[1]*m,out)
            maxwidth=max(maxwidth,out['stats']['width']);maxstates=max(maxstates,out['stats']['peak_states'])
            count+=1
        counts[f'all_{alphabet}ary_{m}x{n}']=count
        print('complete',m,n,count,round(time.perf_counter()-start,3),flush=True)
    count=0
    for vv in product(range(3),repeat=9):
        a=[list(vv[i*3:(i+1)*3]) for i in range(3)]
        s=subset_value(a)
        assert s==positive_value(a)==alternating_value(a)
        count+=1
    counts['positive_and_unique_matching_oracles_3x3']=count
    print('complete positive oracles',round(time.perf_counter()-start,3),flush=True)
    rng=random.Random(20261012)
    for _ in range(300):
        m,n=rng.randrange(1,6),rng.randrange(1,6)
        a=[[rng.choice([0,0,0,0,1,1,2,3]) for _ in range(n)] for _ in range(m)]
        w=[rng.randrange(0,20) for _ in range(m)]
        inst=Instance.from_dense(a,w);out=optimize(inst)
        assert out['retained_weight']==subset_value(a,w)
        rr=replay(a,w,out);tr=transport(a,rr['schedule'])
        assert tr['remaining_rows']==out['deferred_rows']
        maxwidth=max(maxwidth,out['stats']['width']);maxstates=max(maxstates,out['stats']['peak_states'])
    counts['seeded_weighted_and_passive_transport']=300
    print('complete random',round(time.perf_counter()-start,3),flush=True)
    for _ in range(150):
        m,n=rng.randrange(1,5),rng.randrange(1,5)
        a=[[rng.randrange(3) for _ in range(n)] for _ in range(m)]
        w=[rng.randrange(8) for _ in range(m)]
        fr={i for i in range(m) if rng.randrange(4)==0};fc={j for j in range(n) if rng.randrange(4)==0}
        forbidden={(i,j) for i in range(m) for j in range(n) if i in fr or j in fc}
        out=optimize(Instance.from_dense(a,w,forbidden_rows=fr,forbidden_columns=fc))
        assert out['retained_weight']==private_value(a,w,forbidden)
        replay(a,w,out,forbidden_pivots=forbidden)
    counts['restricted_private_pivot_instances']=150
    for _ in range(80):
        m,n=3,3
        a=[[rng.randrange(3) for j in range(n)] for i in range(m)]
        inst=Instance.from_dense(a)
        # A deliberately wide one-bag decomposition gives the same answer as the heuristic.
        full=Decomposition((frozenset(range(m+n)),),(None,),0)
        assert optimize(inst,full)['retained_weight']==optimize(inst)['retained_weight']
    counts['different_decompositions']=80
    print('complete decompositions',round(time.perf_counter()-start,3),flush=True)
    pc=0
    for vals in product([1,2],repeat=4):
        for weights in [(1,1),(3,7),(0,5)]:
            p=defect_tile(*weights,*vals)
            assert compile_transfer(p)['matrix']==reference_transfer(p)[0]
            for exponent in range(7):
                cert=power_certificate(p,exponent);verify_power(cert);x=expand(p,exponent)
                out=optimize(Instance.from_dense(x['matrix'],x['weights'],columns=x['columns']))
                assert cert['retained_weight']==out['retained_weight']
                pc+=1
    counts['power_expansion_comparisons']=pc
    huge=power_certificate(defect_tile(3,7),1<<1024);verify_power(huge)
    assert huge['deferred_weight']==3*(1<<1024)
    (ROOT/'results'/'huge_power_certificate.json').write_text(json.dumps(huge,separators=(',',':'))+'\n')
    data={'status':'PASS','seed':20261012,'python':sys.version,'platform':platform.platform(),
          'counts':counts,'maximum_observed_heuristic_width':maxwidth,
          'maximum_observed_states':maxstates,
          'huge_power':{'exponent':'2^1024','retained_weight':'7*2^1024',
                        'deferred_weight':'3*2^1024',**huge['stats']},
          'seconds':time.perf_counter()-start,
          'scope':'Synthetic abstract unsigned matrices and graph templates; no native geometric or knot benchmark.'}
    (ROOT/'results'/'audit.json').write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps(data,indent=2))

if __name__=='__main__':run()
