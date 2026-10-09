"""Compare full Euler networks with forced-difference contraction and lifting."""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import platform
import subprocess
import sys
import time
from types import ModuleType
from unittest.mock import patch
from fastunknot import Diagram
from fastunknot.diagram_exterior import diagram_exterior
from fastunknot.normal_cocycle import _rank_one_cocycle_seed_details
from fastunknot.cocycle_span import minimize_cocycle_span
from fastunknot.cocycle_euler import maximize_cocycle_face_euler
from fastunknot.cocycle_euler_flow import _minimize_difference
from fastunknot.normal_cocycle_verify import inspect_cocycle_certificate
from normal_orbit_research import euler,seeds
ROOT=Path(__file__).resolve().parents[1]
BASELINE='18e76fe879fd2c97e86257e1eea6bad1f99f81a6'
PREVIOUS=ROOT.parent/'synthesis/data/cocycle-euler-audit.json'


def baseline():
    path='Topology/UnknotRecognition/fast/fastunknot/cocycle_euler_flow.py'
    source=subprocess.check_output(['git','show',BASELINE+':'+path],cwd=ROOT)
    module=ModuleType('_euler_quotient_baseline');module.__package__='fastunknot';sys.modules[module.__name__]=module
    exec(compile(source,BASELINE+':'+path,'exec'),module.__dict__)
    return module._minimize_difference,sha256(source).hexdigest()


def pins():
    result=euler.pins();result[str(PREVIOUS.relative_to(ROOT.parent))]=sha256(PREVIOUS.read_bytes()).hexdigest()
    return result


def audit(old):
    previous=json.loads(PREVIOUS.read_text())
    with patch('fastunknot.cocycle_euler._minimize_difference',old):before=euler.audit()
    before=seeds.json_safe(before)
    for key,value in before.items():assert value==previous[key],key
    after=seeds.json_safe(euler.audit())
    for a,b in zip(before['source_cases'],after['source_cases']):
        assert a['source']==b['source']
        if a['status']=='COMPLETE':
            assert b['status']=='COMPLETE'
            for key in ('initial_euler','optimum_euler','disc_count','positive','summary'):
                assert a[key]==b[key],(a['source']['name'],key)
    families=[]
    for n in (8,16,32,64,128):
        initial=list(range(n));edges=[[0,v,1-v,1] for v in range(1,n)]
        constraints=[[v,(v+1)%n,((v+1)%n)-v] for v in range(n)]
        pair={}
        for name,fn in [('old',old),('new',_minimize_difference)]:
            work=[0]
            def tick():work[0]+=1
            r=fn(n,edges,constraints,initial,tick)
            assert r['certificate']['objective']==n-1
            pair[name]=dict(stats=r['stats'],work=work[0],proof_sha256=seeds.digest(r['certificate']))
        assert pair['old']['stats']['augmentations']==n-1 and pair['new']['stats']['augmentations']==0
        families.append(dict(vertices=n,results=pair))
    return dict(old_source_cases=before['source_cases'],new=after,cycle_family=families)


def benchmark(old,rounds):
    entries={r['source']['name']:r['source'] for r in json.loads(PREVIOUS.read_text())['source_cases']}
    names=['trefoil','optimized-positive','random-142','random-19','random-158','kinoshita_terasaka','circle-17','circle-33']
    def run(source,use_old):
        with patch('fastunknot.cocycle_euler._minimize_difference',old if use_old else _minimize_difference):
            d=Diagram.from_pd(source['pd']);raw=diagram_exterior(d)
            seed,p=_rank_one_cocycle_seed_details(raw)
            span=minimize_cocycle_span(seed['vertices'],seed['heights'])['certificate']
            result=maximize_cocycle_face_euler(raw,seed['heights'],span)
            proof=euler.source_proof(source,raw,seed,result['certificate'])
            summary=inspect_cocycle_certificate(d,proof)
            assert summary is not None and summary['euler_characteristic']==result['euler_characteristic']
            st=result['stats']
            return dict(completed=True,euler_characteristic=result['euler_characteristic'],disc_count=result['certificate']['disc_count'],
                augmentations=st['augmentations'],quotient_nodes=st.get('quotient_nodes',st['network_nodes']-2),work=st['work'],
                proof_sha256=seeds.digest(proof))
    return seeds.rounds([(name,entries[name]) for name in names],run,rounds)


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('mode',choices=('audit','benchmark'))
    parser.add_argument('--rounds',type=int,default=5);parser.add_argument('--output',type=Path,required=True);args=parser.parse_args()
    if args.rounds<1:parser.error('rounds must be positive')
    old,digest=baseline();before=pins();start=time.perf_counter()
    result=audit(old) if args.mode=='audit' else benchmark(old,args.rounds)
    assert pins()==before
    result.update(source_sha256=before,baseline_commit=BASELINE,baseline_flow_sha256=digest,
                  mode=args.mode,elapsed_seconds=time.perf_counter()-start,python=platform.python_version())
    args.output.write_text(json.dumps(seeds.json_safe(result),indent=2)+'\n')
    print('complete',args.mode,result['elapsed_seconds'],flush=True)
if __name__=='__main__':main()
