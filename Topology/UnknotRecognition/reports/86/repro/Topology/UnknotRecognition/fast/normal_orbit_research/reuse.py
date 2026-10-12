"""Validate and time per-search geometry reuse with independent positive replay."""
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
from fastunknot import Diagram,recognize
from fastunknot.normal_seed import normal_seed_decide
from fastunknot.normal_seed_verify import verify_normal_seed_certificate
from fastunknot.diagram_exterior import diagram_exterior
from fastunknot.normal_cocycle import _rank_one_cocycle_seed_details,_height_summary
from fastunknot.cocycle_trees import cocycle_tree_candidates
from fastunknot.cocycle_span import minimize_cocycle_span
from fastunknot.normal_surface_geometry import _coordinates
from normal_orbit_research import seeds
from normal_orbit_research.fixtures import regina_triangulation,regina_surface
from primitive_power_research import forests
ROOT=Path(__file__).resolve().parents[1]
BASELINE='a6947e39a6e9520ecdf3c179795f1624d2976a81'
PREVIOUS=ROOT.parent/'synthesis/data/cocycle-planar-audit.json'
SURVEY=ROOT.parent/'synthesis/data/cocycle-planar-survey.json'


def baseline():
    path='Topology/UnknotRecognition/fast/fastunknot/normal_seed.py'
    source=subprocess.check_output(['git','show',BASELINE+':'+path],cwd=ROOT)
    module=ModuleType('_cocycle_reuse_baseline');module.__package__='fastunknot';sys.modules[module.__name__]=module
    exec(compile(source,BASELINE+':'+path,'exec'),module.__dict__)
    return module.normal_seed_decide,sha256(source).hexdigest()


def pins():
    result=seeds.sources()
    for p in (PREVIOUS,SURVEY):result[str(p.relative_to(ROOT.parent))]=sha256(p.read_bytes()).hexdigest()
    return result


def compact(d,r):
    if r['status']=='UNKNOT':
        proof=r.pop('certificate');assert verify_normal_seed_certificate(d,proof)
        r.update(certificate_sha256=seeds.digest(proof),schema=proof['schema'])
    return r


def audit(old):
    records=[]
    for entry in json.loads(PREVIOUS.read_text())['source_cases']:
        source=entry['source'];d=Diagram.from_pd(source['pd']);results={}
        for label,trials in [('default',4),('extended',24)]:
            results[label]={}
            for planar in (False,True):
                arm='on' if planar else 'off';previous=entry['results'][label][arm]
                a=compact(d,old(d,tree_trials=trials,planar=planar));assert a==previous
                b=compact(d,normal_seed_decide(d,tree_trials=trials,planar=planar))
                if 'allowance exhausted' not in a.get('reason',''):
                    assert {k:v for k,v in a.items() if k!='work'}=={k:v for k,v in b.items() if k!='work'},(source['name'],label,arm)
                if b['status']=='UNKNOT':assert source['expected']=='UNKNOT'
                results[label][arm]=dict(old=a,new=b)
        records.append(dict(source=source,results=results));print(source['name'],[(k,v['off']['new']['status'],v['off']['old']['work'],v['off']['new']['work']) for k,v in results.items()],flush=True)
    ordinary=[]
    for source in forests.corpus():
        arms=[]
        for fn in (old,normal_seed_decide):
            with patch('fastunknot.normal_seed.normal_seed_decide',fn):
                r=recognize(Diagram.from_pd(source['pd']),**seeds.COMMON,use_normal_seed=True)
            assert r.status==source['expected'];arms.append(dict(status=r.status,method=r.method,native_attempts=len(list(seeds.native_stages(r.evidence)))))
        ordinary.append(dict(name=source['name'],answers=arms))
    return dict(source_cases=records,ordinary_pipeline=ordinary)


def survey(old):
    records=[]
    for entry in json.loads(SURVEY.read_text())['source_cases']:
        source=entry['source'];raw=diagram_exterior(Diagram.from_pd(source['pd']));seed,p=_rank_one_cocycle_seed_details(raw);tri=regina_triangulation(raw)
        trees=[c for c in cocycle_tree_candidates(raw,seed['heights'],trials=24) if not c['duplicate']]
        choices=[('raw',seed['heights'],seed['coordinates'],None)]+[(f"tree-{c['trial']}",c['heights'],c['coordinates'],None) for c in trees if c['trial']<=4]
        opt=minimize_cocycle_span(seed['vertices'],seed['heights'])['certificate']
        choices += [('optimized',seed['heights'],opt['coordinates'],dict(zip(opt['vertex_ids'],opt['potential'])))]+[(f"tree-{c['trial']}",c['heights'],c['coordinates'],None) for c in trees if c['trial']>4]
        assert len(choices)==len(entry['candidates']);rows=[]
        for (stage,heights,coords,potential),prior in zip(choices,entry['candidates']):
            assert stage==prior['stage'];summary=_height_summary(p,heights,potential=potential)
            a=_coordinates(p,coords,lambda:None);s=regina_surface(tri,coords)
            assert summary['euler_characteristic']==a['euler_characteristic']==int(str(s.eulerChar()))==prior['euler']
            assert summary['normal_pieces']==a['normal_disks']
            assert s.isConnected() and s.isOrientable() and s.countBoundaries()==prior['boundaries']
            rows.append(dict(stage=stage,**summary,boundaries=prior['boundaries']))
        records.append(dict(source=source,candidates=rows));print('survey',source['name'],len(rows),flush=True)
    return dict(source_cases=records)


def benchmark(old,rounds):
    entries={e['source']['name']:e['source'] for e in json.loads(PREVIOUS.read_text())['source_cases']}
    entries['genus-one-miss']=dict(name='genus-one-miss',pd=Diagram.from_braid(2,[1,1,-1]).pd,expected='UNKNOT')
    specs=[('circle-9','circle-9',4,False,0,True),('random-29','random-29',4,False,0,True),
           ('optimized-positive','optimized-positive',4,False,0,True),('random-142','random-142',4,False,0,True),
           ('random-81','random-81',24,False,0,True),('random-1','random-1',24,False,0,True),
           ('planar-positive','optimized-positive',4,True,0,True),('planar-late','random-162',24,True,0,True),
           ('face-positive','random-142',4,False,4,False),('trefoil','trefoil',4,False,0,True),
           ('genus-one-miss','genus-one-miss',4,False,0,True)]
    cases=[(label,(entries[name],trials,planar,face,annulus)) for label,name,trials,planar,face,annulus in specs]
    def run(case,use_old):
        source,trials,planar,face,annulus=case;d=Diagram.from_pd(source['pd'])
        with patch('fastunknot.normal_seed.normal_seed_decide',old if use_old else normal_seed_decide):
            r=recognize(d,**seeds.FORCED,normal_seed_tree_trials=trials,normal_seed_planar=planar,normal_seed_face_roots=face,normal_seed_annulus=annulus)
        native=r.evidence.get('normal_seed',{});proof=native.get('certificate')
        if proof is not None:assert verify_normal_seed_certificate(d,proof)
        complete=r.status in ('UNKNOT','KNOTTED')
        if complete:assert r.status==source['expected']
        return dict(completed=complete,status=r.status,method=r.method,native_status=native.get('status'),native_work=native.get('work'),schema=proof['schema'] if proof else None,certificate_sha256=seeds.digest(proof) if proof else None)
    return seeds.rounds(cases,run,rounds)


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('mode',choices=('audit','survey','recognize'));parser.add_argument('--rounds',type=int,default=5);parser.add_argument('--output',type=Path,required=True);args=parser.parse_args()
    if args.rounds<1:parser.error('rounds must be positive')
    old,baseline_sha=baseline();before=pins();start=time.perf_counter();result=benchmark(old,args.rounds) if args.mode=='recognize' else globals()[args.mode](old)
    assert pins()==before
    result.update(mode=args.mode,source_sha256=before,baseline_commit=BASELINE,baseline_seed_sha256=baseline_sha,elapsed_seconds=time.perf_counter()-start,python=platform.python_version())
    args.output.write_text(json.dumps(seeds.json_safe(result),indent=2)+'\n');print('complete',args.mode,result['elapsed_seconds'],flush=True)

if __name__=='__main__':main()
