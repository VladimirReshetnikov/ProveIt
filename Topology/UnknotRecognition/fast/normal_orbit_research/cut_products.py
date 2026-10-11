"""Conservative cut core counts and wholly prismatic component certificates."""
from hashlib import sha256
import argparse
from contextlib import ExitStack
from copy import deepcopy
import json
from pathlib import Path
import subprocess
import time
from types import ModuleType
from unittest.mock import patch
from fastunknot.normal_cut_complement import normal_complement_components,_chamber_system,_exceptional_chambers
from fastunknot.normal_cut_complement_verify import verify_normal_complement_certificate
from fastunknot.normal_surface_geometry import _prepare,_coordinates
from normal_orbit_research.fixtures import layered_torus
from normal_orbit_research import seeds
ROOT=Path(__file__).resolve().parents[1];DATA=ROOT.parent/'synthesis/data'
BASE='1aeabfa735c78a30b732405b101009d376d56f18'

def frozen():
    path='Topology/UnknotRecognition/fast/fastunknot/normal_cut_complement.py'
    module=ModuleType('fastunknot._old_cut_products');module.__package__='fastunknot'
    raw=subprocess.check_output(['git','show',BASE+':'+path],cwd=ROOT)
    exec(compile(raw,path,'exec'),module.__dict__)
    return module,sha256(raw).hexdigest()

def replay(raw,rows,proof):
    with ExitStack()as stack:
        for name in ('fastunknot.normal_cut_complement._exceptional_chambers',
            'fastunknot.normal_cut_complement._chamber_system','fastunknot.interval_orbits.count_orbits'):
            stack.enter_context(patch(name,side_effect=AssertionError('producer used')))
        assert verify_normal_complement_certificate(raw,rows,proof)

def audit():
    old,digest=frozen()
    bank={r['id']:r['triangulation']for r in json.loads((ROOT.parent/'reports/57/results/discovery_corpus.json').read_text())['records']}
    vectors={(r['id'],r['index']):r['coordinates']for r in json.loads((DATA/'complement-chamber-pilot.json').read_text())['records']}
    pilot=json.loads((DATA/'cut-product-pilot.json').read_text());records=[];proofs=[];retained=set()
    for case in pilot['records']:
        raw=bank[case['id']];rows=[[case['scale']*x for x in row]for row in vectors[case['id'],case['index']]]
        disabled=normal_complement_components(raw,rows,record_certificate=True)
        assert disabled==old.normal_complement_components(raw,rows,record_certificate=True)
        result=normal_complement_components(raw,rows,classify_prisms=True,record_certificate=True)
        for key in ('cut_components','core_components','prismatic_components'):assert result[key]==(case['product_components']if key=='prismatic_components'else case[key])
        assert result['exceptional_chambers']==case['marked_chambers']<=6*len(rows)
        replay(raw,rows,result['certificate'])
        record=dict(case,cycles=result['cycles'],proof_sha256=sha256(seeds.encode(result['certificate'])).hexdigest())
        records.append(record)
        if result['prismatic_components']and case['id']not in retained:
            retained.add(case['id']);proofs.append(dict(id=case['id'],triangulation=raw,coordinates=rows,certificate=result['certificate']))
    assert len(retained)==48
    prior=json.loads((DATA/'cut-complement-audit.json').read_text())
    for record in prior['source_proofs']:replay(record['triangulation'],record['coordinates'],record['certificate'])
    large=[]
    for t in (1,4,16):
        raw,vector=layered_torus(t)
        for bits in (128,500):
            n=1<<bits;rows=[[n*x for x in row]for row in vector]
            r=normal_complement_components(raw,rows,classify_prisms=True,record_certificate=True)
            assert r['cut_components']==n and r['core_components']==1 and r['prismatic_components']==n-1
            replay(raw,rows,r['certificate']);large.append(dict(tetrahedra=t,bits=bits,cycles=r['cycles'],core_components=1,prismatic_components=n-1))
            proofs.append(dict(id=f'large/{t}/{bits}',triangulation=raw,coordinates=rows,certificate=r['certificate']))
    raw,vector=layered_torus(1);n=1<<16384;rows=[[n*x for x in row]for row in vector]
    r=normal_complement_components(raw,rows,classify_prisms=True,record_certificate=True)
    assert r['core_components']==1 and r['prismatic_components']==n-1
    replay(raw,rows,json.loads(seeds.encode(r['certificate'])))
    large.append(dict(tetrahedra=1,bits=16384,cycles=r['cycles'],core_components=1,prismatic_components=n-1))
    proofs.append(dict(id='large/16384',triangulation=raw,coordinates=rows,certificate=r['certificate']))
    capped=normal_complement_components(raw,rows,classify_prisms=True,record_certificate=True,max_cycles=4)
    assert capped['status']=='INCONCLUSIVE'and 'cut_components'not in capped and 'certificate'not in capped
    return dict(records=records,source_proofs=proofs,large_cases=large,pilot_cases=len(records),
        disabled_exact_cases=len(records),normal_midsections_checked=pilot['normal_midsections_checked'],
        legacy_proofs=len(prior['source_proofs']),source_cases=48,baseline=BASE,baseline_sha256=digest)

def explicit(raw,rows):
    p=_prepare(raw,lambda:None);a=_coordinates(p,rows,lambda:None);size,pairs=_chamber_system(p,a['rows'],lambda:None)
    marks=_exceptional_chambers(a['rows'],lambda:None);parent=list(range(size))
    def find(x):
        while parent[x]!=x:parent[x]=parent[parent[x]];x=parent[x]
        return x
    for pairing in pairs:
        for point in range(pairing.a,pairing.b+1):
            left,right=find(point),find(pairing.image(point));parent[right]=left
    total=len({find(p)for p in range(size)});core=len({find(p)for p in marks})
    return dict(cut_components=total,core_components=core,prismatic_components=total-core,expanded_points=size)

def benchmark(rounds):
    def run(n,use_expansion):
        raw,vector=layered_torus(1);rows=[[n*x for x in row]for row in vector]
        if use_expansion:r=explicit(raw,rows)
        else:
            r=normal_complement_components(raw,rows,classify_prisms=True,record_certificate=True)
            assert verify_normal_complement_certificate(raw,rows,r['certificate'])
        assert r['cut_components']==n and r['core_components']==1 and r['prismatic_components']==n-1
        wire=seeds.encode(r)
        return dict(completed=True,cut_components=n,core_components=1,prismatic_components=n-1,
            result_bytes=len(wire),expanded_points=r.get('expanded_points'),cycles=r.get('cycles'))
    return seeds.rounds([(f'meridians-{n}',n)for n in (16,256,4096,65536)],run,rounds)

def main():
    parser=argparse.ArgumentParser();parser.add_argument('mode',choices=('audit','benchmark'))
    parser.add_argument('--output',type=Path,required=True);parser.add_argument('--rounds',type=int,default=5)
    args=parser.parse_args();pins=seeds.sources();start=time.perf_counter()
    result=audit()if args.mode=='audit'else benchmark(args.rounds)
    assert pins==seeds.sources()
    result.update(native_source_sha256=pins,native_runtime_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
        native_seconds=time.perf_counter()-start,pilot_sha256=sha256((DATA/'cut-product-pilot.json').read_bytes()).hexdigest())
    args.output.write_bytes(seeds.encode(result)+b'\n')
    print(json.dumps({k:v for k,v in result.items()if k in ('native_seconds','pilot_cases','disabled_exact_cases','normal_midsections_checked','legacy_proofs','measured_calls','completed_calls')}))
if __name__=='__main__':main()
