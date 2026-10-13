"""Inside-core prism face connectivity and exact source-labelled interface audits."""
import argparse
from collections import Counter
from contextlib import ExitStack
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import time
from unittest.mock import patch
from fastunknot.normal_prism_interfaces import normal_prism_face_regions
from fastunknot.normal_prism_interfaces_verify import verify_normal_prism_interfaces,_reference_interface_system
from fastunknot.normal_cut_complement import normal_complement_components
from fastunknot.normal_surface_geometry import _prepare,_coordinates
from normal_orbit_research.fixtures import layered_torus
from normal_orbit_research import seeds
ROOT=Path(__file__).resolve().parents[1];DATA=ROOT.parent/'synthesis/data'


def explicit(raw,rows):
    prepared=_prepare(raw,lambda:None);analysed=_coordinates(prepared,rows,lambda:None)
    size,pairs,d,weights,structure=_reference_interface_system(prepared,analysed['rows'],lambda:None)
    parent=list(range(size))
    def find(x):
        while parent[x]!=x:parent[x]=parent[parent[x]];x=parent[x]
        return x
    for a,b,c,e,sign in pairs:
        for x in range(a,b+1):
            image=x+c-a if sign==1 else a+e-x
            left,right=find(x),find(image);parent[right]=left
    values=[[0]*d for _ in range(size)]
    for lo,stop,vector in weights:
        for p in range(lo,stop):
            for j,x in enumerate(vector):values[p][j]+=x
    groups={}
    for p in range(size):
        root=find(p);total=groups.setdefault(root,[0]*d)
        for j,x in enumerate(values[p]):total[j]+=x
    attached=[];free=Counter()
    for w in groups.values():
        ports=[i for i,x in enumerate(w[2:])if x]
        if ports:attached.append(dict(ports=ports,prism_cells=w[0],face_bands=w[1],ribbon_euler_characteristic=w[0]-w[1]))
        else:free[w[0],w[1]]+=1
    attached.sort(key=lambda r:r['ports'])
    structure.update(attached_regions=attached,unattached_profiles=[dict(prism_cells=a,face_bands=b,
        ribbon_euler_characteristic=a-b,multiplicity=m)for (a,b),m in sorted(free.items())],
        face_attached_components=len(attached),unattached_components=sum(free.values()))
    return structure


def replay(raw,rows,proof):
    with ExitStack()as stack:
        for name in ('fastunknot.normal_prism_interfaces._interface_system','fastunknot.normal_prism_interfaces._profiles',
            'fastunknot.weighted_orbits.weighted_orbit_histogram','fastunknot.interval_orbits.count_orbits'):
            stack.enter_context(patch(name,side_effect=AssertionError('producer used')))
        assert verify_normal_prism_interfaces(raw,rows,proof)


def audit():
    bank={r['id']:r['triangulation']for r in json.loads((ROOT.parent/'reports/57/results/discovery_corpus.json').read_text())['records']}
    vectors={(r['id'],r['index']):r['coordinates']for r in json.loads((DATA/'complement-chamber-pilot.json').read_text())['records']}
    pilot=json.loads((DATA/'cut-product-pilot.json').read_text());records=[];proofs=[];retained=set()
    for case in pilot['records']:
        raw=bank[case['id']];rows=[[case['scale']*x for x in row]for row in vectors[case['id'],case['index']]]
        expected=explicit(raw,rows);r=normal_prism_face_regions(raw,rows,record_certificate=True)
        assert r['structure']==expected
        assert expected['unattached_components']==case['product_components']
        replay(raw,rows,r['certificate'])
        records.append(dict(id=case['id'],index=case['index'],scale=case['scale'],
            ports=len(expected['ports']),face_attached_components=expected['face_attached_components'],
            unattached_components=expected['unattached_components'],prism_points=expected['prism_points'],
            maximum_weight_runs=r['stats']['maximum_weight_runs'],proof_sha256=sha256(seeds.encode(r['certificate'])).hexdigest()))
        if expected['ports']and case['id']not in retained:
            retained.add(case['id']);proofs.append(dict(id=case['id'],triangulation=raw,coordinates=rows,certificate=r['certificate']))
    mixed=0
    previous=json.loads((DATA/'cut-complement-audit.json').read_text())
    for source in previous['source_proofs']:
        if '/mixed'not in source['id']:continue
        raw,rows=source['triangulation'],source['coordinates']
        expected=explicit(raw,rows);r=normal_prism_face_regions(raw,rows,record_certificate=True)
        assert r['structure']==expected
        old=normal_complement_components(raw,rows,classify_prisms=True)
        assert expected['unattached_components']==old['prismatic_components']
        replay(raw,rows,r['certificate']);mixed+=1
        records.append(dict(id=source['id'],index=-1,scale=1,ports=len(expected['ports']),
            face_attached_components=expected['face_attached_components'],unattached_components=expected['unattached_components'],
            prism_points=expected['prism_points'],maximum_weight_runs=r['stats']['maximum_weight_runs'],
            proof_sha256=sha256(seeds.encode(r['certificate'])).hexdigest()))
    assert mixed==48
    inside=[];large=[]
    for t in (2,4,8,16):
        raw,v=layered_torus(t);r=normal_prism_face_regions(raw,v,record_certificate=True)
        cut=normal_complement_components(raw,v,classify_prisms=True)
        assert cut['core_components']==1 and cut['prismatic_components']==0 and r['structure']['face_attached_components']>0
        replay(raw,v,r['certificate'])
        inside.append(dict(tetrahedra=t,ports=len(r['structure']['ports']),regions=r['structure']['face_attached_components'],
            prism_points=r['structure']['prism_points'],unattached_components=0))
        proofs.append(dict(id=f'primitive/{t}',triangulation=raw,coordinates=v,certificate=r['certificate']))
    for t in (1,4,16):
        raw,v=layered_torus(t)
        for bits in (128,500):
            n=1<<bits;rows=[[n*x for x in row]for row in v]
            r=normal_prism_face_regions(raw,rows,record_certificate=True)
            assert r['structure']['unattached_components']==n-1
            replay(raw,rows,r['certificate']);proofs.append(dict(id=f'large/{t}/{bits}',triangulation=raw,coordinates=rows,certificate=r['certificate']))
            large.append(dict(tetrahedra=t,bits=bits,ports=len(r['structure']['ports']),regions=r['structure']['face_attached_components'],
                maximum_weight_runs=r['stats']['maximum_weight_runs']))
    raw,v=layered_torus(4);n=1<<16384;rows=[[n*x for x in row]for row in v]
    r=normal_prism_face_regions(raw,rows,record_certificate=True);assert r['structure']['unattached_components']==n-1
    replay(raw,rows,json.loads(seeds.encode(r['certificate'])))
    proofs.append(dict(id='large/16384',triangulation=raw,coordinates=rows,certificate=r['certificate']))
    large.append(dict(tetrahedra=4,bits=16384,ports=len(r['structure']['ports']),regions=r['structure']['face_attached_components'],maximum_weight_runs=r['stats']['maximum_weight_runs']))
    return dict(supplied_cases=len(records),records=records,source_proofs=proofs,inside_core_cases=inside,large_cases=large,
        attached_source_cases=len(retained),mixed_cases=mixed,previous_unattached_counts_preserved=len(records))


def benchmark(rounds):
    def run(case,expand):
        t,n=case;raw,v=layered_torus(t);rows=[[n*x for x in row]for row in v]
        if expand:s=explicit(raw,rows);stats=dict(expanded_points=s['prism_points'])
        else:
            r=normal_prism_face_regions(raw,rows,record_certificate=True)
            assert verify_normal_prism_interfaces(raw,rows,r['certificate']);s=r['structure'];stats=r['stats']
        assert s['unattached_components']==n-1
        wire=seeds.encode(s if expand else r)
        return dict(completed=True,ports=len(s['ports']),attached=s['face_attached_components'],unattached=s['unattached_components'],
            structure_sha256=sha256(seeds.encode(s)).hexdigest(),result_bytes=len(wire),stats=stats)
    return seeds.rounds([(f'layered-{t}-copies-{n}',(t,n))for t,n in ((4,1),(16,1),(4,256),(4,4096))],run,rounds)


def main():
    p=argparse.ArgumentParser();p.add_argument('mode',choices=('audit','benchmark'));p.add_argument('--output',type=Path,required=True)
    p.add_argument('--rounds',type=int,default=5);args=p.parse_args();pins=seeds.sources();start=time.perf_counter()
    r=audit()if args.mode=='audit'else benchmark(args.rounds)
    assert pins==seeds.sources()
    r.update(native_source_sha256=pins,native_runtime_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
        native_seconds=time.perf_counter()-start,pilot_sha256=sha256((DATA/'cut-product-pilot.json').read_bytes()).hexdigest())
    args.output.write_bytes(seeds.encode(r)+b'\n')
    print(json.dumps({k:v for k,v in r.items()if k in ('supplied_cases','attached_source_cases','previous_unattached_counts_preserved','native_seconds','measured_calls','completed_calls')}))
if __name__=='__main__':main()
