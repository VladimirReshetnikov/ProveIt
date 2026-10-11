"""Explicit small chamber inventories and source-certified binary recovery."""
import argparse
from collections import Counter
from contextlib import ExitStack
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import time
from unittest.mock import patch

from fastunknot.normal_prismatic_inventory import normal_prismatic_inventory
from fastunknot.normal_prismatic_inventory_verify import verify_normal_prismatic_inventory
from fastunknot.normal_cut_complement_verify import _reference_chambers
from fastunknot.normal_cut_complement import normal_complement_components
from fastunknot.normal_surface_geometry import _prepare,_coordinates
from normal_orbit_research.fixtures import layered_torus,regina_triangulation,regina_surface
from normal_orbit_research import seeds
ROOT=Path(__file__).resolve().parents[1];DATA=ROOT.parent/'synthesis/data'


def explicit(raw,rows):
    prepared=_prepare(raw,lambda:None);size,pairs=_reference_chambers(prepared,rows,lambda:None)
    marks=set();types=[]
    for t,row in enumerate(rows):
        q=sum(row[4:]);kind=next((j for j in range(3)if row[4+j]),None);start=len(types)
        marks.update((start,start+q));types.extend((t,4+kind)if kind is not None else None for _ in range(q+1))
        for v,count in enumerate(row[:4]):
            if count:marks.add(len(types))
            types.extend((t,v)for _ in range(count))
    parent=list(range(size))
    def find(x):
        while parent[x]!=x:parent[x]=parent[parent[x]];x=parent[x]
        return x
    for a,b,c,d,sign in pairs:
        for x in range(a,b+1):
            image=x+c-a if sign==1 else a+d-x
            left,right=find(x),find(image);parent[right]=left
    groups={}
    for point in range(size):groups.setdefault(find(point),[]).append(point)
    core={find(p)for p in marks};vectors=Counter()
    for root,points in groups.items():
        if root in core:continue
        vector=[0]*(7*len(rows))
        for point in points:
            t,c=types[point];vector[7*t+c]+=1
        vectors[tuple(vector)]+=1
    bases=[]
    for flat,copies in sorted(vectors.items()):
        v=[list(flat[7*i:7*(i+1)])for i in range(len(rows))]
        chi=_coordinates(prepared,v,lambda:None)['euler_characteristic']
        bases.append(dict(coordinates=v,multiplicity=copies,euler_characteristic=chi))
    return dict(core_components=len(core),prismatic_components=len(groups)-len(core),bases=bases),size


def replay(raw,rows,proof):
    disabled=('fastunknot.normal_prismatic_inventory._prism_weights','fastunknot.normal_prismatic_inventory._inventory',
        'fastunknot.normal_cut_complement._chamber_system','fastunknot.weighted_orbits.weighted_orbit_histogram',
        'fastunknot.weighted_orbits.weighted_histogram_from_orbit_certificate','fastunknot.interval_orbits.count_orbits')
    with ExitStack()as stack:
        for name in disabled:stack.enter_context(patch(name,side_effect=AssertionError('producer invoked')))
        assert verify_normal_prismatic_inventory(raw,rows,proof)


def audit():
    bank={r['id']:r['triangulation']for r in json.loads((ROOT.parent/'reports/57/results/discovery_corpus.json').read_text())['records']}
    rows_by_id={(r['id'],r['index']):r['coordinates']for r in json.loads((DATA/'complement-chamber-pilot.json').read_text())['records']}
    pilot=json.loads((DATA/'cut-product-pilot.json').read_text())
    records=[];proofs=[];retained=set();regina_checks=0
    for case in pilot['records']:
        raw=bank[case['id']];rows=[[case['scale']*x for x in row]for row in rows_by_id[case['id'],case['index']]]
        expected,points=explicit(raw,rows)
        r=normal_prismatic_inventory(raw,rows,record_certificate=True)
        assert r['inventory']==expected
        assert expected['core_components']==case['core_components']and expected['prismatic_components']==case['product_components']
        replay(raw,rows,r['certificate'])
        records.append(dict(id=case['id'],index=case['index'],scale=case['scale'],core_components=expected['core_components'],
            prismatic_components=expected['prismatic_components'],bases=len(expected['bases']),
            maximum_weight_runs=r['stats']['maximum_weight_runs'],proof_sha256=sha256(seeds.encode(r['certificate'])).hexdigest()))
        if expected['bases']and case['id']not in retained:
            retained.add(case['id']);proofs.append(dict(id=case['id'],triangulation=raw,coordinates=rows,certificate=r['certificate']))
            tri=regina_triangulation(raw)
            for base in expected['bases']:
                surface=regina_surface(tri,base['coordinates'])
                assert surface.isConnected()and int(str(surface.eulerChar()))==base['euler_characteristic'];regina_checks+=1
    large=[];reused=0
    for t in (1,4,16):
        raw,v=layered_torus(t)
        for bits in (128,500):
            n=1<<bits;rows=[[n*x for x in row]for row in v]
            r=normal_prismatic_inventory(raw,rows,record_certificate=True)
            assert r['inventory']==dict(core_components=1,prismatic_components=n-1,
                bases=[dict(coordinates=v,multiplicity=n-1,euler_characteristic=1)])
            replay(raw,rows,r['certificate'])
            cut=normal_complement_components(raw,rows,record_certificate=True)
            with patch('fastunknot.weighted_orbits.count_orbits',side_effect=AssertionError('new orbit search')):
                reuse=normal_prismatic_inventory(raw,rows,orbit_certificate=cut['certificate']['orbit_certificate'],record_certificate=True)
            assert reuse['inventory']==r['inventory'];replay(raw,rows,reuse['certificate']);reused+=1
            proofs.append(dict(id=f'large/{t}/{bits}',triangulation=raw,coordinates=rows,certificate=r['certificate']))
            large.append(dict(tetrahedra=t,bits=bits,bases=1,maximum_weight_runs=r['stats']['maximum_weight_runs']))
    raw,v=layered_torus(1);n=1<<16384;rows=[[n*x for x in row]for row in v]
    r=normal_prismatic_inventory(raw,rows,record_certificate=True)
    assert r['inventory']['bases']==[dict(coordinates=v,multiplicity=n-1,euler_characteristic=1)]
    replay(raw,rows,json.loads(seeds.encode(r['certificate'])))
    proofs.append(dict(id='large/16384',triangulation=raw,coordinates=rows,certificate=r['certificate']))
    large.append(dict(tetrahedra=1,bits=16384,bases=1,maximum_weight_runs=r['stats']['maximum_weight_runs']))
    for parity in (0,1):
        n=(1<<500)+parity;rows=[[0,0,0,0,0,n,0]]
        r=normal_prismatic_inventory(raw,rows,record_certificate=True)
        expected=[dict(coordinates=[[0,0,0,0,0,1,0]],multiplicity=1,euler_characteristic=0)]if parity==0 else[]
        expected.append(dict(coordinates=[[0,0,0,0,0,2,0]],multiplicity=n//2-(parity==0),euler_characteristic=0))
        assert r['inventory']['bases']==expected
        replay(raw,rows,r['certificate']);proofs.append(dict(id=f'mobius/{parity}',triangulation=raw,coordinates=rows,certificate=r['certificate']))
        large.append(dict(kind='mobius',parity=parity,bits=500,bases=len(expected),maximum_weight_runs=r['stats']['maximum_weight_runs']))
    return dict(records=records,source_proofs=proofs,source_cases=48,supplied_cases=len(records),regina_base_checks=regina_checks,
        large_cases=large,search_free_reused_traces=reused,normal_midsection_instances=sum(r['prismatic_components']for r in records))


def benchmark(rounds):
    def run(n,expanded):
        raw,v=layered_torus(1);rows=[[n*x for x in row]for row in v]
        if expanded:inventory,points=explicit(raw,rows);stats=dict(expanded_points=points)
        else:
            r=normal_prismatic_inventory(raw,rows,record_certificate=True)
            assert verify_normal_prismatic_inventory(raw,rows,r['certificate'])
            inventory=r['inventory'];stats=r['stats']
        assert inventory==dict(core_components=1,prismatic_components=n-1,bases=[dict(coordinates=v,multiplicity=n-1,euler_characteristic=1)])
        wire=seeds.encode(inventory if expanded else r)
        return dict(completed=True,inventory=inventory,stats=stats,result_bytes=len(wire))
    return seeds.rounds([(f'meridians-{n}',n)for n in (16,256,4096,65536)],run,rounds)


def main():
    p=argparse.ArgumentParser();p.add_argument('mode',choices=('audit','benchmark'));p.add_argument('--output',type=Path,required=True)
    p.add_argument('--rounds',type=int,default=5);args=p.parse_args();pins=seeds.sources();start=time.perf_counter()
    result=audit()if args.mode=='audit'else benchmark(args.rounds)
    assert pins==seeds.sources()
    result.update(native_source_sha256=pins,native_runtime_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
        native_seconds=time.perf_counter()-start,pilot_sha256=sha256((DATA/'cut-product-pilot.json').read_bytes()).hexdigest())
    args.output.write_bytes(seeds.encode(result)+b'\n')
    print(json.dumps({k:v for k,v in result.items()if k in ('supplied_cases','source_cases','regina_base_checks','search_free_reused_traces','native_seconds','measured_calls','completed_calls')}))
if __name__=='__main__':main()
