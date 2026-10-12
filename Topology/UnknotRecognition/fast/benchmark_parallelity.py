"""Parallelity base topology and core charts: binary proof versus literal polygons."""
from collections import Counter
import argparse
import gc
from hashlib import sha256
import json
from pathlib import Path
import platform
import random
import statistics
from time import perf_counter
from fastunknot.integer_codec import json_safe
from fastunknot.normal_parallelity import normal_cut_parallelity
from fastunknot.normal_parallelity_verify import verify_normal_cut_parallelity
from fastunknot.normal_parallelity_reference import _reference_parallelity
from fastunknot.normal_surface_geometry import _prepare, _coordinates
from normal_orbit_research.fixtures import layered_torus
from normal_orbit_research.parallelity import literal_base
from normal_orbit_research import seeds


def encode(value):return json.dumps(json_safe(value),sort_keys=True,separators=(',',':')).encode()

def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--output',type=Path,required=True);args=parser.parse_args()
    cases={}
    for t,n in ((1,1),(1,16),(1,128),(1,1024),(1,4096),(4,1),(16,1)):
        raw,base=layered_torus(t);cases[f'layered_{t}_copies_{n}']=raw,[[n*x for x in row]for row in base]
    pins=seeds.sources();rng=random.Random(2610129);samples=[];expected={}
    for round_number in range(6):
        tasks=[(name,arm)for name in cases for arm in ('native','literal','literal_control')];rng.shuffle(tasks)
        for name,arm in tasks:
            raw,rows=cases[name];gc.collect();began=perf_counter()
            if arm=='native':
                a=normal_cut_parallelity(raw,rows,record_certificate=True)
                assert verify_normal_cut_parallelity(raw,rows,a['certificate'])
                profiles=Counter()
                for p in a['summary']['base_profiles']:
                    profiles[(p['euler_characteristic'],p['boundary_components'],p['orientable'],*p['handles'],p['original_boundary_edges'],tuple(p['core_ports']))]+=p['multiplicity']
                wire=encode(a);geometry=a['geometry']
            else:
                prepared=_prepare(raw,lambda:None);analysed=_coordinates(prepared,rows,lambda:None)
                geometry=_reference_parallelity(prepared,analysed,lambda:None);b=literal_base(geometry,max_points=1000000)
                profiles=b.pop('profiles');wire=encode(dict(geometry=geometry,profiles=[[list(k),v]for k,v in sorted(profiles.items())],literal=b))
            elapsed=perf_counter()-began
            signature=(profiles,[len(geometry['core'][f'handles{i}'])for i in range(4)])
            assert expected.setdefault(name,signature)==signature
            samples.append(dict(case=name,arm=arm,round=round_number,warmup=round_number==0,seconds=elapsed,result_bytes=len(wire),
                polygon_families=len(geometry['polygons']),physical_polygons=geometry['polygon_points'],completed=True))
            del wire,geometry,profiles
            if arm=='native':del a
            else:del b,prepared,analysed
        print('parallelity timing round',round_number,flush=True)
    assert pins==seeds.sources();summary={}
    for name in cases:
        rows=[r for r in samples if r['case']==name and not r['warmup']]
        def ratio(arm):return statistics.median(next(r['seconds']for r in rows if r['arm']=='literal'and r['round']==i)/next(r['seconds']for r in rows if r['arm']==arm and r['round']==i)for i in range(1,6))
        summary[name]=dict(paired_literal_over_native=ratio('native'),identical_control=ratio('literal_control'),
            median_seconds={arm:statistics.median(r['seconds']for r in rows if r['arm']==arm)for arm in ('native','literal','literal_control')})
    result=dict(native_source_sha256=pins,python=platform.python_version(),seed=2610129,samples=samples,summary=summary,
        timing='Both arms validate source coordinates, construct source parallelity and bounded core charts, classify every base '
               'and serialize their result. Native includes independent source and orbit-proof replay. Literal independently '
               'reconstructs geometry from raw cut incidences and expands polygons, fibre orientation, boundary loops and vertex '
               'links. Formats and proof obligations differ; this compares supplied-surface decomposition tasks, not complete '
               'unknot recognition. Five shuffled paired rounds after warmup, with an identical literal control.')
    args.output.write_bytes(encode(result)+b'\n');print(json.dumps(summary,indent=2))

if __name__=='__main__':main()
