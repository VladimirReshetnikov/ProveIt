"""Regina cut-open oracle and binary native cut-component experiments."""
import argparse
from contextlib import ExitStack
from hashlib import sha256
import json
from pathlib import Path
import random
import subprocess
import time
from unittest.mock import patch

from fastunknot.normal_cut_complement import normal_complement_components
from fastunknot.normal_cut_complement_verify import verify_normal_complement_certificate
from fastunknot.normal_surface_geometry import _prepare,_coordinates
from normal_orbit_research.fixtures import layered_torus,regina_triangulation,regina_surface
from normal_orbit_research import seeds

ROOT=Path(__file__).resolve().parents[1];DATA=ROOT.parent/'synthesis/data'


def replay(raw,rows,proof):
    disabled=('fastunknot.normal_cut_complement._chamber_system',
        'fastunknot.normal_cut_complement.normal_complement_components','fastunknot.interval_orbits.count_orbits')
    with ExitStack()as stack:
        for name in disabled:stack.enter_context(patch(name,side_effect=AssertionError('producer used')))
        assert verify_normal_complement_certificate(raw,rows,proof)


def audit():
    bank={r['id']:r for r in json.loads((ROOT.parent/'reports/57/results/discovery_corpus.json').read_text())['records']}
    pilot=json.loads((DATA/'complement-chamber-pilot.json').read_text())
    records=[];proofs=[];mixed=[];large=[];rng=random.Random(20261010)
    groups={}
    for row in pilot['records']:groups.setdefault(row['id'],[]).append(row)
    for name,cohort in groups.items():
        raw=bank[name]['triangulation'];tri=regina_triangulation(raw)
        for i,case in enumerate(cohort):
            rows=case['coordinates'];result=normal_complement_components(raw,rows,record_certificate=True)
            replay(raw,rows,result['certificate'])
            cut=regina_surface(tri,rows).cutAlong()
            assert result['cut_components']==cut.countComponents()==case['components']
            assert result['chamber_points']==len(rows)+result['normal_disks']
            assert result['interval_pairings']<=20*len(rows)
            records.append(dict(id=name,index=case['index'],components=result['cut_components'],
                normal_discs=result['normal_disks'],chamber_points=result['chamber_points'],
                interval_pairings=result['interval_pairings'],cycles=result['cycles'],
                proof_sha256=sha256(seeds.encode(result['certificate'])).hexdigest(),cut_tetrahedra=cut.size()))
            if i in (0,len(cohort)-1):proofs.append(dict(id=f'{name}/{i}',triangulation=raw,coordinates=rows,certificate=result['certificate']))
        vertices=[v['coordinates']for v in bank[name]['standard_vertices']if v['normal_discs']<=64]
        link=next(v for v in vertices if not any(x for row in v for x in row[4:]))
        prepared=_prepare(raw,lambda:None);count=0
        for attempt in range(128):
            a,b=rng.choice(vertices),rng.choice(vertices);sa,sb=rng.randrange(1,4),rng.randrange(1,4)
            if attempt%2==0:a,sa,sb=link,1,1
            rows=[[sa*x+sb*y for x,y in zip(left,right)]for left,right in zip(a,b)]
            if sum(sum(row)for row in rows)>128:continue
            if any(sum(bool(x)for x in row[4:])>1 for row in rows):continue
            _coordinates(prepared,rows,lambda:None)
            result=normal_complement_components(raw,rows,record_certificate=True)
            replay(raw,rows,result['certificate'])
            cut=regina_surface(tri,rows).cutAlong();assert result['cut_components']==cut.countComponents()
            mixed.append(dict(id=name,components=result['cut_components'],normal_discs=result['normal_disks'],
                proof_sha256=sha256(seeds.encode(result['certificate'])).hexdigest(),cut_tetrahedra=cut.size()))
            if count==0:proofs.append(dict(id=f'{name}/mixed',triangulation=raw,coordinates=rows,certificate=result['certificate']))
            count+=1
            if count==8:break
        assert count==8,(name,count)
        print(name,len(cohort),count,flush=True)
    for t in (1,4,16):
        raw,vector=layered_torus(t)
        for bits in (0,128,500):
            scale=1<<bits;rows=[[scale*x for x in row]for row in vector]
            result=normal_complement_components(raw,rows,record_certificate=True);assert result['cut_components']==scale
            replay(raw,rows,result['certificate'])
            large.append(dict(kind='parallel-meridian',tetrahedra=t,scale_bits=bits,components=result['cut_components'],
                chamber_points=result['chamber_points'],pairings=result['interval_pairings'],cycles=result['cycles']))
            proofs.append(dict(id=f'large/{t}/{bits}',triangulation=raw,coordinates=rows,certificate=result['certificate']))
    raw,vector=layered_torus(1)
    for kind,vector,scale,expected in (
        ('meridian',vector,1<<16384,1<<16384),
        ('vertex-link',[[1,1,1,1,0,0,0]],1<<500,(1<<500)+1),
        ('mobius-odd',[[0,0,0,0,0,1,0]],(1<<500)+1,(1<<499)+1),
        ('mobius-even',[[0,0,0,0,0,1,0]],1<<500,(1<<499)+1)):
        rows=[[scale*x for x in row]for row in vector]
        result=normal_complement_components(raw,rows,record_certificate=True);assert result['cut_components']==expected
        wire=json.loads(seeds.encode(result['certificate']));replay(raw,rows,wire)
        large.append(dict(kind=kind,tetrahedra=1,scale_bits=scale.bit_length()-1,
            components=expected,chamber_points=result['chamber_points'],pairings=result['interval_pairings'],cycles=result['cycles']))
        proofs.append(dict(id=f'large/{kind}',triangulation=raw,coordinates=rows,certificate=wire))
    return dict(source_cases=len(groups),pilot_surfaces=len(records),mixed_surfaces=len(mixed),
        large_binary_cases=len(large),regina_cut_checks=len(records)+len(mixed),
        records=records,mixed_records=mixed,large_cases=large,source_proofs=proofs)


def benchmark(rounds):
    cases=[(f'meridian-copies-{n}',n)for n in (1,16,128,1024)]
    def run(scale,external):
        raw,vector=layered_torus(1);rows=[[scale*x for x in row]for row in vector]
        if external:
            cut=regina_surface(regina_triangulation(raw),rows).cutAlong()
            count=cut.countComponents();wire=seeds.encode(dict(cut_components=count,cut_tetrahedra=cut.size()))
            assert count==scale
            return dict(completed=True,cut_components=count,cut_tetrahedra=cut.size(),result_bytes=len(wire))
        result=normal_complement_components(raw,rows,record_certificate=True)
        assert result['cut_components']==scale
        assert verify_normal_complement_certificate(raw,rows,result['certificate'])
        wire=seeds.encode(result)
        return dict(completed=True,cut_components=scale,chamber_points=result['chamber_points'],
            interval_pairings=result['interval_pairings'],cycles=result['cycles'],result_bytes=len(wire))
    result=seeds.rounds(cases,run,rounds)
    result['scope']='Exact component-count task: explicit Regina cut and count versus native compressed chambers, independent orbit replay and serialization. The native method does not return the expanded cut triangulation.'
    return result


def main():
    parser=argparse.ArgumentParser();parser.add_argument('mode',choices=('audit','benchmark'))
    parser.add_argument('--output',type=Path,required=True);parser.add_argument('--rounds',type=int,default=5)
    args=parser.parse_args();pins=seeds.sources();start=time.perf_counter()
    result=audit()if args.mode=='audit'else benchmark(args.rounds)
    assert pins==seeds.sources()
    result.update(native_source_sha256=pins,native_seconds=time.perf_counter()-start,
        native_runtime_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True,cwd=ROOT).strip(),
        pilot_sha256=sha256((DATA/'complement-chamber-pilot.json').read_bytes()).hexdigest(),
        corpus_sha256=sha256((ROOT.parent/'reports/57/results/discovery_corpus.json').read_bytes()).hexdigest())
    args.output.write_bytes(seeds.encode(result)+b'\n')
    print(json.dumps({k:v for k,v in result.items()if k in ('native_seconds','source_cases','pilot_surfaces','mixed_surfaces','regina_cut_checks','large_binary_cases','measured_calls','completed_calls')}))

if __name__=='__main__':main()
