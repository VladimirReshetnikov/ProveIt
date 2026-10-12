"""Certified 3-2 escapes and direct one-vertex span optimization experiments."""
import argparse
from collections import defaultdict
from hashlib import sha256
import json
from pathlib import Path
import random
import subprocess
import time
from types import ModuleType
from unittest.mock import patch

from fastunknot import Diagram, recognize
from fastunknot.diagram_exterior import diagram_exterior
from fastunknot.boundary_shellings import shell_boundary
from fastunknot.pachner23 import pachner_23
from fastunknot.pachner23_verify import verify_pachner_23
from fastunknot.pachner32 import pachner_32
from fastunknot.pachner32_verify import verify_pachner_32
from fastunknot.normal_surface_geometry import _prepare, _EDGES
from fastunknot.normal_cocycle import _rank_one_cocycle_seed_details, _height_summary
from fastunknot.cocycle_trees import _prepared_tree_candidates
from fastunknot.cocycle_span import minimize_cocycle_span
from fastunknot.cocycle_span_verify import verify_cocycle_span
from fastunknot.normal_seed import normal_seed_decide
from fastunknot.normal_seed_verify import verify_normal_seed_certificate
from fastunknot.normal_surface_orbits import normal_surface_topology
from fastunknot.normal_surface_verify import verify_normal_surface_certificate
from fastunknot.normal_disk_kernel import normal_compressing_disk_count, verify_normal_disk_count_certificate
from normal_orbit_research import seeds
from normal_orbit_research.fixtures import layered_torus, regina_triangulation, regina_surface

ROOT=Path(__file__).resolve().parents[1]
DATA=ROOT.parent/'synthesis/data'
BASELINE='a6cadc5d6bc05ba09fa037c3279de6e55558ad65'


def old_solver():
    path='Topology/UnknotRecognition/fast/fastunknot/cocycle_span.py'
    source=subprocess.check_output(['git','show',BASELINE+':'+path],cwd=ROOT)
    module=ModuleType('_span_before_one_vertex');module.__package__='fastunknot'
    exec(compile(source,BASELINE+':'+path,'exec'),module.__dict__)
    return module.minimize_cocycle_span,sha256(source).hexdigest()


def obstruction():
    return json.loads((DATA/'coherent-obstruction-certificate.json').read_text())['moves'][-1]['triangulation']


def greedy(raw):
    """First eligible edge in local incidence order; tetrahedra strictly decrease."""
    moves=[]
    while True:
        p=_prepare(raw,lambda:None);groups=defaultdict(list)
        for local,root in enumerate(p['edge_roots']):groups[root].append((local//6,*_EDGES[local%6]))
        choices=[group for group in groups.values() if len(group)==3 and len({t for t,a,b in group})==3
                 and all(raw['tetrahedra'][t][f] is not None for t,a,b in group for f in range(4) if f not in (a,b))]
        if not choices:break
        t,a,b=choices[0][0]
        result=pachner_32(raw,t,[a,b]);after=result['triangulation']
        assert verify_pachner_32(raw,after,result['certificate'])
        reference=regina_triangulation(raw)
        local_edge=_EDGES.index((a,b))
        assert reference.pachner(reference.tetrahedron(t).edge(local_edge))
        assert reference.isoSig()==regina_triangulation(after).isoSig()
        moves.append(dict(tetrahedron=t,vertices=[a,b],certificate=result['certificate'],
                          output_sha256=seeds.digest(after)))
        raw=after
    return raw,moves


def audit(old):
    rng=random.Random(261009515)
    raw=obstruction();escaped=pachner_32(raw,5,[0,1]);after=escaped['triangulation']
    assert verify_pachner_32(raw,after,escaped['certificate'])
    seed,p=_rank_one_cocycle_seed_details(after)
    disc=normal_compressing_disk_count(after,seed['coordinates'],record_certificate=True)
    assert disc['compressing_disk_components']==1
    assert verify_normal_disk_count_certificate(after,seed['coordinates'],disc['certificate'])
    escape=dict(before=raw,replacement=escaped,coordinates=seed['coordinates'],disc_certificate=disc['certificate'])
    move_records=[]
    fixtures=[layered_torus(n)[0] for n in (2,8)]
    fixtures += [diagram_exterior(Diagram.from_braid(2,w)) for w in ([1],[1,1,1])]
    for initial in fixtures:
        raw=initial
        for step in range(100):
            reference=regina_triangulation(raw)
            up=[f.index() for f in reference.triangles() if reference.hasPachner(f)]
            down=[e.index() for e in reference.edges() if reference.hasPachner(e)]
            use_down=bool(down) and (len(raw['tetrahedra'])>len(initial['tetrahedra'])+10 or rng.randrange(2))
            if use_down:
                site=rng.choice(down);face=reference.edge(site);emb=face.embedding(0);perm=emb.vertices()
                t=emb.tetrahedron().index();vs=[perm[0],perm[1]]
                result=pachner_32(raw,t,vs)
                assert verify_pachner_32(raw,result['triangulation'],result['certificate'])
            else:
                site=rng.choice(up);face=reference.triangle(site);emb=face.embedding(0)
                result=pachner_23(raw,emb.tetrahedron().index(),emb.face())
                assert verify_pachner_23(raw,result['triangulation'],result['certificate'])
            assert reference.pachner(face)
            raw=result['triangulation'];signature=regina_triangulation(raw).isoSig()
            assert signature==reference.isoSig()
            move_records.append(dict(initial_tetrahedra=len(initial['tetrahedra']),step=step,
                                     certificate=result['certificate'],output_iso_signature=signature))
    arithmetic=[]
    for one in (False,True):
        for _ in range(300):
            n=rng.randrange(2,25)
            vs=[[rng.randrange(4) if not one else 71 for _ in range(4)] for _ in range(n)]
            if not one:vs[0]=[0,1,2,3]
            hs=[[rng.randrange(-100,101) for _ in range(4)] for _ in range(n)]
            a,b=old(vs,hs),minimize_cocycle_span(vs,hs)
            assert a['coordinates']==b['coordinates'] if one else a==b
            assert verify_cocycle_span(vs,hs,a['certificate']) and verify_cocycle_span(vs,hs,b['certificate'])
            arithmetic.append(dict(one_vertex=one,tetrahedra=n,old=a['stats'],new=b['stats']))
    previous=json.loads((DATA/'boundary-shellings-audit.json').read_text());source_records=[];proofs=set()
    for entry in previous['source_cases']:
        source=entry['source'];d=Diagram.from_pd(source['pd']);answers={}
        for arm,options in [('off',{}),('on',dict(shellings=True)),('planar',dict(shellings=True,planar=True))]:
            answer=normal_seed_decide(d,**options)
            if answer['status']=='UNKNOT':
                proof=answer.pop('certificate');assert verify_normal_seed_certificate(d,proof)
                digest=seeds.digest(proof);assert proof==previous['certificates'][digest];proofs.add(digest)
                answer.update(certificate_sha256=digest,schema=proof['schema'])
            assert answer=={k:v for k,v in entry['results'][arm].items() if k!='regina'},(source['name'],arm)
            answers[arm]=answer
        source_records.append(dict(source=source,results=answers))
        print(source['name'],'native records preserved',flush=True)
    corpus=json.loads((DATA/'cocycle-reuse-audit.json').read_text());search=[]
    for entry in corpus['source_cases']:
        source=entry['source']
        if len(source['pd'])>16:continue
        for shellings in (False,True):
            raw=diagram_exterior(Diagram.from_pd(source['pd']))
            if shellings:raw=shell_boundary(raw)['triangulation']
            initial_count=len(raw['tetrahedra']);raw,moves=greedy(raw)
            seed,p=_rank_one_cocycle_seed_details(raw)
            candidates=[dict(heights=seed['heights'],coordinates=seed['coordinates'])]
            candidates.extend(c for c in _prepared_tree_candidates(p,seed['heights'],trials=4,check=lambda:None) if not c['duplicate'])
            summaries=[_height_summary(p,c['heights']) for c in candidates]
            best=max(range(len(candidates)),key=lambda j:summaries[j]['euler_characteristic'])
            chi=summaries[best]['euler_characteristic']
            if chi>=0:
                tri=regina_triangulation(raw);surface=regina_surface(tri,candidates[best]['coordinates'])
                assert source['expected']=='UNKNOT' and surface.isConnected() and surface.isOrientable()
                assert int(str(surface.eulerChar()))==chi
                if chi==1:assert surface.isCompressingDisc(True)
            search.append(dict(source=source,shellings=shellings,initial_tetrahedra=initial_count,
                               remaining_tetrahedra=len(raw['tetrahedra']),moves=moves,best=summaries[best],
                               new_over_extended_planar=chi>=0 and entry['results']['extended']['on']['new']['status']!='UNKNOT'))
    return dict(escape=escape,mixed_moves=move_records,arithmetic=arithmetic,
                preserved_source_cases=source_records,preserved_positive_proofs=sorted(proofs),greedy_search=search)


def benchmark(old,count):
    # Construct inputs outside all timed calls. The pipeline arm below repeats
    # cocycle extraction, optimization, topology production and both replays.
    cases=[]
    for n in (16,64,256,1024):
        cases.append((f'distinct-spans-{n}',dict(vertices=[[0]*4 for _ in range(n)],heights=[[0,0,0,i] for i in range(n)])))
    for n in (16,64,256):
        raw,_=layered_torus(n)
        cases.append((f'layered-{n}',dict(triangulation=raw)))
    cases.append(('genus-two-miss',dict(triangulation=obstruction())))
    cases.append(('escaped-disc',dict(triangulation=pachner_32(obstruction(),5,[0,1])['triangulation'])))
    for crossings in (1,4):
        cases.append((f'canonical-control-{crossings}',dict(triangulation=diagram_exterior(Diagram.from_braid(crossings+1,list(range(1,crossings+1)))))))
    for name,strands,word,expected in [('recognize-disc',3,[1,2],'UNKNOT'),
                                      ('recognize-miss',2,[1,1,-1],'UNKNOT'),
                                      ('recognize-trefoil',2,[1,1,1],'KNOTTED')]:
        cases.append((name,dict(diagram=Diagram.from_braid(strands,word),expected=expected)))
    def run(case,use_old):
        solver=old if use_old else minimize_cocycle_span
        if 'diagram' in case:
            d=case['diagram']
            with patch('fastunknot.normal_seed.minimize_cocycle_span',solver):
                answer=recognize(d,**seeds.FORCED)
                native=answer.evidence.get('normal_seed',{});proof=native.get('certificate')
                if proof is not None:assert verify_normal_seed_certificate(d,proof)
            complete=answer.status in ('UNKNOT','KNOTTED')
            if complete:assert answer.status==case['expected']
            return dict(completed=complete,status=answer.status,method=answer.method,
                        native_status=native.get('status'),native_work=native.get('work'),
                        certificate_sha256=seeds.digest(proof) if proof else None)
        if 'triangulation' in case:
            raw=case['triangulation'];seed,p=_rank_one_cocycle_seed_details(raw)
            vs,hs=seed['vertices'],seed['heights']
        else:vs,hs=case['vertices'],case['heights']
        result=solver(vs,hs)
        assert verify_cocycle_span(vs,hs,result['certificate'])
        record=dict(completed=True,stats=result['stats'],coordinates_sha256=seeds.digest(result['coordinates']),
                    certificate_sha256=seeds.digest(result['certificate']))
        if 'triangulation' in case:
            surface=normal_surface_topology(raw,result['coordinates'],record_certificate=True)
            assert verify_normal_surface_certificate(raw,result['coordinates'],surface['certificate'])
            record['topology']={k:surface.get(k) for k in ('components','genus','euler_characteristic','normal_disks','compressing_disk')}
        return record
    return seeds.rounds(cases,run,count)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode',choices=('audit','benchmark'))
    parser.add_argument('--rounds',type=int,default=5)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args();old,digest=old_solver();start=time.perf_counter()
    if args.rounds<1:parser.error('rounds must be positive')
    result=audit(old) if args.mode=='audit' else benchmark(old,args.rounds)
    result.update(baseline=BASELINE,baseline_solver_sha256=digest,seconds=time.perf_counter()-start)
    pins=seeds.sources()
    for path in [Path(__file__),ROOT/'normal_orbit_research/fixtures.py',ROOT/'normal_orbit_research/seeds.py',
                 DATA/'coherent-obstruction-certificate.json',DATA/'cocycle-reuse-audit.json',DATA/'boundary-shellings-audit.json']:
        pins[str(path.relative_to(ROOT.parent))]=sha256(path.read_bytes()).hexdigest()
    result['source_sha256']=pins
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print('completed',args.mode,'seconds',result['seconds'],flush=True)


if __name__=='__main__':main()
