"""Source coverage, boundary controls and timings for primitive annulus caps."""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import platform
import time
from fastunknot import Diagram, recognize
from fastunknot.cocycle_face import cocycle_face_candidates
from fastunknot.cocycle_span import minimize_cocycle_span
from fastunknot.diagram_exterior import diagram_exterior
from fastunknot.normal_cocycle import rank_one_cocycle_seed, local_coordinates
from fastunknot.normal_annulus_verify import inspect_annulus_certificate
from fastunknot.normal_cocycle_verify import inspect_cocycle_certificate
from fastunknot.normal_seed import normal_seed_decide
from fastunknot.normal_seed_verify import verify_normal_seed_certificate
from fastunknot.normal_surface_geometry import _prepare, _coordinates, _arc_system
from fastunknot.normal_component_geometry import boundary_homology_basis, valid_boundary_basis
from normal_orbit_research import seeds, face
from normal_orbit_research.fixtures import regina_triangulation, regina_surface
from primitive_power_research import forests

ROOT=Path(__file__).resolve().parents[1]
PREVIOUS=ROOT.parent/'synthesis/data/cocycle-face-audit.json'
BASELINE='b2d13b5f4a83d5e6ee7fa98baf37092743ffd2c1'


def pins():
    result=seeds.sources()
    result[str(PREVIOUS.relative_to(ROOT.parent))]=sha256(PREVIOUS.read_bytes()).hexdigest()
    return result


def boundary_control(raw,coordinates):
    """Expanded small-fixture control, never used by recognition/replay."""
    prepared=_prepare(raw,lambda:None);analysed=_coordinates(prepared,coordinates,lambda:None)
    size,pairings=_arc_system(prepared,analysed,boundary=True)
    assert size<=100000
    parent=list(range(size))
    def find(x):
        while parent[x]!=x:
            parent[x]=parent[parent[x]];x=parent[x]
        return x
    for pairing in pairings:
        for x in range(pairing.a,pairing.b+1):parent[find(x)]=find(pairing.image(x))
    basis=boundary_homology_basis(prepared)
    assert valid_boundary_basis(prepared,basis)
    weights={};offset=0
    for edge in sorted(prepared['boundary_incidence']):
        for x in range(offset,offset+analysed['weights'][edge]):
            root=find(x);row=weights.setdefault(root,[0,0])
            for i,cycle in enumerate(basis):row[i]^=int(edge in cycle)
        offset+=analysed['weights'][edge]
    return dict(expanded_boundary_points=size,curve_parities=sorted(weights.values()))


def audit():
    entries=json.loads(PREVIOUS.read_text())['source_cases']
    records,proofs,controls=[],{},[]
    policies=[('default',4,0,'default','off'),('extended',24,0,'extended','off'),('face-four',4,4,'default','on')]
    for entry in entries:
        source=entry['source'];diagram=Diagram.from_pd(source['pd']);results={}
        for label,trees,roots,prior_tree,prior_face in policies:
            old=normal_seed_decide(diagram,tree_trials=trees,face_roots=roots,annulus=False)
            new=normal_seed_decide(diagram,tree_trials=trees,face_roots=roots)
            previous=entry['results'][prior_tree][prior_face]
            assert old['status']==previous['status'] and old['work']==previous['work']
            if old['status']=='UNKNOT':
                assert seeds.digest(old['certificate'])==previous['certificate_sha256']
                assert new['status']=='UNKNOT'
                assert verify_normal_seed_certificate(diagram,old['certificate'])
            for result in (old,new):
                if result['status']=='UNKNOT':
                    assert source['expected']=='UNKNOT'
                    certificate=result.pop('certificate');key=seeds.digest(certificate)
                    assert verify_normal_seed_certificate(diagram,certificate)
                    result['certificate_sha256']=key;result['schema']=certificate['schema']
                    if certificate['schema']=='diagram-cocycle-annulus-v1':proofs[key]=certificate
            results[label]=dict(off=old,on=new)
        records.append(dict(source=source,results=results))
        print(source['name'],[(k,v['on']['status'],v['on']['work']) for k,v in results.items()],flush=True)
        if len(source['pd'])>12:continue
        raw=diagram_exterior(diagram);seed=rank_one_cocycle_seed(raw)
        initial=minimize_cocycle_span(seed['vertices'],seed['heights'])['certificate']
        choices=[initial]+[x['certificate'] for x in cocycle_face_candidates(seed['vertices'],seed['heights'],initial,roots=len(initial['vertex_ids']))]
        triangulation=regina_triangulation(raw)
        for c in choices:
            disc=face.proof(diagram,raw,seed,c);summary=inspect_cocycle_certificate(diagram,disc)
            annulus=dict(disc,schema='diagram-cocycle-annulus-v1')
            accepted=inspect_annulus_certificate(diagram,annulus) is not None
            surface=regina_surface(triangulation,c['coordinates'])
            assert surface.isConnected() and surface.isOrientable()
            chi=int(str(surface.eulerChar()));boundaries=surface.countBoundaries()
            assert summary['euler_characteristic']==chi and accepted==(chi==0)
            row=dict(name=source['name'],euler=chi,boundaries=boundaries,annulus_accepted=accepted,
                     certificate_sha256=seeds.digest(annulus))
            if accepted:
                assert source['expected']=='UNKNOT' and boundaries==2
                boundary=boundary_control(raw,c['coordinates'])
                assert sorted(map(bool,map(any,boundary['curve_parities'])))==[False,True]
                row.update(boundary)
            controls.append(row)
    # Raw and later-tree annuli need their own fresh boundary/topology controls.
    positive_controls=[]
    for key,proof in proofs.items():
        diagram=Diagram.from_pd(proof['input_pd']);summary=inspect_annulus_certificate(diagram,proof)
        surface=regina_surface(regina_triangulation(proof['triangulation']),proof['coordinates'])
        assert surface.isConnected() and surface.isOrientable() and surface.eulerChar()==0 and surface.countBoundaries()==2
        boundary=boundary_control(proof['triangulation'],proof['coordinates'])
        assert sorted(any(x) for x in boundary['curve_parities'])==[False,True]
        positive_controls.append(dict(certificate_sha256=key,summary=summary,**boundary))
    diagram=Diagram.from_braid(2,[1,1,1]);raw=diagram_exterior(diagram);seed=rank_one_cocycle_seed(raw)
    heights=[[int(v in (3,7)) for v in row] for row in seed['vertices']]
    coordinates=[local_coordinates(row) for row in heights]
    surface=regina_surface(regina_triangulation(raw),coordinates)
    assert surface.isConnected() and surface.isOrientable() and surface.eulerChar()==0 and surface.countBoundaries()==2
    null=dict(name='trefoil-null-class-annulus',normal_pieces=sum(map(sum,coordinates)),**boundary_control(raw,coordinates))
    negative=dict(schema='diagram-cocycle-annulus-v1',input_pd=[list(r) for r in diagram.pd],triangulation=raw,
                  heights=heights,coordinates=coordinates,span_certificate=None)
    assert not verify_normal_seed_certificate(diagram,negative)
    heights=[[x-int(v==3) for x,v in zip(hs,vs)] for hs,vs in zip(seed['heights'],seed['vertices'])]
    coordinates=[local_coordinates(row) for row in heights]
    surface=regina_surface(regina_triangulation(raw),coordinates)
    components=surface.components()
    assert len(components)==2 and surface.eulerChar()==0
    assert not any(s.eulerChar()==1 and s.isCompressingDisc(True) for s in components)
    disconnected=dict(name='trefoil-primitive-disconnected-euler-zero',components=2,euler=0,compressing_discs=0)
    negative.update(heights=heights,coordinates=coordinates)
    assert not verify_normal_seed_certificate(diagram,negative)
    ordinary=[]
    for source in forests.corpus():
        answers=[]
        for enabled in (False,True):
            result=recognize(Diagram.from_pd(source['pd']),**seeds.COMMON,use_normal_seed=True,normal_seed_annulus=enabled)
            assert result.status==source['expected']
            answers.append(dict(enabled=enabled,status=result.status,method=result.method,native_attempts=len(list(seeds.native_stages(result.evidence)))))
        ordinary.append(dict(name=source['name'],answers=answers))
    return dict(source_cases=records,annulus_proofs=proofs,surface_controls=controls,
                positive_controls=positive_controls,null_annulus_control=null,
                disconnected_control=disconnected,ordinary_pipeline=ordinary)


def benchmark(rounds):
    entries={e['source']['name']:e['source'] for e in json.loads(PREVIOUS.read_text())['source_cases']}
    cases=[(name,(entries[name],trees,roots)) for name,trees,roots in
           [('circle-9',4,0),('optimized-positive',4,0),('random-29',4,0),('random-79',4,0),('random-99',4,0),
            ('random-142',4,0),('random-81',24,0),('random-1',24,0),('random-127',24,0),('trefoil',4,0)]]
    cases.insert(6,('random-142-face-four',(entries['random-142'],4,4)))
    def run(case,off):
        source,trees,roots=case;diagram=Diagram.from_pd(source['pd'])
        result=recognize(diagram,**seeds.FORCED,normal_seed_tree_trials=trees,normal_seed_face_roots=roots,normal_seed_annulus=not off)
        native=result.evidence.get('normal_seed',{});certificate=native.get('certificate')
        if certificate is not None:assert verify_normal_seed_certificate(diagram,certificate)
        complete=result.status in ('UNKNOT','KNOTTED')
        if complete:assert result.status==source['expected']
        return dict(completed=complete,status=result.status,method=result.method,native_status=native.get('status'),native_work=native.get('work'),
                    schema=certificate['schema'] if certificate else None,certificate_sha256=seeds.digest(certificate) if certificate else None)
    return seeds.rounds(cases,run,rounds)


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('mode',choices=('audit','recognize'))
    parser.add_argument('--rounds',type=int,default=5);parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    if args.rounds<1:parser.error('rounds must be positive')
    before=pins();start=time.perf_counter();result=audit() if args.mode=='audit' else benchmark(args.rounds)
    assert pins()==before
    result.update(mode=args.mode,source_sha256=before,baseline_commit=BASELINE,elapsed_seconds=time.perf_counter()-start,python=platform.python_version())
    args.output.write_text(json.dumps(seeds.json_safe(result),indent=2)+'\n');print('complete',args.mode,result['elapsed_seconds'],flush=True)

if __name__=='__main__':main()
