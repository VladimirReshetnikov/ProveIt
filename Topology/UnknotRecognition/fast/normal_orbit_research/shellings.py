"""Source, topology and complete-recognition controls for boundary shellings."""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import platform
import time
from fastunknot import Diagram,recognize
from fastunknot.diagram_exterior import diagram_exterior
from fastunknot.boundary_shellings import shell_boundary
from fastunknot.boundary_shellings_verify import verify_boundary_shellings
from fastunknot.normal_seed import normal_seed_decide
from fastunknot.normal_seed_verify import verify_normal_seed_certificate
from fastunknot.normal_cocycle import _rank_one_cocycle_seed_details
from fastunknot.cocycle_trees import _prepared_tree_candidates
from fastunknot.cocycle_span import minimize_cocycle_span
from fastunknot.normal_surface_geometry import _coordinates
from normal_orbit_research import seeds
from normal_orbit_research.fixtures import regina_triangulation,regina_surface
from primitive_power_research import forests
ROOT=Path(__file__).resolve().parents[1]
BASELINE='54cce4c8400c33f9a64f062b58665341c047b8cd'
PREVIOUS=ROOT.parent/'synthesis/data/cocycle-reuse-audit.json'


def pins():
    result=seeds.sources();result[str(PREVIOUS.relative_to(ROOT.parent))]=sha256(PREVIOUS.read_bytes()).hexdigest()
    return result


def surface_control(tri,coordinates):
    surface=regina_surface(tri,coordinates)
    assert surface.isConnected() and surface.isOrientable()
    chi=int(str(surface.eulerChar()));boundaries=surface.countBoundaries()
    disc=chi==1 and surface.isCompressingDisc(True)
    if chi==1:assert disc
    return dict(euler=chi,boundaries=boundaries,compressing_disc=bool(disc))


def audit():
    cases=[];proofs={};moves=0;surfaces=0
    for entry in json.loads(PREVIOUS.read_text())['source_cases']:
        source=entry['source'];d=Diagram.from_pd(source['pd']);raw=diagram_exterior(d)
        reduced=shell_boundary(raw);final=reduced['triangulation'];trace=reduced['moves']
        assert verify_boundary_shellings(raw,final,trace)
        tri=regina_triangulation(raw);alive=list(range(tri.size()))
        for t in trace:
            index=alive.index(t);assert tri.shellBoundary(tri.tetrahedron(index));alive.pop(index);moves+=1
        assert tri.isoSig()==regina_triangulation(final).isoSig()
        assert tri.isValid() and tri.isOrientable() and tri.isConnected()
        assert tri.countBoundaryComponents()==1 and tri.boundaryComponent(0).eulerChar()==0
        results={}
        for label,options in [('off',{}),('on',dict(shellings=True)),('planar',dict(shellings=True,planar=True))]:
            r=normal_seed_decide(d,**options)
            if r['status']=='UNKNOT':
                assert source['expected']=='UNKNOT'
                proof=r.pop('certificate');assert verify_normal_seed_certificate(d,proof)
                key=seeds.digest(proof);proofs[key]=proof
                r.update(certificate_sha256=key,schema=proof['schema'])
                inner=proof.get('surface_certificate',proof)
                control=surface_control(regina_triangulation(inner['triangulation']),inner['coordinates']);surfaces+=1
                if inner['schema']=='diagram-cocycle-planar-v1':assert control['euler']+control['boundaries']==2
            else:control=None
            if label=='off':assert r==entry['results']['default']['off']['new'],source['name']
            results[label]=r
            if label!='off':r['regina']=control
        candidates=[]
        if len(source['pd'])<=12:
            seed,p=_rank_one_cocycle_seed_details(final)
            choices=[('raw',seed['coordinates'])]
            choices += [(f"tree-{c['trial']}",c['coordinates']) for c in _prepared_tree_candidates(p,seed['heights'],trials=4,check=lambda:None) if not c['duplicate']]
            opt=minimize_cocycle_span(seed['vertices'],seed['heights'])
            choices.append(('optimized',opt['coordinates']))
            for stage,coordinates in choices:
                a=_coordinates(p,coordinates,lambda:None);control=surface_control(tri,coordinates);surfaces+=1
                assert a['euler_characteristic']==control['euler']
                if control['euler']>=0:assert source['expected']=='UNKNOT'
                candidates.append(dict(stage=stage,normal_pieces=a['normal_disks'],**control))
        cases.append(dict(source=source,reduction=dict(stats=reduced['stats'],moves=trace,
                     triangulation_sha256=seeds.digest(final)),results=results,candidates=candidates))
        print(source['name'],reduced['stats']['initial_tetrahedra'],len(final['tetrahedra']),
              [(k,v['status'],v['work']) for k,v in results.items()],flush=True)
    ordinary=[]
    for source in forests.corpus():
        answers=[]
        for enabled in (False,True):
            r=recognize(Diagram.from_pd(source['pd']),**seeds.COMMON,use_normal_seed=True,normal_seed_shellings=enabled)
            assert r.status==source['expected']
            answers.append(dict(status=r.status,method=r.method,native_attempts=len(list(seeds.native_stages(r.evidence)))))
        ordinary.append(dict(name=source['name'],answers=answers))
    return dict(source_cases=cases,certificates=proofs,regina_shellings=moves,regina_surfaces=surfaces,ordinary_pipeline=ordinary)


def benchmark(rounds):
    entries={e['source']['name']:e['source'] for e in json.loads(PREVIOUS.read_text())['source_cases']}
    entries['genus-one-miss']=dict(name='genus-one-miss',pd=Diagram.from_braid(2,[1,1,-1]).pd,expected='UNKNOT')
    names=['circle-9','random-29','optimized-positive','random-142','random-1','random-25','random-81','random-176','trefoil','genus-one-miss']
    def run(source,off):
        d=Diagram.from_pd(source['pd']);r=recognize(d,**seeds.FORCED,normal_seed_shellings=not off)
        native=r.evidence.get('normal_seed',{});proof=native.get('certificate')
        if proof is not None:assert verify_normal_seed_certificate(d,proof)
        complete=r.status in ('UNKNOT','KNOTTED')
        if complete:assert r.status==source['expected']
        return dict(completed=complete,status=r.status,method=r.method,native_status=native.get('status'),
                    native_work=native.get('work'),schema=proof['schema'] if proof else None,
                    certificate_sha256=seeds.digest(proof) if proof else None)
    result=seeds.rounds([(n,entries[n]) for n in names],run,rounds)
    for row in result['cases']:
        for arm in ('old','old_AA','new','new_AA'):
            signatures=[{k:v for k,v in sample['measurements'][arm].items() if k!='seconds'} for sample in row['samples']+row['warmups']]
            assert all(s==signatures[0] for s in signatures), (row['name'],arm)
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('mode',choices=('audit','recognize'));parser.add_argument('--rounds',type=int,default=5);parser.add_argument('--output',type=Path,required=True);args=parser.parse_args()
    if args.rounds<1:parser.error('rounds must be positive')
    before=pins();start=time.perf_counter();result=audit() if args.mode=='audit' else benchmark(args.rounds)
    assert before==pins()
    result.update(mode=args.mode,source_sha256=before,baseline_commit=BASELINE,elapsed_seconds=time.perf_counter()-start,python=platform.python_version())
    args.output.write_text(json.dumps(seeds.json_safe(result),indent=2)+'\n');print('complete',args.mode,result['elapsed_seconds'],flush=True)

if __name__=='__main__':main()
