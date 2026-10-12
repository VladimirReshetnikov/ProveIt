"""Audit exact Euler optimization on a certified minimum-span face."""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import platform
import time
from fastunknot import Diagram
from fastunknot.diagram_exterior import diagram_exterior
from fastunknot.normal_cocycle import _rank_one_cocycle_seed_details, _Budget, CocycleLimit
from fastunknot.cocycle_span import minimize_cocycle_span
from fastunknot.cocycle_face import cocycle_face_candidates
from fastunknot.cocycle_euler import maximize_cocycle_face_euler, _euler_model
from fastunknot.cocycle_euler_verify import verify_difference_optimum
from fastunknot.normal_surface_geometry import _coordinates
from fastunknot.normal_cocycle_verify import inspect_cocycle_certificate
from fastunknot.normal_seed_verify import verify_normal_seed_certificate
from normal_orbit_research import seeds
from normal_orbit_research.fixtures import regina_triangulation, regina_surface
ROOT=Path(__file__).resolve().parents[1]
BASELINE='3c0817c50e1be9671e62ae288201d0dc0c7cc5b5'
PREVIOUS=ROOT.parent/'synthesis/data/cocycle-reuse-audit.json'
FACE=ROOT.parent/'synthesis/data/cocycle-face-audit.json'


def pins():
    result=seeds.sources()
    for p in (PREVIOUS,FACE):result[str(p.relative_to(ROOT.parent))]=sha256(p.read_bytes()).hexdigest()
    return result


def source_proof(source,raw,seed,certificate):
    return dict(schema='diagram-cocycle-disc-v1',input_pd=[list(row) for row in source['pd']],triangulation=raw,
        heights=seed['heights'],coordinates=certificate['coordinates'],span_certificate=certificate)


def audit():
    prior=json.loads(PREVIOUS.read_text())['source_cases']
    old_faces={r['name']:r['candidates'] for r in json.loads(FACE.read_text())['surface_controls']}
    records=[];proofs={};duals={};regina_count=0;root_comparisons=0
    extra=dict(name='genus-one-miss',pd=Diagram.from_braid(2,[1,1,-1]).pd,expected='UNKNOT')
    for entry in prior+[dict(source=extra)]:
        source=entry['source'];d=Diagram.from_pd(source['pd']);budget=_Budget(lambda:None,2000000)
        record=dict(source=source);phase='exterior'
        try:
            raw=diagram_exterior(d,check=budget.tick);phase='cocycle'
            seed,p=_rank_one_cocycle_seed_details(raw,check=budget.tick);phase='span'
            span=minimize_cocycle_span(seed['vertices'],seed['heights'],check=budget.tick)['certificate'];phase='euler'
            result=maximize_cocycle_face_euler(raw,seed['heights'],span,check=budget.tick)
            phase='independent-replay'
            model=_euler_model(p,seed['heights'],span,budget.tick)
            assert verify_difference_optimum(len(model[4]),model[2],model[3],result['optimality_certificate'],check=budget.tick)
            proof=source_proof(source,raw,seed,result['certificate'])
            summary=inspect_cocycle_certificate(d,proof,check=budget.tick);assert summary is not None
            chi=result['euler_characteristic'];assert summary['euler_characteristic']==chi
            if chi==0:proof['schema']='diagram-cocycle-annulus-v1'
            positive=chi in (0,1)
            if positive:
                assert source['expected']=='UNKNOT' and verify_normal_seed_certificate(d,proof,check=budget.tick)
                proofs[seeds.digest(proof)]=proof
            old=old_faces.get(source['name'])
            if old:
                assert all(chi>=r['summary']['euler_characteristic'] for r in old)
                root_comparisons+=len(old)
            if len(source['pd'])<=12:
                s=regina_surface(regina_triangulation(raw),result['certificate']['coordinates'])
                assert s.isConnected() and s.isOrientable() and int(str(s.eulerChar()))==chi
                assert bool(s.isCompressingDisc(True))==(chi==1)
                regina_count+=1;record['regina_boundaries']=s.countBoundaries()
            # The complete model and dual let the arithmetic optimum be
            # replayed independently of geometry construction or the solver.
            dual=dict(n=len(model[4]),edges=model[2],constraints=model[3],certificate=result['optimality_certificate'])
            dual_hash=seeds.digest(dual);duals[dual_hash]=dual
            record.update(status='COMPLETE',initial_euler=result['initial_euler_characteristic'],
                optimum_euler=chi,disc_count=result['certificate']['disc_count'],
                best_root_euler=max(r['summary']['euler_characteristic'] for r in old) if old else None,
                root_candidates=len(old) if old else 0,weight_sum=result['stats']['weight_sum'],
                minimum_edge_weight=min(row[3] for row in model[2]),stats=result['stats'],
                summary=summary,positive=positive,proof_sha256=seeds.digest(proof),dual_sha256=dual_hash)
            if 'results' in entry:
                record['previous_default_positive']=entry['results']['default']['off']['new']['status']=='UNKNOT'
        except CocycleLimit:
            record.update(status='CAPPED',phase=phase)
        record['total_work']=budget.work;records.append(record)
        print(source['name'],record['status'],record.get('initial_euler'),record.get('optimum_euler'),budget.work,flush=True)
    return dict(source_cases=records,positive_proofs=proofs,arithmetic_duals=duals,
                regina_comparisons=regina_count,previous_root_comparisons=root_comparisons)


def benchmark(rounds):
    entries={r['source']['name']:r['source'] for r in json.loads(PREVIOUS.read_text())['source_cases']}
    names=['trefoil','optimized-positive','random-142','random-19','random-158','kinoshita_terasaka']
    cases=[(name,entries[name]) for name in names]
    def run(source,roots):
        d=Diagram.from_pd(source['pd']);raw=diagram_exterior(d)
        seed,p=_rank_one_cocycle_seed_details(raw)
        span=minimize_cocycle_span(seed['vertices'],seed['heights'])['certificate']
        if roots:
            best=span;chi=_coordinates(p,best['coordinates'],lambda:None)['euler_characteristic']
            count=0
            for row in cocycle_face_candidates(seed['vertices'],seed['heights'],span,roots=len(span['vertex_ids'])):
                count+=1;c=row['certificate'];value=_coordinates(p,c['coordinates'],lambda:None)['euler_characteristic']
                if value>chi:best,chi=c,value
        else:
            result=maximize_cocycle_face_euler(raw,seed['heights'],span)
            best,chi=result['certificate'],result['euler_characteristic'];count=result['stats']['augmentations']
        proof=source_proof(source,raw,seed,best)
        summary=inspect_cocycle_certificate(d,proof);assert summary is not None and summary['euler_characteristic']==chi
        return dict(completed=True,euler_characteristic=chi,disc_count=best['disc_count'],
                    steps=count,proof_sha256=seeds.digest(proof))
    return seeds.rounds(cases,run,rounds)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode',choices=('audit','benchmark'));parser.add_argument('--rounds',type=int,default=5)
    parser.add_argument('--output',type=Path,required=True);args=parser.parse_args()
    if args.rounds<1:parser.error('rounds must be positive')
    before=pins();start=time.perf_counter()
    result=audit() if args.mode=='audit' else benchmark(args.rounds)
    assert pins()==before
    result.update(mode=args.mode,source_sha256=before,baseline_commit=BASELINE,
                  elapsed_seconds=time.perf_counter()-start,python=platform.python_version())
    args.output.write_text(json.dumps(seeds.json_safe(result),indent=2)+'\n')
    print('complete',args.mode,result['elapsed_seconds'],flush=True)
if __name__=='__main__':main()
