"""Audit and measure bounded searches of a certified minimum-span face."""
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
from fastunknot.normal_cocycle import rank_one_cocycle_seed
from fastunknot.normal_cocycle_verify import inspect_cocycle_certificate
from fastunknot.normal_seed import normal_seed_decide
from fastunknot.normal_seed_verify import verify_normal_seed_certificate
from normal_orbit_research import seeds
from normal_orbit_research.fixtures import regina_triangulation, regina_surface
from primitive_power_research import forests

ROOT = Path(__file__).resolve().parents[1]
PREVIOUS = ROOT.parent/'synthesis/data/cocycle-blocking-audit.json'
BASELINE = 'a8658ec40a368c3b4938115e45b3a4e16ac8a19e'


def pins():
    result = seeds.sources()
    result[str(PREVIOUS.relative_to(ROOT.parent))] = sha256(PREVIOUS.read_bytes()).hexdigest()
    return result


def proof(diagram, raw, seed, certificate):
    return dict(schema='diagram-cocycle-disc-v1', input_pd=[list(r) for r in diagram.pd],
                triangulation=raw, heights=seed['heights'], coordinates=certificate['coordinates'],
                span_certificate=certificate)


def audit():
    entries = json.loads(PREVIOUS.read_text())['source_cases']
    records, surfaces, proofs, counterexamples = [], [], {}, {}
    for entry in entries:
        source = entry['source']; diagram = Diagram.from_pd(source['pd']); outcomes = {}
        for policy, trials in [('default',4),('extended',24)]:
            old = normal_seed_decide(diagram,tree_trials=trials,face_roots=0)
            new = normal_seed_decide(diagram,tree_trials=trials,face_roots=4)
            prior = entry['results'][policy]
            assert old['status']==prior['status'] and old['work']==prior['work']
            if old['status']=='UNKNOT':
                assert seeds.digest(old['certificate'])==prior['certificate_sha256']
                assert old['certificate']==new['certificate'] and old['work']==new['work']
            for result in (old,new):
                if result['status']=='UNKNOT':
                    assert source['expected']=='UNKNOT'
                    assert verify_normal_seed_certificate(diagram,result['certificate'])
                    certificate=result.pop('certificate');key=seeds.digest(certificate)
                    result['certificate_sha256']=key
                    if old['status']!='UNKNOT': proofs[key]=certificate
            outcomes[policy]=dict(off=old,on=new)
        records.append(dict(source=source,results=outcomes))
        print(source['name'],[(k,v['on']['status'],v['on']['work']) for k,v in outcomes.items()],flush=True)
        if len(source['pd'])>12:continue
        raw=diagram_exterior(diagram);seed=rank_one_cocycle_seed(raw)
        certificate=minimize_cocycle_span(seed['vertices'],seed['heights'])['certificate']
        triangulation=regina_triangulation(raw)
        choices=[dict(root=None,direction=None,root_trial=0,certificate=certificate)]
        choices.extend(cocycle_face_candidates(seed['vertices'],seed['heights'],certificate,roots=len(certificate['vertex_ids'])))
        checked=[]
        for candidate in choices:
            c=candidate['certificate'];full=proof(diagram,raw,seed,c)
            summary=inspect_cocycle_certificate(diagram,full);assert summary is not None
            surface=regina_surface(triangulation,c['coordinates'])
            assert surface.isConnected() and surface.isOrientable()
            assert summary['components']==summary['orientable_components']==1
            assert summary['euler_characteristic']==int(str(surface.eulerChar()))
            disc=int(surface.eulerChar()==1 and surface.isCompressingDisc(True))
            assert summary['compressing_discs']==disc
            checked.append(dict(root=candidate['root'],direction=candidate['direction'],root_trial=candidate['root_trial'],
                                summary=summary,boundaries=surface.countBoundaries(),certificate_sha256=seeds.digest(full)))
            if source['name'] in ('optimized-positive','random-142'):
                counterexamples[seeds.digest(full)]=full
        surfaces.append(dict(name=source['name'],candidates=checked))
    ordinary=[]
    for source in forests.corpus():
        answers=[]
        for roots in (0,4):
            answer=recognize(Diagram.from_pd(source['pd']),**seeds.COMMON,use_normal_seed=True,normal_seed_face_roots=roots)
            assert answer.status==source['expected']
            attempts=len(list(seeds.native_stages(answer.evidence)))
            answers.append(dict(roots=roots,status=answer.status,method=answer.method,native_attempts=attempts))
        ordinary.append(dict(name=source['name'],answers=answers))
    return dict(source_cases=records,surface_controls=surfaces,new_source_proofs=proofs,
                topology_counterexamples=counterexamples,ordinary_pipeline=ordinary)


def benchmark(rounds):
    entries={e['source']['name']:e['source'] for e in json.loads(PREVIOUS.read_text())['source_cases']}
    cases=[(name,(entries[name],trials)) for name,trials in [('circle-9',4),('optimized-positive',4),
           ('random-99',4),('random-81',24),('random-142',4),('trefoil',4)]]
    cases.append(('genus-one-miss',(dict(pd=Diagram.from_braid(2,[1,1,-1]).pd,expected='UNKNOT'),4)))
    def run(case,off):
        source,trials=case;diagram=Diagram.from_pd(source['pd'])
        result=recognize(diagram,**seeds.FORCED,normal_seed_tree_trials=trials,normal_seed_face_roots=0 if off else 4)
        native=result.evidence.get('normal_seed',{});certificate=native.get('certificate')
        if certificate is not None: assert verify_normal_seed_certificate(diagram,certificate)
        complete=result.status in ('UNKNOT','KNOTTED')
        if complete: assert result.status==source['expected']
        return dict(completed=complete,status=result.status,method=result.method,
                    native_status=native.get('status'),native_work=native.get('work'),
                    face_search=native.get('stats',{}).get('face_search'),
                    certificate_sha256=seeds.digest(certificate) if certificate else None)
    return seeds.rounds(cases,run,rounds)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode',choices=('audit','recognize'))
    parser.add_argument('--rounds',type=int,default=5)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    if args.rounds<1:parser.error('rounds must be positive')
    before=pins();start=time.perf_counter()
    result=audit() if args.mode=='audit' else benchmark(args.rounds)
    assert pins()==before
    result.update(mode=args.mode,source_sha256=before,baseline_commit=BASELINE,
                  elapsed_seconds=time.perf_counter()-start,python=platform.python_version())
    args.output.write_text(json.dumps(seeds.json_safe(result),indent=2)+'\n')
    print('complete',args.mode,result['elapsed_seconds'],flush=True)

if __name__=='__main__':main()
