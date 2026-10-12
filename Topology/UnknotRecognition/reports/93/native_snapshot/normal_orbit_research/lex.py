"""Source-corpus and complete-portfolio checks for edge-first cocycle search."""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import time
from types import ModuleType

from fastunknot import Diagram,recognize
from fastunknot.integer_codec import json_safe
from fastunknot.diagram_exterior import diagram_exterior
from fastunknot.normal_cocycle import _rank_one_cocycle_seed_details,_Budget,CocycleLimit
from fastunknot.cocycle_span import minimize_cocycle_span
from fastunknot.cocycle_lex import _prepared_minimize_edge_span
from fastunknot.cocycle_lex_verify import inspect_lex_cocycle_certificate
from fastunknot.normal_seed import normal_seed_decide
from fastunknot.normal_seed_verify import verify_normal_seed_certificate
from normal_orbit_research import seeds
from normal_orbit_research.fixtures import regina_triangulation,regina_surface

ROOT=Path(__file__).resolve().parents[1]
CORPUS=ROOT.parent/'synthesis/data/cocycle-reuse-audit.json'
BASELINE='5402cd990d22552336c855a770ff4989d1b78c6a'


def corpus():
    sources=[r['source'] for r in json.loads(CORPUS.read_text())['source_cases']]
    sources.append(dict(name='genus-one-miss',pd=Diagram.from_braid(2,[1,1,-1]).pd,expected='UNKNOT'))
    return sources


def baseline():
    path='Topology/UnknotRecognition/fast/fastunknot/normal_seed.py'
    source=subprocess.check_output(['git','show',BASELINE+':'+path],cwd=ROOT)
    m=ModuleType('_lex_seed_baseline');m.__package__='fastunknot'
    exec(compile(source,BASELINE+':'+path,'exec'),m.__dict__)
    return m.normal_seed_decide,sha256(source).hexdigest()


def pins():
    result=seeds.sources();result[str(CORPUS.relative_to(ROOT.parent))]=sha256(CORPUS.read_bytes()).hexdigest()
    return result


def audit(old):
    rows=[];proofs=[];arithmetic=[];regina_checks=0
    for source in corpus():
        d=Diagram.from_pd(source['pd']);before=old(d)
        assert before==normal_seed_decide(d,edge_span=False)
        after=normal_seed_decide(d,edge_span=True)
        if after['status']=='UNKNOT':
            assert source['expected']=='UNKNOT' and verify_normal_seed_certificate(d,after['certificate'])
        entry=dict(source=source,old_status=before['status'],new_status=after['status'],
            old_work=before['work'],new_work=after['work'],new_stages=after['stages'])
        budget=_Budget(lambda:None,2000000)
        try:
            raw=diagram_exterior(d,check=budget.tick);seed,prepared=_rank_one_cocycle_seed_details(raw,check=budget.tick)
            span=minimize_cocycle_span(seed['vertices'],seed['heights'],check=budget.tick)['certificate']
            selected=_prepared_minimize_edge_span(prepared,seed['heights'],span,budget.tick)
            proof=dict(schema='diagram-cocycle-lex-v1',input_pd=[list(r) for r in d.pd],
                triangulation=raw,heights=seed['heights'],coordinates=selected['coordinates'],optimality_certificate=selected['certificate'])
            summary=inspect_lex_cocycle_certificate(d,proof,check=budget.tick)
            assert summary is not None and summary['euler_characteristic']==selected['euler_characteristic']
            if summary['euler_characteristic']>=0:
                assert source['expected']=='UNKNOT' and verify_normal_seed_certificate(d,proof,check=budget.tick)
                proofs.append(proof)
            if len(source['pd'])<=12:
                s=regina_surface(regina_triangulation(raw),selected['coordinates'])
                assert s.isConnected() and s.isOrientable() and int(str(s.eulerChar()))==summary['euler_characteristic']
                assert s.isCompressingDisc(True)==bool(summary['compressing_discs'])
                regina_checks+=1
            arithmetic.append(dict(triangulation=raw,heights=seed['heights'],certificate=selected['certificate'],
                                   outer_certificate=proof))
            entry.update(arithmetic_status='COMPLETE',euler=summary['euler_characteristic'],
                pieces=summary['normal_pieces'],secondary_network=selected['stats']['secondary_network'],
                selected_stats=selected['stats'],arithmetic_work=budget.work)
        except CocycleLimit:
            entry.update(arithmetic_status='CAPPED',arithmetic_work=budget.work)
        rows.append(entry)
        print(source['name'],entry['old_status'],entry['new_status'],entry['arithmetic_status'],entry.get('euler'),flush=True)
    return dict(source_cases=rows,legacy_exact_comparisons=len(rows),source_proofs=proofs,
                arithmetic_records=arithmetic,regina_checks=regina_checks,
                old_positives=sum(r['old_status']=='UNKNOT' for r in rows),new_positives=sum(r['new_status']=='UNKNOT' for r in rows))


def benchmark(rounds):
    sources={r['name']:r for r in corpus()}
    sources['figure-eight']=dict(name='figure-eight',pd=Diagram.from_braid(3,[1,-2,1,-2]).pd,expected='KNOTTED')
    selected=['empty-circle','optimized-positive','random-22','random-112','genus-one-miss','trefoil','figure-eight']
    cases=[('seed/'+name,('seed',sources[name])) for name in selected]
    cases += [('recognition/'+name,('recognition',sources[name])) for name in
              ('optimized-positive','genus-one-miss','trefoil','figure-eight')]
    def run(case,use_old):
        kind,source=case;d=Diagram.from_pd(source['pd'])
        if kind=='seed':
            result=normal_seed_decide(d,edge_span=not use_old)
            if result['status']=='UNKNOT':assert verify_normal_seed_certificate(d,result['certificate'])
            wire=seeds.encode(result)
            return dict(completed=True,status=result['status'],work=result['work'],
                result_sha256=sha256(wire).hexdigest(),result_bytes=len(wire))
        result=recognize(d,**dict(seeds.FORCED,normal_seed_edge_span=not use_old,seconds=30))
        assert result.status==source['expected']
        wire=seeds.encode(result.evidence)
        return dict(completed=True,status=result.status,method=result.method,
                    evidence_sha256=sha256(wire).hexdigest(),evidence_bytes=len(wire))
    result=seeds.rounds(cases,run,rounds)
    for row in result['cases']:
        values=[v for s in row['samples']+row['warmups'] for v in s['measurements'].values()]
        assert all(v['completed'] for v in values)
        # Recognition evidence has elapsed-time fields, unlike deterministic seed proofs.
        if row['name'].startswith('seed/'):
            for arm in ('old','new'):
                values=[{k:v for k,v in s['measurements'][a].items() if k!='seconds'}
                    for s in row['samples']+row['warmups'] for a in (arm,arm+'_AA')]
                assert all(v==values[0] for v in values)
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('mode',choices=('audit','benchmark'))
    parser.add_argument('--output',type=Path,required=True);parser.add_argument('--rounds',type=int,default=5)
    args=parser.parse_args();old,h=baseline();before=pins();started=time.perf_counter()
    result=audit(old) if args.mode=='audit' else benchmark(args.rounds)
    assert before==pins();result.update(source_sha256=before,baseline=BASELINE,baseline_source_sha256=h,
                                       seconds=time.perf_counter()-started)
    args.output.write_text(json.dumps(json_safe(result),indent=2)+'\n')
    print('complete',args.mode,result['seconds'],flush=True)


if __name__=='__main__':main()
