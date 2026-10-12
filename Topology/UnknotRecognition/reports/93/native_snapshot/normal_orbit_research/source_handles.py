"""Audits and complete-task comparisons for source handle cancellations."""
from contextlib import ExitStack
from hashlib import sha256
import json
from pathlib import Path
import random
from time import perf_counter
from unittest.mock import patch

from fastunknot import Diagram, DiagramError, recognize
from fastunknot.diagram_exterior import diagram_exterior
from fastunknot.normal_seed import normal_seed_decide
from fastunknot.normal_seed_verify import verify_normal_seed_certificate
from fastunknot.source_handle_reduction import reduce_source_handles
from fastunknot.source_handle_reduction_verify import verify_source_handle_reduction
from fastunknot.source_handle_disc import verify_handle_disc_certificate
from normal_orbit_research.fixtures import regina_triangulation
from normal_orbit_research import seeds
from primitive_power_research.forests import corpus
from tests.test_normal_components import relabel

ROOT=Path(__file__).resolve().parents[2]

def encode(value):return json.dumps(value,sort_keys=True,separators=(',',':')).encode()


def audit(output):
    pins=seeds.sources();began=perf_counter();bank=json.loads((ROOT/'reports/57/results/discovery_corpus.json').read_text())['records'];rng=random.Random(26101212)
    cases=[(c['id'],c['triangulation'],not c['id'].startswith('finite_'))for c in bank]
    cases.append(('trefoil_sum_s2xs1',json.loads((ROOT/'synthesis/data/handle-reducible-trefoil.json').read_text()),False))
    for c in bank:
        for i in range(3):
            changed,_=relabel(c['triangulation'],[[0]*7 for _ in c['triangulation']['tetrahedra']],rng)
            cases.append((f"{c['id']}/relabel/{i}",changed,not c['id'].startswith('finite_')))
    disabled=('fastunknot.source_handle_reduction.reduce_source_handles','fastunknot.source_handle_reduction._source_handles',
              'fastunknot.normal_parallelity_geometry._parallelity_geometry','fastunknot.normal_parallelity_geometry._edge_links')
    def replay(raw,proof):
        with ExitStack()as stack:
            for name in disabled:stack.enter_context(patch(name,side_effect=AssertionError('producer used')))
            assert verify_source_handle_reduction(raw,proof)
    records=[];proofs=[]
    for name,raw,expected in cases:
        r=reduce_source_handles(raw,record_certificate=True);replay(raw,r['certificate']);oracle=regina_triangulation(raw).hasCompressingDisc()
        assert (r['compressing_disc']is not None)==oracle==expected,name
        records.append(dict(id=name,tetrahedra=len(raw['tetrahedra']),disc=oracle,stats=r['stats'],summary=r['summary'],proof_sha256=sha256(encode(r['certificate'])).hexdigest()))
        if '/relabel/'not in name:proofs.append(dict(id=name,triangulation=raw,certificate=r['certificate']))
    diagrams=[dict(name=c['name'],pd=c['pd'],expected=c['expected'])for c in corpus()]
    diagrams.append(dict(name='empty-circle',pd=[],expected='UNKNOT'))
    for i in range(100):
        strands=rng.randrange(2,5);word=[rng.choice((-1,1))*rng.randrange(1,strands)for _ in range(rng.randrange(1,13))]
        try:d=Diagram.from_braid(strands,word)
        except DiagramError:continue
        reference=recognize(d,seconds=10,max_objects=50000);assert reference.status in ('UNKNOT','KNOTTED')
        diagrams.append(dict(name=f'random/{i}',pd=d.pd,expected=reference.status))
    diagram_records=[]
    for c in diagrams:
        d=Diagram.from_pd(c['pd']);raw=diagram_exterior(d);r=reduce_source_handles(raw,record_certificate=True);replay(raw,r['certificate']);hit=r['compressing_disc']is not None
        if hit:
            assert c['expected']=='UNKNOT',c['name']
            assert regina_triangulation(raw).isSolidTorus()
            proof=dict(schema='diagram-handle-disc-v1',input_pd=[list(row)for row in d.pd],triangulation=raw,handle_certificate=r['certificate'])
            assert verify_handle_disc_certificate(d,proof)
            proofs.append(dict(id='diagram/'+c['name'],diagram_certificate=proof))
        diagram_records.append(dict(source=c,disc=hit,stats=r['stats'],summary=r['summary'],proof_sha256=sha256(encode(r['certificate'])).hexdigest()))
        print('source handle diagram',c['name'],hit,flush=True)
    assert pins==seeds.sources()
    result=dict(native_source_sha256=pins,source_cases=len(records),source_positive=sum(r['disc']for r in records),diagram_cases=len(diagram_records),
        diagram_positive=sum(r['disc']for r in diagram_records),source_records=records,diagram_records=diagram_records,source_proofs=proofs,seconds=perf_counter()-began,
        corpus_sha256=sha256((ROOT/'reports/57/results/discovery_corpus.json').read_bytes()).hexdigest())
    Path(output).write_bytes(encode(result)+b'\n');print(json.dumps({k:result[k]for k in ('source_cases','source_positive','diagram_cases','diagram_positive','seconds')}),flush=True)


def benchmark(output):
    import gc
    from statistics import median
    pins=seeds.sources();rng=random.Random(26101213)
    chosen=[dict(name='two-crossing-circle',pd=Diagram.from_braid(3,[1,-2]).pd),
            dict(name='eight-crossing-circle',pd=Diagram.from_braid(9,list(range(1,9))).pd),
            dict(name='optimized-positive',pd=Diagram.from_braid(4,[-1,2,1,-2,3]).pd)]
    chosen += [c for c in corpus()if c['name']in ('survivor-06','trefoil')]
    samples=[];proofs={};expected={}
    for round_number in range(6):
        tasks=[(c,arm)for c in chosen for arm in ('old','old_control','handles')];rng.shuffle(tasks)
        for c,arm in tasks:
            d=Diagram.from_pd(c['pd']);gc.collect();start=perf_counter()
            r=normal_seed_decide(d,handles=arm=='handles',max_work=None)
            if r['status']=='UNKNOT':assert verify_normal_seed_certificate(d,r['certificate'])
            wire=encode(r);elapsed=perf_counter()-start
            assert expected.setdefault(c['name'],r['status'])==r['status'],(c['name'],arm)
            samples.append(dict(case=c['name'],arm=arm,round=round_number,warmup=round_number==0,seconds=elapsed,status=r['status'],method=r.get('method'),work=r['work'],bytes=len(wire)))
            if r['status']=='UNKNOT':proofs[c['name']+'/'+arm]=r['certificate']
            del r,wire
        print('source handle timing round',round_number,flush=True)
    summary={}
    for c in chosen:
        rows=[r for r in samples if r['case']==c['name']and not r['warmup']]
        def ratio(arm):return median(next(r['seconds']for r in rows if r['arm']=='old'and r['round']==i)/next(r['seconds']for r in rows if r['arm']==arm and r['round']==i)for i in range(1,6))
        summary[c['name']]=dict(paired_old_over_handles=ratio('handles'),identical_control=ratio('old_control'),
            median_seconds={arm:median(r['seconds']for r in rows if r['arm']==arm)for arm in ('old','old_control','handles')})
    assert pins==seeds.sources()
    result=dict(native_source_sha256=pins,samples=samples,summary=summary,source_proofs=proofs,
        timing='Native positive-certificate stage from a PD, including exterior construction, discovery, its internal positive replay, '
               'a second independent public certificate replay, and serialization. Handles mode adds the optional empty-pattern '
               'reduction before the unchanged cocycle fallback. Both modes must return the same status. Five shuffled paired rounds '
               'after warmup and an identical old control. Fixtures and garbage collection excluded; this is not a full portfolio timing.')
    Path(output).write_bytes(encode(result)+b'\n');print(json.dumps(summary,indent=2))


if __name__=='__main__':
    import argparse
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('mode',choices=('audit','benchmark'));parser.add_argument('--output',required=True)
    args=parser.parse_args();(audit if args.mode=='audit'else benchmark)(args.output)
