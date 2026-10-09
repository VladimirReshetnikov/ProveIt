"""Pinned complete discovery/replay comparisons for source-anchored production."""
import argparse
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path
import platform
import random
from statistics import median
import sys
import tempfile
import time
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT));sys.path.insert(0,str(ROOT/'tests'))
from compressed_word_research import anchored_replay as prior
from fastunknot import Diagram,DiagramError
from fastunknot import compressed_search as current
from fastunknot.group_certificate import verify_group_certificate,GroupLimit
from fastunknot.anchored_projection_verify import replay_compressed_monomial_block
from fastunknot.primitive_projection_verify import verify_compressed_rank_one
from fastunknot.integer_codec import json_safe
BASELINE='339c5359d34be1945ccfa784c4696a527208859e';SEED=261009453
encode=prior.encode


def audit(old,search,group):
    rng=random.Random(SEED);inputs=[dict(name=s['name'],pd=s['pd']) for s in prior.harness.corpus()];records=[];proofs={};replays=0;blocks=0
    for i in range(300):
        strands=rng.randrange(2,7);word=[rng.choice((-1,1))*rng.randrange(1,strands) for _ in range(rng.randrange(1,19))]
        try:d=Diagram.from_braid(strands,word)
        except DiagramError:continue
        inputs.append(dict(name=f'random-{i}',pd=d.pd))
    for n in (5,9,17,33,65):inputs.append(dict(name=f'circle-{n}',pd=Diagram.from_braid(n,list(range(1,n))).pd))
    options=[('default',{}),('projection',dict(primitive_projection=True)),('forest',dict(primitive_forest=True)),
             ('combined',dict(primitive_projection=True,elimination_batch=True)),
             ('combined_forest',dict(primitive_forest=True,elimination_batch=True)),
             ('no_rank_two',dict(primitive_projection=True,primitive_power=False))]
    for source in inputs:
        modes={};d=Diagram.from_pd(source['pd']);od=old.Diagram.from_pd(source['pd'])
        for mode,opts in options:
            found=[];results={}
            for label,engine,diagram in [('old',search,od),('current',current,d)]:
                stats={};limit=False
                try:c=engine.compressed_certificate(diagram,relator_moves=True,max_work=5000000,stats=stats,**opts)
                except (GroupLimit,group.GroupLimit):c=None;limit=True
                found.append(c);key=None
                if c:key=sha256(encode(c)).hexdigest();proofs[key]=c
                results[label]=dict(certificate_sha256=key,limit=limit,stats=stats)
            assert found[0]==found[1],(source['name'],mode)
            if found[1]:
                for compressed in (False,True):
                    assert group.verify_group_certificate(od,found[1],compressed=compressed,max_work=20000000)
                    assert verify_group_certificate(d,found[1],compressed=compressed,max_work=20000000)
                    replays+=2
            blocks+=results['current']['stats'].get('anchored_search_blocks',0);modes[mode]=results
        records.append(dict(source=source,modes=modes))
    capacities=[]
    for shape,rank,bits,forest in [('balanced',32,128,False),('star',32,128,False),('chain',16,512,False),('chain',16,512,True)]:
        results={};reference=None
        for label,engine in [('old',search),('current',current)]:
            a,roots,alive=prior.build(engine.WordArena,shape,rank,bits);initial=len(a.rules)-1;moves=[];terminal={}
            assert engine._search(a,roots,alive,moves,primitive_projection=True,primitive_forest=forest,primitive_terminal=terminal,rank_two_terminal=False)
            payload=(moves,terminal,prior.runs(a,roots),alive)
            if reference is None:reference=payload
            assert payload==reference
            b,rr,ll=prior.build(current.WordArena,shape,rank,bits)
            assert replay_compressed_monomial_block(b,rr,ll,moves)
            assert verify_compressed_rank_one(b,rr,ll,terminal)
            results[label]=dict(initial_nodes=initial,final_nodes=len(a.rules)-1,stats=deepcopy(a.stats),moves=moves,terminal=terminal)
        capacities.append(dict(shape=shape,rank=rank,bits=bits,forest=forest,engines=results))
    return dict(cases=records,certificates=proofs,diagrams=len(records),source_replays=replays,producer_blocks=blocks,
                all_discovered_certificates_identical=True,capacity=capacities)


def benchmark(mode,old,search,group):
    if mode=='pipeline':
        prior.SEED=SEED
        return prior.pipeline(old)
    rng=random.Random(SEED+1);records=[];proofs={};arms=('old','old_AA','current','current_AA')
    if mode=='kernels':
        cases=[dict(name=f'{shape}-{rank}-{bits}'+('-forest' if forest else ''),shape=shape,rank=rank,bits=bits,forest=forest)
               for shape,rank,bits,forest in [('star',4,0,False),('balanced',32,64,False),('star',32,128,False),('chain',16,512,False),('chain',16,512,True)]]
    else:
        cases=[dict(name=f'circle-{n}-'+('forest' if forest else 'projection'),pd=Diagram.from_braid(n,list(range(1,n))).pd,forest=forest)
               for n in (5,17,65,129) for forest in (False,True)]
    for source in cases:
        samples=[];warmups=[];reference=None
        for iteration in range(-1,5):
            order=list(arms);rng.shuffle(order);measurements={}
            for arm in order:
                historical=arm.startswith('old');engine=search if historical else current;begin=time.perf_counter()
                if mode=='kernels':
                    a,roots,alive=prior.build(engine.WordArena,source['shape'],source['rank'],source['bits']);moves=[];terminal={}
                    ok=engine._search(a,roots,alive,moves,primitive_projection=True,primitive_forest=source['forest'],primitive_terminal=terminal,rank_two_terminal=False)
                    b,rr,ll=prior.build(current.WordArena,source['shape'],source['rank'],source['bits'])
                    checked=replay_compressed_monomial_block(b,rr,ll,moves) and verify_compressed_rank_one(b,rr,ll,terminal)
                    elapsed=time.perf_counter()-begin;assert ok and checked
                    payload=(moves,terminal,prior.runs(a,roots));stats=deepcopy(a.stats)
                    extra=dict(final_nodes=len(a.rules)-1,checker_stats=deepcopy(b.stats));c=dict(moves=moves,terminal=terminal)
                else:
                    package=old if historical else sys.modules['fastunknot'];d=package.Diagram.from_pd(source['pd']);stats={}
                    c=engine.compressed_certificate(d,primitive_projection=True,primitive_forest=source['forest'],stats=stats,max_work=20000000)
                    checker=group.verify_group_certificate if historical else verify_group_certificate;verify_stats={}
                    checked=bool(c) and checker(d,c,compressed=True,max_work=20000000,stats=verify_stats)
                    elapsed=time.perf_counter()-begin;assert checked
                    payload=c;extra=dict(checker_stats=verify_stats)
                if reference is None:reference=payload
                assert payload==reference
                key=sha256(encode(c)).hexdigest();proofs[key]=c
                measurements[arm]=dict(seconds=elapsed,completed=True,stats=stats,certificate_sha256=key,**extra)
            (warmups if iteration<0 else samples).append(dict(order=order,measurements=measurements))
        medians={arm:median(s['measurements'][arm]['seconds'] for s in samples) for arm in arms}
        ratios={f'{a}/{b}':median(s['measurements'][a]['seconds']/s['measurements'][b]['seconds'] for s in samples)
                for a,b in (('old','current'),('old','old_AA'),('current','current_AA'))}
        records.append(dict(source=source,samples=samples,warmups=warmups,medians=medians,paired_ratios=ratios));print(source['name'],ratios,flush=True)
    return dict(cases=records,certificates=proofs,measured_calls=len(cases)*20,warmup_calls=len(cases)*4,completed_calls=len(cases)*20,
                scope=('Fresh abstract grammar construction, complete automatic greedy search, independent source-grammar rebuild and complete replay/endpoint; no diagram-derived knot claim.' if mode=='kernels' else
                       'Fresh validated PD, automatic compressed certificate discovery and complete independent source recovery/replay/endpoint.')+
                      ' Five shuffled rounds and both A/A controls. Exact comparisons and certificate serialization outside timers.')


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('mode',choices=('audit','kernels','source','pipeline'));p.add_argument('--output',type=Path,required=True);args=p.parse_args()
    before=prior.sources();prior.harness.BASELINE=BASELINE;begin=time.perf_counter()
    with tempfile.TemporaryDirectory(prefix='unknot-anchored-producer-') as directory:
        old,search,group,hashes=prior.harness.baseline(directory)
        changed={n for n,h in hashes.items() if h!=sha256((ROOT/'fastunknot'/n).read_bytes()).hexdigest()}
        assert changed=={'compressed_search.py','primitive_projection.py','primitive_forest.py'},changed
        assert all(h==sha256((ROOT/'fastunknot'/n).read_bytes()).hexdigest() for n,h in hashes.items() if 'verify' in n or n in ('compressed_group.py','group_certificate.py'))
        result=audit(old,search,group) if args.mode=='audit' else benchmark(args.mode,old,search,group)
    assert before==prior.sources()
    result.update(mode=args.mode,baseline_commit=BASELINE,source_sha256=before,baseline_source_sha256=hashes,
                  source_hashes_unchanged=True,checker_sources_unchanged=True,seconds=time.perf_counter()-begin,
                  seed=SEED,python=platform.python_version(),platform=platform.platform())
    args.output.write_text(json.dumps(json_safe(result),indent=2)+'\n');print('complete',args.mode,result['seconds'],flush=True)


if __name__=='__main__':main()
