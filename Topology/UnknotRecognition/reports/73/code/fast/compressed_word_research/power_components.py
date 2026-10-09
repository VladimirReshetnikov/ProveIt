"""Pinned plain-power component audit and complete-operation measurements."""
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
from fastunknot.power_component_verify import replay_compressed_power_components,replay_literal_power_components
from fastunknot.primitive_projection_verify import verify_compressed_rank_one
from fastunknot.integer_codec import json_safe
from test_power_component import family,source_certificate
BASELINE='8be43faf3e732e967a728388daac68b14226217f';SEED=261009457
encode=prior.encode


def audit(old,search,group):
    rng=random.Random(SEED);inputs=[dict(name=s['name'],pd=s['pd']) for s in prior.harness.corpus()];cases=[];proofs={};replays=0
    for i in range(240):
        strands=rng.randrange(2,6);word=[rng.choice((-1,1))*rng.randrange(1,strands) for _ in range(rng.randrange(1,15))]
        try:d=Diagram.from_braid(strands,word)
        except DiagramError:continue
        inputs.append(dict(name=f'random-{i}',pd=d.pd))
    for n in (5,9,17,33):inputs.append(dict(name=f'circle-{n}',pd=Diagram.from_braid(n,list(range(1,n))).pd))
    identical=True;activations=0
    for source in inputs:
        d=Diagram.from_pd(source['pd']);od=old.Diagram.from_pd(source['pd']);modes={}
        for mode,opts in [('default',{}),('projection',dict(primitive_projection=True)),('forest',dict(primitive_forest=True))]:
            results={};found=[]
            for label,engine,diagram in [('old',search,od),('current',current,d)]:
                stats={};limited=False
                try:c=engine.compressed_certificate(diagram,relator_moves=True,max_work=2000000,stats=stats,**opts)
                except (GroupLimit,group.GroupLimit):c=None;limited=True
                found.append(c);key=None
                if c:key=sha256(encode(c)).hexdigest();proofs[key]=c
                results[label]=dict(certificate_sha256=key,limited=limited,stats=stats)
            identical &= found[0]==found[1]
            if found[1]:
                for compressed in (False,True):
                    assert verify_group_certificate(d,found[1],compressed=compressed,max_work=20000000);replays+=1
                    if found[1]['version']<=9:
                        assert group.verify_group_certificate(od,found[1],compressed=compressed,max_work=20000000);replays+=1
                activations+=sum(m['kind']=='power_component_delete' for m in found[1]['moves'])
            if found[0]:assert found[1] is not None,(source['name'],mode,'lost positive')
            modes[mode]=results
        cases.append(dict(source=source,modes=modes))
    exposed=[]
    for n in (5,9,17):
        d,c=source_certificate(n);key=sha256(encode(c)).hexdigest();proofs[key]=c
        for compressed in (False,True):
            assert verify_group_certificate(d,c,compressed=compressed,max_work=20000000);replays+=1
            assert not group.verify_group_certificate(old.Diagram.from_pd(d.pd),c,compressed=compressed)
        exposed.append(dict(strands=n,pd=d.pd,certificate_sha256=key,automatic_exposure=False))
    # Two independent product-difference-one cycles share only a free label.
    words=[]
    for base in (2,5):
        for i in range(3):words.append([base+i]*5+[-(base+(i+1)%3)]*(31 if i==2 else 2))
    a=current.WordArena();roots=[a.from_word(w) for w in words];alive=set(range(1,8));moves=[];terminal={}
    assert current._search(a,roots,alive,moves,primitive_projection=True,primitive_terminal=terminal)
    assert len(moves)==1 and len(moves[0]['components'])==2
    b=current.WordArena();rr=[b.from_word(w) for w in words];ll=set(range(1,8))
    assert replay_compressed_power_components(b,rr,ll,moves[0]) and ll=={1} and not any(rr)
    literal=deepcopy(words);la=set(range(1,8))
    assert replay_literal_power_components(literal,la,moves[0],current._Budget(lambda:None,1000000,1000000))
    assert la=={1} and not any(literal)
    multi_component=dict(words=words,moves=moves,terminal=terminal,stats=deepcopy(a.stats))
    capacities=[]
    for n,bits in ((3,64),(8,64),(16,128),(32,128)):
        results={}
        for label,engine in [('old',search),('current',current)]:
            a,roots,alive=family(n,bits,engine.WordArena);moves=[];terminal={}
            ok=engine._search(a,roots,alive,moves,primitive_projection=True,primitive_terminal=terminal)
            if label=='current':
                assert ok and len(moves)==1 and moves[0]['kind']=='power_component_delete'
                b,rr,ll=family(n,bits)
                assert replay_compressed_power_components(b,rr,ll,moves[0]) and verify_compressed_rank_one(b,rr,ll,terminal)
            results[label]=dict(algebraic_search_success=ok,stats=deepcopy(a.stats),nodes=len(a.rules)-1,moves=moves,terminal=terminal)
        capacities.append(dict(rank=n,bits=bits,engines=results))
    return dict(cases=cases,certificates=proofs,diagrams=len(cases),source_replays=replays,
                all_ordinary_discovered_certificates_identical=identical,automatic_component_moves=activations,
                exposed_cases=exposed,capacity=capacities,multi_component=multi_component)


def benchmark(mode,old):
    if mode=='pipeline':prior.SEED=SEED;return prior.pipeline(old)
    rng=random.Random(SEED+1);cases=[];proofs={}
    inputs=([dict(name=f'cycle-{n}-{bits}',rank=n,bits=bits) for n,bits in ((3,64),(8,64),(16,128),(32,128))]
            if mode=='stages' else [dict(name=f'exposed-circle-{n}',strands=n) for n in (5,9,17)])
    for source in inputs:
        samples=[];warmups=[];reference=None
        for iteration in range(-1,5):
            order=['current','current_AA'];rng.shuffle(order);measurements={}
            for arm in order:
                begin=time.perf_counter()
                if mode=='stages':
                    a,roots,alive=family(source['rank'],source['bits']);moves=[];terminal={}
                    assert current._search(a,roots,alive,moves,primitive_projection=True,primitive_terminal=terminal)
                    b,rr,ll=family(source['rank'],source['bits'])
                    assert replay_compressed_power_components(b,rr,ll,moves[0]) and verify_compressed_rank_one(b,rr,ll,terminal)
                    elapsed=time.perf_counter()-begin;c=dict(moves=moves,terminal=terminal);stats=deepcopy(a.stats);extra=dict(nodes=len(a.rules)-1,checker_stats=deepcopy(b.stats))
                else:
                    d,c=source_certificate(source['strands']);stats={}
                    assert verify_group_certificate(d,c,compressed=True,max_work=20000000,stats=stats)
                    elapsed=time.perf_counter()-begin;extra={}
                key=sha256(encode(c)).hexdigest();proofs[key]=c
                if reference is None:reference=key
                assert key==reference
                measurements[arm]=dict(seconds=elapsed,completed=True,certificate_sha256=key,stats=stats,**extra)
            (warmups if iteration<0 else samples).append(dict(order=order,measurements=measurements))
        medians={arm:median(s['measurements'][arm]['seconds'] for s in samples) for arm in ('current','current_AA')}
        ratio=median(s['measurements']['current']['seconds']/s['measurements']['current_AA']['seconds'] for s in samples)
        cases.append(dict(source=source,samples=samples,warmups=warmups,medians=medians,paired_AA=ratio));print(source['name'],medians,ratio,flush=True)
    return dict(cases=cases,certificates=proofs,measured_calls=len(cases)*10,warmup_calls=len(cases)*2,completed_calls=len(cases)*10,
                scope=('Fresh binary source grammar, full automatic algebraic search and independently rebuilt source replay through the endpoint. Isolated presentations are unconditionally Z by product difference one; no PD provenance claim.' if mode=='stages' else
                       'Fresh PD, presentation recovery, supplied Whitehead exposure, automatic graph discovery and complete independent PD-bound replay. Exposure choice is supplied.')+
                      ' Five shuffled A/A rounds; no speed ratio against the predecessor, which does not support the new inference.')


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('mode',choices=('audit','stages','source','pipeline'));p.add_argument('--output',type=Path,required=True);args=p.parse_args()
    before=prior.sources();prior.harness.BASELINE=BASELINE;begin=time.perf_counter()
    with tempfile.TemporaryDirectory(prefix='unknot-power-components-') as directory:
        old,search,group,hashes=prior.harness.baseline(directory)
        changed={n for n,h in hashes.items() if h!=sha256((ROOT/'fastunknot'/n).read_bytes()).hexdigest()}
        assert changed=={'compressed_search.py','power_pair.py','compressed_group.py','group_certificate.py'},changed
        result=audit(old,search,group) if args.mode=='audit' else benchmark(args.mode,old)
    assert before==prior.sources()
    result.update(mode=args.mode,baseline_commit=BASELINE,source_sha256=before,baseline_source_sha256=hashes,
                  source_hashes_unchanged=True,seconds=time.perf_counter()-begin,seed=SEED,python=platform.python_version(),platform=platform.platform())
    args.output.write_text(json.dumps(json_safe(result),indent=2)+'\n');print('complete',args.mode,result['seconds'],flush=True)


if __name__=='__main__':main()
