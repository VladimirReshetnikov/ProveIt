"""Pinned source-anchored replay audits and complete-call comparisons."""
import argparse
from copy import deepcopy
from hashlib import sha256
import importlib
import json
from pathlib import Path
import platform
import random
from statistics import median
import sys
import tempfile
import time
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT));sys.path.insert(0,str(ROOT/'tests'))
from primitive_power_research import forests as harness
from compressed_word_research import power_pairs as prior
from fastunknot import Diagram,DiagramError
from fastunknot.compressed_words import WordArena
from fastunknot.compressed_search import compressed_certificate
from fastunknot.group_certificate import verify_group_certificate,GroupLimit
from fastunknot.anchored_projection_verify import replay_compressed_monomial_block
from fastunknot.primitive_projection import plan_projection,apply_projection
from fastunknot.primitive_forest import plan_forest,apply_forest
from fastunknot.primitive_projection_verify import verify_compressed_rank_one
from fastunknot.integer_codec import json_safe
from test_anchored_projection import schedule,setup
BASELINE='b41fc4960968f40f186fb38f2f4fa9e1f4e2630c';SEED=261009449


def sources():return prior.sources()
def encode(value):return json.dumps(json_safe(value),sort_keys=True,separators=(',',':')).encode()


def build(arena_type,shape,rank,bits):
    a=arena_type(max_nodes=1000000,max_work=200000000);roots=[];alive=set(range(1,rank+1));edges=[]
    if shape=='balanced':
        current=sorted(alive)
        while len(current)>1:
            edges.extend(zip(current[::2],current[1::2]));current=current[::2]
    else:edges=[(1 if shape=='star' else child-1,child) for child in range(2,rank+1)]
    for parent,child in edges:
        word=a.concat(a.power(a.letter(parent),1<<bits),a.letter(child))
        roots.extend((a.power(word,2),a.power(word,3)))
    return a,roots,alive


def plan(shape,rank,bits,mixed):
    a,roots,alive=build(WordArena,shape,rank,bits);moves=[]
    while len(alive)>1:
        if mixed and len(moves)%2:
            edges=plan_forest(a,roots,alive)[:2];assert edges
            moves.append(dict(kind='primitive_forest',edges=edges));apply_forest(a,roots,alive,edges)
        else:
            pairs=plan_projection(a,roots,alive);assert pairs
            if mixed:pairs=pairs[:1]
            moves.append(dict(kind='primitive_projection',pairs=pairs));apply_projection(a,roots,alive,pairs)
    return moves


def runs(arena,roots):
    memo={0:()}
    for root in roots:
        pending=[(root,False)]
        while pending:
            node,ready=pending.pop()
            if node in memo:continue
            rule=arena.rules[node]
            if rule[0]=='t':memo[node]=((rule[1],1),)
            elif not ready:pending.extend(((node,True),(rule[2],False),(rule[1],False)))
            else:
                out=list(memo[rule[1]])
                for letter,count in memo[rule[2]]:
                    if out and out[-1][0]==letter:out[-1]=(letter,out[-1][1]+count)
                    else:out.append((letter,count))
                assert len(out)<=1000
                memo[node]=tuple(out)
    return [memo[r] for r in roots]


def audit(old,search,group,projection,forest):
    rng=random.Random(SEED);inputs=list(harness.corpus());records=[];proofs={};replays=0;activations=0
    for i in range(240):
        strands=rng.randrange(2,6);word=[rng.choice((-1,1))*rng.randrange(1,strands) for _ in range(rng.randrange(1,15))]
        try:d=Diagram.from_braid(strands,word)
        except DiagramError:continue
        inputs.append(dict(name=f'random-{i}',pd=d.pd))
    for n in (5,9,17,33,65):
        inputs.append(dict(name=f'circle-{n}',pd=Diagram.from_braid(n,list(range(1,n))).pd))
    for source in inputs:
        d=Diagram.from_pd(source['pd']);od=old.Diagram.from_pd(source['pd']);modes={}
        for mode,options in [('default',{}),('projection',dict(primitive_projection=True)),('forest',dict(primitive_forest=True))]:
            found=[]
            for engine,diagram in ((search,od),(sys.modules['fastunknot.compressed_search'],d)):
                try:c=engine.compressed_certificate(diagram,relator_moves=True,max_work=2000000,**options)
                except (GroupLimit,group.GroupLimit):c=None
                found.append(c)
            assert found[0]==found[1];c=found[1];stats={};key=None
            if c:
                key=sha256(encode(c)).hexdigest();proofs[key]=c
                for compressed in (False,True):
                    assert group.verify_group_certificate(od,c,compressed=compressed,max_work=20000000)
                    assert verify_group_certificate(d,c,compressed=compressed,max_work=20000000,stats=stats if compressed else None)
                    replays+=2
                activations+=stats.get('anchored_replay_blocks',0)
            modes[mode]=dict(certificate_sha256=key,new_replay_stats=stats)
        records.append(dict(source=source,modes=modes))
    capacities=[]
    for shape,rank,bits,mixed in [('balanced',32,128,False),('star',32,128,False),('chain',16,512,True)]:
        moves=plan(shape,rank,bits,mixed);engines={};reference=None
        for label,arena_type in [('old',search.WordArena),('current',WordArena)]:
            a,roots,alive=build(arena_type,shape,rank,bits);initial=len(a.rules)-1;start=a.stats['work']
            if label=='old':
                for m in moves:assert (forest if m['kind']=='primitive_forest' else projection)(a,roots,alive,m)
            else:assert replay_compressed_monomial_block(a,roots,alive,moves)
            assert verify_compressed_rank_one(a,roots,alive,dict(kind='rank_one_exponent_zero',generator=next(iter(alive))))
            output=runs(a,roots)
            if reference is None:reference=output
            assert output==reference
            engines[label]=dict(initial_nodes=initial,final_nodes=len(a.rules)-1,replay_work=a.stats['work']-start,stats=deepcopy(a.stats))
        capacities.append(dict(shape=shape,rank=rank,bits=bits,mixed=mixed,moves=moves,engines=engines))
    return dict(cases=records,certificates=proofs,diagrams=len(records),source_replays=replays,
                anchored_blocks=activations,all_discovered_certificates_identical=True,capacity=capacities)


def benchmark(mode,old,search,group,projection,forest):
    if mode=='pipeline':return pipeline(old)
    rng=random.Random(SEED+1);records=[];proofs={};arms=('old','old_AA','current','current_AA')
    if mode=='kernels':
        cases=[dict(name=f'{shape}-{rank}-{bits}'+('-mixed' if mixed else ''),shape=shape,rank=rank,bits=bits,mixed=mixed,
                    moves=plan(shape,rank,bits,mixed))
               for shape,rank,bits,mixed in [('star',4,0,False),('balanced',32,64,False),('star',32,128,False),('chain',16,512,True)]]
    else:
        cases=[]
        for strands in (5,17,65,129):
            d=Diagram.from_braid(strands,list(range(1,strands)))
            for forest_mode in (False,True):
                c=compressed_certificate(d,primitive_projection=True,primitive_forest=forest_mode,primitive_power=False,max_work=20000000)
                key=sha256(encode(c)).hexdigest();proofs[key]=c
                cases.append(dict(name=f'circle-{strands}-'+('forest' if forest_mode else 'projection'),pd=d.pd,certificate_sha256=key))
    for source in cases:
        samples=[];warmups=[];reference=None
        for iteration in range(-1,5):
            order=list(arms);rng.shuffle(order);measurements={}
            for arm in order:
                label=arm.removesuffix('_AA');begin=time.perf_counter()
                if mode=='kernels':
                    a,roots,alive=build(search.WordArena if label=='old' else WordArena,source['shape'],source['rank'],source['bits'])
                    if label=='old':
                        for m in source['moves']:assert (forest if m['kind']=='primitive_forest' else projection)(a,roots,alive,m)
                    else:assert replay_compressed_monomial_block(a,roots,alive,source['moves'])
                    assert verify_compressed_rank_one(a,roots,alive,dict(kind='rank_one_exponent_zero',generator=next(iter(alive))))
                    end=time.perf_counter();stats=deepcopy(a.stats);extra=dict(final_nodes=len(a.rules)-1)
                    output=runs(a,roots)
                    if reference is None:reference=output
                    assert output==reference
                else:
                    engine=old if label=='old' else sys.modules['fastunknot'];diagram=engine.Diagram.from_pd(source['pd']);stats={}
                    verify=group.verify_group_certificate if label=='old' else verify_group_certificate
                    assert verify(diagram,proofs[source['certificate_sha256']],compressed=True,max_work=20000000,stats=stats)
                    end=time.perf_counter();extra={}
                measurements[arm]=dict(seconds=end-begin,completed=True,stats=stats,**extra)
            (warmups if iteration<0 else samples).append(dict(order=order,measurements=measurements))
        medians={arm:median(s['measurements'][arm]['seconds'] for s in samples) for arm in arms}
        ratios={f'{a}/{b}':median(s['measurements'][a]['seconds']/s['measurements'][b]['seconds'] for s in samples)
                for a,b in (('old','current'),('old','old_AA'),('current','current_AA'))}
        records.append(dict(source=source,samples=samples,warmups=warmups,medians=medians,paired_ratios=ratios));print(source['name'],ratios,flush=True)
    return dict(cases=records,certificates=proofs,measured_calls=len(cases)*20,warmup_calls=len(cases)*4,completed_calls=len(cases)*20,
        scope=('Fresh grammar construction, authenticated supplied monomial schedule and endpoint. Discovery excluded; abstract Z presentations, no knot claim.' if mode=='kernels' else 'Fresh validated PD, independent presentation recovery, full supplied certificate and endpoint. Producer discovery excluded; same proof in both arms.')+' Five shuffled paired rounds and both A/A controls; exact comparisons outside timers.')


def pipeline(old):
    rng=random.Random(SEED+2);records=[];proofs={};arms=('old','old_AA','current','current_AA')
    for source in harness.corpus():
        samples=[];warmups=[]
        for iteration in range(-1,5):
            order=list(arms);rng.shuffle(order);measurements={}
            for arm in order:
                engine=old if arm.startswith('old') else sys.modules['fastunknot'];begin=time.perf_counter()
                result=engine.recognize(engine.Diagram.from_pd(source['pd']),use_group=True,
                    group_primitive_projection=True,group_relators=True,group_compressed_search=True,
                    group_seconds=10,group_max_work=20000000,seconds=12,max_objects=50000)
                elapsed=time.perf_counter()-begin;complete=result.status in ('UNKNOT','KNOTTED')
                if complete:assert result.status==source['expected']
                groups=[]
                for g in harness.stage_records(result.evidence):
                    row={k:v for k,v in g.items() if k!='certificate'}
                    if 'certificate' in g:
                        c=g['certificate'];key=sha256(encode(c)).hexdigest();proofs[key]=c;row['certificate_sha256']=key
                    groups.append(row)
                measurements[arm]=dict(seconds=elapsed,completed=complete,status=result.status,groups=groups)
            (warmups if iteration<0 else samples).append(dict(order=order,measurements=measurements))
        medians={a:median(s['measurements'][a]['seconds'] for s in samples if s['measurements'][a]['completed'])
                 if any(s['measurements'][a]['completed'] for s in samples) else None for a in arms}
        ratios=harness.ratios(samples,[('current','old','current'),('old_AA','old','old_AA'),('current_AA','current','current_AA')])
        records.append(dict(source=source,samples=samples,warmups=warmups,medians=medians,paired_ratios=ratios));print(source['name'],ratios,flush=True)
    return dict(cases=records,certificates=proofs,measured_calls=len(records)*20,warmup_calls=len(records)*4,
        completed_calls=sum(m['completed'] for r in records for s in r['samples'] for m in s['measurements'].values()),
        scope='Whole recognition from fresh validated PDs, with primitive projection enabled in both packages. '
        'Includes discovery and mandatory independent source replay. Five shuffled paired rounds and both A/A controls. Failures retained.')


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('mode',choices=('audit','kernels','source','pipeline'));p.add_argument('--output',type=Path,required=True);args=p.parse_args()
    before=sources();harness.BASELINE=BASELINE;begin=time.perf_counter()
    with tempfile.TemporaryDirectory(prefix='unknot-anchored-replay-') as directory:
        old,search,group,hashes=harness.baseline(directory)
        changed={name for name,h in hashes.items() if h!=sha256((ROOT/'fastunknot'/name).read_bytes()).hexdigest()}
        assert changed=={'compressed_group.py'},changed
        projection=importlib.import_module(old.__name__+'.primitive_projection_verify').replay_compressed_projection
        forest=importlib.import_module(old.__name__+'.primitive_forest_verify').replay_compressed_forest
        result=audit(old,search,group,projection,forest) if args.mode=='audit' else benchmark(args.mode,old,search,group,projection,forest)
    assert before==sources()
    result.update(mode=args.mode,baseline_commit=BASELINE,source_sha256=before,baseline_source_sha256=hashes,source_hashes_unchanged=True,
        seconds=time.perf_counter()-begin,seed=SEED,python=platform.python_version(),platform=platform.platform())
    args.output.write_text(json.dumps(json_safe(result),indent=2)+'\n');print('complete',args.mode,result['seconds'],flush=True)


if __name__=='__main__':main()
