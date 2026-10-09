"""Pinned ordered-batch compatibility audit and complete replay/search timings."""
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
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from primitive_power_research import forests as harness
from fastunknot import Diagram, DiagramError, recognize
from fastunknot.compressed_search import compressed_certificate
from fastunknot.compressed_words import WordArena
from fastunknot.elimination_batch_verify import replay_compressed_batch, replay_literal_batch
from fastunknot.group_certificate import group_decide, verify_group_certificate, _Budget, GroupLimit
from fastunknot.integer_codec import json_safe
from cyclic_overlap_research.native import stage_records
BASELINE='06fcb7685da7770b1f7e9ff1df7f6164222100ee';SEED=261009035


def sources():
    paths=list(ROOT.rglob('*.py'))+[harness.CORPUS]
    return {str(p.relative_to(ROOT.parent)):sha256(p.read_bytes()).hexdigest() for p in paths}


def encode(c):return json.dumps(json_safe(c),sort_keys=True,separators=(',',':')).encode()


def digest(a,roots):
    hashes={0:sha256(b'empty').digest()}
    for n in a._reachable(roots):
        r=a.rules[n];hashes[n]=sha256(('t'+str(r[1])).encode()).digest() if r[0]=='t' else sha256(b'c'+hashes[r[1]]+hashes[r[2]]).digest()
    return [hashes[r].hex() for r in roots]


def family(arena_type,kind,size):
    a=arena_type(max_nodes=1000000,max_work=100000000);roots=[];entries=[]
    if kind=='shared':
        body=a.power(a.from_word([1,2]),1<<4096)
        for g in range(3,size+3):
            roots.append(a.concat(a.letter(-g),body));entries.append(dict(relation=len(roots)-1,generator=g))
    else:
        previous=1
        for g in range(3,size+3):
            body=a.power(a.from_word([previous,1,-previous,2]),1<<128)
            roots.append(a.concat(a.letter(-g),body));entries.append(dict(relation=len(roots)-1,generator=g));previous=g
    roots.extend([a.from_word([size+2,-3]),0,a.letter(-(size+2))])
    if kind=='legacy':entries.reverse()
    return a,roots,set(range(1,size+3)),dict(kind='elimination_batch',entries=entries)


def audit(old,old_search,old_group,old_replay):
    rng=random.Random(SEED);abstract=[]
    for case in range(400):
        rank=rng.randrange(3,10);words=[];entries=[];images={1:[1],-1:[-1],2:[2],-2:[-2]}
        for g in range(3,rank+1):
            context=[rng.choice((-1,1))*rng.randrange(1,g) for _ in range(rng.randrange(5))]
            sign=rng.choice((-1,1));cut=rng.randrange(len(context)+1)
            # Rotate a donor while retaining the defining cyclic context.
            word=[sign*g]+context;word=word[cut:]+word[:cut]
            value=[y for x in context for y in images[x]]
            if sign>0:value=[-x for x in reversed(value)]
            images[g]=value;images[-g]=[-x for x in reversed(value)]
            entries.append(dict(relation=len(words),generator=g));words.append(word)
        words += [[rng.choice((-1,1))*rng.randrange(1,rank+1) for _ in range(rng.randrange(12))] for _ in range(4)]
        expected=[[] if i<len(entries) else [y for x in w for y in images[x]] for i,w in enumerate(words)]
        records=[]
        for order in (entries,list(reversed(entries))):
            evidence=dict(kind='elimination_batch',entries=order)
            for arena_type,replay,label in ((old_search.WordArena,old_replay,'old'),(WordArena,replay_compressed_batch,'current')):
                a=arena_type(max_work=10000000);roots=[a.from_word(w) for w in words];alive=set(range(1,rank+1))
                M=len(a._reachable(roots));N=len(a.rules)-1
                assert replay(a,roots,alive,evidence)
                assert alive=={1,2} and [a.expand(r,limit=1000000) for r in roots]==expected
                added=len(a.rules)-1-N;bound=5 if a.stats.get('elimination_ordered_replays') else 7
                assert added<=bound*M
                records.append(dict(engine=label,ordered=order==entries,new_nodes=added,source_nodes=M,stats=a.stats))
            literal=deepcopy(words);assert replay_literal_batch(literal,set(range(1,rank+1)),evidence,_Budget(lambda:None,10000000,10000000));assert literal==expected
        abstract.append(records)
    inputs=list(harness.corpus())
    for i in range(240):
        strands=rng.randrange(2,6);word=[rng.choice((-1,1))*rng.randrange(1,strands) for _ in range(rng.randrange(1,15))]
        try:d=Diagram.from_braid(strands,word)
        except DiagramError:continue
        inputs.append(dict(name=f'random-{i}',pd=d.pd))
    for n in (4,8,16,32,64,128):inputs.append(dict(name=f'circle-{n}',pd=Diagram.from_braid(n+1,list(range(1,n+1))).pd))
    rows=[];proofs={};replays=0
    for source in inputs:
        cases={};d=Diagram.from_pd(source['pd']);od=old.Diagram.from_pd(source['pd'])
        for mode,options in (('default',{}),('batch',dict(elimination_batch=True))):
            result={}
            for label,diagram,search in (('old',od,old_search.compressed_certificate),('current',d,compressed_certificate)):
                stats={}
                try:c=search(diagram,relator_moves=True,max_work=2000000,stats=stats,**options);reason=None
                except (GroupLimit,old_group.GroupLimit) as exc:c=None;reason=str(exc)
                key=None
                if c:
                    key=sha256(encode(c)).hexdigest();proofs[key]=c
                    for group,source_d in ((old_group,od),(sys.modules['fastunknot.group_certificate'],d)):
                        for compressed in (False,True):
                            assert group.verify_group_certificate(source_d,c,compressed=compressed,max_work=20000000);replays+=1
                result[label]=dict(certificate_sha256=key,reason=reason,stats=stats)
            if mode=='default':assert result['old']['certificate_sha256']==result['current']['certificate_sha256']
            cases[mode]=result
        rows.append(dict(source=source,modes=cases))
    return dict(abstract=abstract,abstract_dags=400,abstract_compressed_replays=1600,abstract_literal_replays=800,cases=rows,diagrams=len(rows),source_replays=replays,certificates=proofs,default_certificates_identical=True,
        batch_lost=sum(bool(r['modes']['batch']['old']['certificate_sha256'] and not r['modes']['batch']['current']['certificate_sha256']) for r in rows),batch_gained=sum(bool(not r['modes']['batch']['old']['certificate_sha256'] and r['modes']['batch']['current']['certificate_sha256']) for r in rows))


def benchmark(old,old_search,old_group,old_replay,kind):
    rng=random.Random(SEED+1);rows=[];proofs={};arms=('old','current','old_AA','current_AA')
    if kind=='kernels':cases=[dict(kind=k,size=n) for k in ('shared','tower','legacy') for n in (8,32,128)]
    elif kind=='stages':cases=[dict(name=f'circle-{n}',crossings=n,pd=Diagram.from_braid(n+1,list(range(1,n+1))).pd,expected='UNKNOT') for n in (8,16,32,64,128,256)]
    else:cases=harness.corpus()
    for source in cases:
        samples=[];warmups=[]
        for iteration in range(-1,5):
            order=list(arms);rng.shuffle(order);measurements={}
            for arm in order:
                prior=arm.startswith('old');begin=time.perf_counter()
                if kind=='kernels':
                    a,roots,alive,evidence=family(old_search.WordArena if prior else WordArena,source['kind'],source['size'])
                    construction=time.perf_counter();initial=len(a.rules)-1;work=a.stats['work']
                    assert (old_replay if prior else replay_compressed_batch)(a,roots,alive,evidence)
                    end=time.perf_counter();assert alive=={1,2}
                    record=dict(status='COMPLETE',completed=True,construction_seconds=construction-begin,replay_seconds=end-construction,
                        source_nodes=initial,new_nodes=len(a.rules)-1-initial,replay_work=a.stats['work']-work,stats=dict(a.stats),length_bits=max(a.lengths[r].bit_length() for r in roots))
                    record['digests']=digest(a,roots)
                else:
                    package=old if prior else sys.modules['fastunknot'];group=old_group if prior else sys.modules['fastunknot.group_certificate']
                    if kind=='stages':result=group.group_decide(package.Diagram.from_pd(source['pd']),elimination_batch=True,compressed_search=True,max_work=20000000,seconds=20)
                    else:result=package.recognize(package.Diagram.from_pd(source['pd']),use_group=True,group_elimination_batch=True,group_relators=True,group_compressed_search=True,group_seconds=10,group_max_work=20000000,seconds=12,max_objects=50000)
                    end=time.perf_counter();status=result['status'] if kind=='stages' else result.status
                    record=dict(status=status,completed=status in ('UNKNOT','KNOTTED'),groups=[])
                    if record['completed']:assert status==source['expected']
                    for g in ([result] if kind=='stages' else stage_records(result.evidence)):
                        data={k:v for k,v in g.items() if k!='certificate'}
                        if 'certificate' in g:
                            c=g['certificate'];raw=encode(c);key=sha256(raw).hexdigest();proofs[key]=c;data.update(certificate_sha256=key,certificate_bytes=len(raw))
                        record['groups'].append(data)
                record['seconds']=end-begin;measurements[arm]=record
            if kind=='kernels':assert all(m['digests']==measurements['old']['digests'] for m in measurements.values())
            (warmups if iteration<0 else samples).append(dict(order=order,measurements=measurements))
        medians={arm:median(s['measurements'][arm]['seconds'] for s in samples if s['measurements'][arm]['completed']) if any(s['measurements'][arm]['completed'] for s in samples) else None for arm in arms}
        ratios=harness.ratios(samples,[('current','old','current'),('old_AA','old','old_AA'),('current_AA','current','current_AA')])
        rows.append(dict(source=source,samples=samples,warmups=warmups,medians=medians,paired_ratios=ratios));print(source.get('name',(source.get('kind'),source.get('size'))),ratios,flush=True)
    return dict(cases=rows,certificates=proofs,measured_calls=len(rows)*20,warmup_calls=len(rows)*4,completed_calls=sum(m['completed'] for r in rows for s in r['samples'] for m in s['measurements'].values()),scope=dict(kernels='Fresh grammar construction and complete checked substitution. Three families include legacy reversed witnesses; no diagram discovery.',stages='Fresh diagram validation, complete optional batch group search and mandatory independent source replay. Earlier simplification bypassed.',pipeline='Complete recognition of fresh PDs with the same optional batch portfolio in both engines, including mandatory replay. Incomplete outcomes retained.')[kind])


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('mode',choices=('audit','kernels','stages','pipeline'));p.add_argument('--output',type=Path,required=True);args=p.parse_args()
    before=sources();harness.BASELINE=BASELINE;begin=time.perf_counter()
    with tempfile.TemporaryDirectory(prefix='unknot-ordered-batch-') as directory:
        old,search,group,hashes=harness.baseline(directory)
        changed={n for n,h in hashes.items() if h!=sha256((ROOT/'fastunknot'/n).read_bytes()).hexdigest()}
        assert changed=={'elimination_batch.py','elimination_batch_verify.py','compressed_search.py'},changed
        replay=importlib.import_module(search.__package__+'.elimination_batch_verify').replay_compressed_batch
        result=audit(old,search,group,replay) if args.mode=='audit' else benchmark(old,search,group,replay,args.mode)
    assert before==sources()
    result.update(mode=args.mode,baseline_commit=BASELINE,baseline_source_sha256=hashes,source_sha256=before,source_hashes_unchanged=True,seconds=time.perf_counter()-begin,seed=SEED,python=platform.python_version(),platform=platform.platform())
    args.output.write_text(json.dumps(json_safe(result),indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('cases','abstract','certificates','source_sha256','baseline_source_sha256')},indent=2))


if __name__=='__main__':main()
