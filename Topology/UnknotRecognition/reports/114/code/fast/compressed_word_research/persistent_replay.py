"""Pinned whole-block replay audits and complete native-call measurements."""
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
from compressed_word_research import ordered_batch as prior
from fastunknot.compressed_words import WordArena, CompressedLimit
from fastunknot.persistent_elimination_verify import replay_compressed_block
from fastunknot.elimination_batch_verify import replay_literal_batch
from fastunknot.group_certificate import _Budget, verify_group_certificate
from fastunknot import Diagram
from fastunknot.integer_codec import json_safe
from test_persistent_elimination import doubling,move
BASELINE='63c262ac3c22ab98b9cd46dfb4923f16bd10c511';SEED=261009064


def sources():
    return {str(p.relative_to(ROOT.parent)):sha256(p.read_bytes()).hexdigest()
            for p in list(ROOT.rglob('*.py'))+[prior.harness.CORPUS]}


def build(arena_type,kind,size):
    a=arena_type(max_nodes=1000000,max_work=100000000)
    if kind=='contexts':
        words,moves=doubling(size);roots=[a.from_word(w) for w in words]
        alive=set(range(1,size+5));expected=[0]*size+[(1<<size)+2]
    elif kind in ('tower','legacy'):
        roots=[];entries=[];previous=1;length=1
        for g in range(3,size+3):
            body=a.power(a.from_word([previous,1,-previous,2]),1<<128)
            roots.append(a.concat(a.letter(-g),body));entries.append((len(roots)-1,g))
            previous=g;length=(2*length+2)*(1<<128)
        roots.extend((a.letter(previous),a.letter(-previous)))
        moves=[]
        for i in range(0,len(entries),4):
            batch=entries[i:i+4];moves.append(move(list(reversed(batch)) if kind=='legacy' else batch))
        alive=set(range(1,size+3));expected=[0]*size+[length,length]
    else:
        # Two shallow independent batches: an explicit conversion-overhead control.
        roots=[a.from_word([-g,1,2]) for g in range(3,size+3)]+[a.from_word([3,-(size+2)])]
        middle=size//2;entries=[(g-3,g) for g in range(3,size+3)]
        moves=[move(entries[:middle]),move(entries[middle:])]
        alive=set(range(1,size+3));expected=[0]*size+[4]
    return a,roots,alive,moves,expected


def old_block(replay,a,roots,alive,moves):
    return all(replay(a,roots,alive,m) for m in moves)


def audit(old,search,group,replay):
    # Retain the historical source corpus and all four source-bound checkers.
    result=prior.audit(old,search,group,replay)
    assert result['batch_lost']==result['batch_gained']==0
    assert all(r['modes']['batch']['old']['certificate_sha256']==r['modes']['batch']['current']['certificate_sha256'] for r in result['cases'])
    rng=random.Random(SEED);blocks=[];literal_replays=0
    for case in range(400):
        rank=rng.randrange(4,11);words=[];entries=[]
        for g in range(3,rank+1):
            body=[rng.choice((-1,1))*rng.randrange(1,g) for _ in range(rng.randrange(4))]
            word=[rng.choice((-1,1))*g]+body;cut=rng.randrange(len(word))
            words.append(word[cut:]+word[:cut]);entries.append((g-3,g))
        words += [[],[rng.choice((-1,1))*rng.randrange(1,rank+1) for _ in range(12)]]
        rng.shuffle(entries);moves=[]
        while entries:
            n=rng.randrange(1,min(3,len(entries))+1);moves.append(move(entries[:n]));del entries[:n]
        expected=deepcopy(words);alive=set(range(1,rank+1))
        for m in moves:
            assert replay_literal_batch(expected,alive,m,_Budget(lambda:None,1000000,10000000));literal_replays+=1
        engines={}
        for label,arena_type in (('old',search.WordArena),('current',WordArena)):
            a=arena_type(max_work=10000000);roots=[a.from_word(w) for w in words];remaining=set(range(1,rank+1))
            assert (old_block(replay,a,roots,remaining,moves) if label=='old' else replay_compressed_block(a,roots,remaining,moves))
            assert remaining==alive and [a.expand(r,limit=1000000) for r in roots]==expected
            engines[label]=dict(nodes=len(a.rules)-1,stats=a.stats)
        blocks.append(dict(words=words,moves=moves,expected=expected,engines=engines))
    transformed=[]
    for key,c in list(result['certificates'].items()):
        if not any(m['kind']=='elimination_batch' and len(m['entries'])>=2 for m in c['moves']):continue
        candidate=deepcopy(c);candidate['moves']=[piece for m in c['moves'] for piece in
            ([dict(kind='elimination_batch',entries=[e]) for e in m['entries']] if m['kind']=='elimination_batch' else [m])]
        raw=prior.encode(candidate);newkey=sha256(raw).hexdigest();result['certificates'][newkey]=candidate
        stats={};assert verify_group_certificate(Diagram.from_pd(c['input_pd']),candidate,compressed=True,max_work=20000000,stats=stats)
        assert verify_group_certificate(Diagram.from_pd(c['input_pd']),candidate,compressed=False,max_work=20000000)
        assert group.verify_group_certificate(old.Diagram.from_pd(c['input_pd']),candidate,compressed=True,max_work=20000000)
        assert group.verify_group_certificate(old.Diagram.from_pd(c['input_pd']),candidate,compressed=False,max_work=20000000)
        transformed.append(dict(original=key,split=newkey,stats=stats))
    result.update(random_blocks=blocks,block_compressed_replays=800,block_literal_moves=literal_replays,
                  split_source_certificates=transformed,split_source_replays=4*len(transformed),producer_certificates_identical=True)
    return result


def kernels(search,replay):
    rng=random.Random(SEED+1);arms=('old','current','old_AA','current_AA');records=[]
    cases=[(kind,size) for kind in ('contexts','tower','legacy','shallow') for size in (8,32,128)]
    for kind,size in cases:
        samples=[];warmups=[]
        for iteration in range(-1,5):
            order=list(arms);rng.shuffle(order);measurements={}
            for arm in order:
                old=arm.startswith('old');begin=time.perf_counter()
                a,roots,alive,moves,expected=build(search.WordArena if old else WordArena,kind,size)
                built=time.perf_counter();initial=len(a.rules)-1;work=a.stats['work']
                reason=None
                try:
                    assert (old_block(replay,a,roots,alive,moves) if old else replay_compressed_block(a,roots,alive,moves))
                    completed=True
                except (CompressedLimit,search.CompressedLimit) as exc:
                    completed=False;reason=str(exc)
                end=time.perf_counter()
                if completed:assert [a.lengths[r] for r in roots]==expected
                # Hashes are structural evidence only; differing associations are
                # expected. Exact semantics are audited independently on literals.
                measurements[arm]=dict(seconds=end-begin,construction_seconds=built-begin,replay_seconds=end-built,completed=completed,reason=reason,
                    initial_nodes=initial,added_nodes=len(a.rules)-1-initial,replay_work=a.stats['work']-work,stats=dict(a.stats),
                    output_length_bits=max(a.lengths[r].bit_length() for r in roots),moves=moves,
                    root_digests=prior.digest(a,roots) if completed else None)
            (warmups if iteration<0 else samples).append(dict(order=order,measurements=measurements))
        medians={a:median(s['measurements'][a]['seconds'] for s in samples if s['measurements'][a]['completed'])
                 if any(s['measurements'][a]['completed'] for s in samples) else None for a in arms}
        ratios=prior.harness.ratios(samples,[('current','old','current'),('old_AA','old','old_AA'),('current_AA','current','current_AA')])
        records.append(dict(source=dict(kind=kind,size=size),samples=samples,warmups=warmups,medians=medians,paired_ratios=ratios));print(kind,size,ratios,flush=True)
    return dict(cases=records,measured_calls=len(records)*20,warmup_calls=len(records)*4,
                completed_calls=sum(m['completed'] for r in records for s in r['samples'] for m in s['measurements'].values()),
                scope='Fresh binary grammar construction plus complete supplied-block replay. Four shuffled arms, five measured rounds and retained warm-ups. Exact output lengths checked outside timers; structural digests are not word-equality proofs. No source discovery or whole-knot claim.')


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('mode',choices=('audit','kernels','stages','pipeline'));p.add_argument('--output',type=Path,required=True);args=p.parse_args()
    before=sources();prior.harness.BASELINE=BASELINE;prior.SEED=SEED;begin=time.perf_counter()
    with tempfile.TemporaryDirectory(prefix='unknot-persistent-replay-') as directory:
        old,search,group,hashes=prior.harness.baseline(directory)
        changed={n for n,h in hashes.items() if h!=sha256((ROOT/'fastunknot'/n).read_bytes()).hexdigest()}
        assert changed=={'compressed_group.py'},changed
        replay=importlib.import_module(search.__package__+'.elimination_batch_verify').replay_compressed_batch
        if args.mode=='audit':result=audit(old,search,group,replay)
        elif args.mode=='kernels':result=kernels(search,replay)
        else:result=prior.benchmark(old,search,group,replay,args.mode)
    assert before==sources()
    result.update(mode=args.mode,baseline_commit=BASELINE,source_sha256=before,baseline_source_sha256=hashes,source_hashes_unchanged=True,
                  seconds=time.perf_counter()-begin,seed=SEED,python=platform.python_version(),platform=platform.platform())
    args.output.write_text(json.dumps(json_safe(result),indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('cases','certificates','abstract','random_blocks','split_source_certificates','source_sha256','baseline_source_sha256')},indent=2))


if __name__=='__main__':main()
