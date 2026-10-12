"""Pinned power-pair source audit, binary capacity and whole-call controls."""
import argparse
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
from primitive_power_research import forests as harness
from compressed_word_research.ordered_batch import encode
from fastunknot import Diagram,DiagramError
from fastunknot import compressed_search as current
from fastunknot.group_certificate import GroupLimit,verify_group_certificate
from fastunknot.power_pair_verify import replay_compressed_power_pairs
from fastunknot.primitive_forest import plan_forest
from fastunknot.integer_codec import json_safe
from test_power_pair import family,source_certificate

BASELINE='00a33ce6714e45654b3b07057853d756e07b33ff';SEED=261009439


def sources():
    return {str(p.relative_to(ROOT.parent)):sha256(p.read_bytes()).hexdigest() for p in list(ROOT.rglob('*.py'))+[harness.CORPUS]}


def audit(old,search,group):
    rng=random.Random(SEED);inputs=list(harness.corpus());rows=[];proofs={};replays=0
    for i in range(240):
        strands=rng.randrange(2,6);word=[rng.choice((-1,1))*rng.randrange(1,strands) for _ in range(rng.randrange(1,15))]
        try:d=Diagram.from_braid(strands,word)
        except DiagramError:continue
        inputs.append(dict(name=f'random-{i}',pd=d.pd))
    for source in inputs:
        modes={};d=Diagram.from_pd(source['pd']);od=old.Diagram.from_pd(source['pd'])
        for mode,options in [('default',{}),('projection',dict(primitive_projection=True)),('forest',dict(primitive_forest=True))]:
            results={}
            for label,engine,diagram in [('old',search,od),('current',current,d)]:
                stats={}
                try:c=engine.compressed_certificate(diagram,relator_moves=True,max_work=2000000,stats=stats,**options);reason=None
                except (GroupLimit,group.GroupLimit) as exc:c=None;reason=str(exc)
                key=None
                if c:
                    key=sha256(encode(c)).hexdigest();proofs[key]=c
                    for compressed in (False,True):
                        assert verify_group_certificate(d,c,compressed=compressed,max_work=20000000);replays+=1
                results[label]=dict(certificate_sha256=key,reason=reason,stats=stats)
            if mode=='default':assert results['old']['certificate_sha256']==results['current']['certificate_sha256']
            modes[mode]=results
        rows.append(dict(source=source,modes=modes))
    diagram,c=source_certificate();assert all(verify_group_certificate(diagram,c,compressed=v) for v in (False,True))
    key=sha256(encode(c)).hexdigest();proofs[key]=c
    capacity=[]
    for pairs,bits in ((1,8),(8,128),(32,256),(4,4096)):
        a,rr,alive=family(pairs,bits);original=rr[:];remaining=set(alive)
        assert not plan_forest(a,rr,alive)
        initial=len(a.rules)-1;before=a.stats['work'];moves=[];terminal={}
        assert current._search(a,rr,alive,moves,primitive_forest=True,primitive_terminal=terminal)
        assert [m['kind'] for m in moves]==['power_pair_delete']
        production=a.stats['work']-before;start=a.stats['work']
        assert replay_compressed_power_pairs(a,original,remaining,moves[0])
        assert alive==remaining=={1} and not any(rr) and not any(original)
        capacity.append(dict(pairs=pairs,bits=bits,source_nodes=initial,final_nodes=len(a.rules)-1,production_work=production,replay_work=a.stats['work']-start,moves=moves,terminal=terminal))
    return dict(cases=rows,certificates=proofs,diagrams=len(rows),source_replays=replays+2,
        constructed_prefix_certificate=key,capacity=capacity,default_certificates_identical=True,
        changes={mode:dict(lost=sum(bool(r['modes'][mode]['old']['certificate_sha256'] and not r['modes'][mode]['current']['certificate_sha256']) for r in rows),
            gained=sum(bool(not r['modes'][mode]['old']['certificate_sha256'] and r['modes'][mode]['current']['certificate_sha256']) for r in rows),
            changed=sum(r['modes'][mode]['old']['certificate_sha256']!=r['modes'][mode]['current']['certificate_sha256'] for r in rows)) for mode in ('projection','forest')},
        discovered_power_proofs=sum(any(m['kind']=='power_pair_delete' for m in c['moves']) for k,c in proofs.items() if k!=key))


def benchmark(old):
    rng=random.Random(SEED+1);rows=[];proofs={};arms=('old','current','old_AA','current_AA')
    for source in harness.corpus():
        samples=[];warmups=[]
        for iteration in range(-1,5):
            order=list(arms);rng.shuffle(order);measurements={}
            for arm in order:
                engine=old if arm.startswith('old') else sys.modules['fastunknot'];begin=time.perf_counter()
                result=engine.recognize(engine.Diagram.from_pd(source['pd']),use_group=True,group_primitive_forest=True,
                    group_relators=True,group_compressed_search=True,group_seconds=10,group_max_work=20000000,seconds=12,max_objects=50000)
                elapsed=time.perf_counter()-begin;complete=result.status in ('UNKNOT','KNOTTED')
                if complete:assert result.status==source['expected']
                groups=[]
                for g in harness.stage_records(result.evidence):
                    record={k:v for k,v in g.items() if k!='certificate'}
                    if 'certificate' in g:
                        c=g['certificate'];key=sha256(encode(c)).hexdigest();proofs[key]=c;record['certificate_sha256']=key
                    groups.append(record)
                measurements[arm]=dict(seconds=elapsed,completed=complete,status=result.status,groups=groups)
            (warmups if iteration<0 else samples).append(dict(order=order,measurements=measurements))
        medians={a:median(s['measurements'][a]['seconds'] for s in samples if s['measurements'][a]['completed']) if any(s['measurements'][a]['completed'] for s in samples) else None for a in arms}
        ratios=harness.ratios(samples,[('current','old','current'),('old_AA','old','old_AA'),('current_AA','current','current_AA')])
        rows.append(dict(source=source,samples=samples,warmups=warmups,medians=medians,paired_ratios=ratios));print(source['name'],ratios,flush=True)
    return dict(cases=rows,certificates=proofs,measured_calls=len(rows)*20,warmup_calls=len(rows)*4,
        completed_calls=sum(m['completed'] for r in rows for s in r['samples'] for m in s['measurements'].values()),
        scope='Complete recognition of fresh validated PDs with primitive forest enabled in both packages, including independent source replay. Resource failures retained. Five shuffled paired rounds and both A/A controls.')


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('mode',choices=('audit','benchmark'));parser.add_argument('--output',type=Path,required=True);args=parser.parse_args()
    before=sources();harness.BASELINE=BASELINE;begin=time.perf_counter()
    with tempfile.TemporaryDirectory(prefix='unknot-power-pairs-') as directory:
        old,search,group,hashes=harness.baseline(directory)
        changed={n for n,h in hashes.items() if h!=sha256((ROOT/'fastunknot'/n).read_bytes()).hexdigest()}
        assert changed=={'group_certificate.py','compressed_group.py','compressed_search.py'},changed
        result=audit(old,search,group) if args.mode=='audit' else benchmark(old)
    assert before==sources()
    result.update(mode=args.mode,baseline_commit=BASELINE,source_sha256=before,baseline_source_sha256=hashes,source_hashes_unchanged=True,seed=SEED,
        seconds=time.perf_counter()-begin,python=platform.python_version(),platform=platform.platform())
    args.output.write_text(json.dumps(json_safe(result),indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('cases','certificates','source_sha256','baseline_source_sha256')},indent=2))


if __name__=='__main__':main()
