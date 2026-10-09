"""Incremental reachability and phase-aware elimination portfolio audits."""
import argparse
import importlib
import inspect
from hashlib import sha256
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
from fastunknot.group_certificate import group_decide, verify_group_certificate, GroupLimit
from fastunknot.integer_codec import json_safe
from fastunknot.elimination_batch import apply_batch, plan_batch
from fastunknot.compressed_words import WordArena
from fastunknot.elimination_batch_verify import replay_compressed_batch
from cyclic_overlap_research.native import stage_records
from test_elimination_batch import tower
BASELINE='47e87a72c23d92743e7f11dd474094616731e0e4';SEED=261008517
harness.BASELINE=BASELINE


def sources():
    paths=list((ROOT/'fastunknot').rglob('*.py'))+[Path(__file__),Path(harness.__file__),ROOT/'tests/test_elimination_batch.py',ROOT/'tests/test_elimination_reach.py',ROOT/'primitive_power_research/elimination.py',ROOT/'cyclic_overlap_research/native.py',harness.CORPUS]
    return {str(p.relative_to(ROOT.parent)):sha256(p.read_bytes()).hexdigest() for p in paths}


def encode(c):return json.dumps(json_safe(c),sort_keys=True,separators=(',',':')).encode()


def digest(arena,roots):
    values={0:sha256(b'empty').digest()}
    for node in arena._reachable(roots):
        rule=arena.rules[node]
        values[node]=sha256(('t'+str(rule[1])).encode()).digest() if rule[0]=='t' else sha256(b'c'+values[rule[1]]+values[rule[2]]).digest()
    return [values[r].hex() for r in roots]


def capacity():
    rows=[]
    for depth,bits in ((8,128),(64,64),(64,1024)):
        a,roots,alive,move=tower(depth,bits);b,rr,ll,_=tower(depth,bits)
        initial=len(a.rules);apply_batch(a,roots,alive,move['entries'])
        assert replay_compressed_batch(b,rr,ll,move);assert alive==ll=={1,2}
        assert digest(a,roots)==digest(b,rr)
        length=1
        for _ in range(depth):length=(2*length+2)*(1<<bits)
        assert a.lengths[roots[-3]]==b.lengths[rr[-3]]==length
        rows.append(dict(depth=depth,exponent_bits=bits,initial_nodes=initial,producer_nodes=len(a.rules),replay_nodes=len(b.rules),output_length_bits=length.bit_length(),producer_stats=a.stats,replay_stats=b.stats,root_digests=digest(a,roots)))
    return dict(cases=rows,scope='Abstract nonmonomial definition towers with two surviving generators. Exact linked-circuit replay and encoded capacity only; not knot verdicts or whole-recognition timings.')


def audit(old,old_search,old_group,hashes):
    from primitive_power_research import elimination as prior
    from test_elimination_reach import literal_plan
    old_plan=importlib.import_module(old_search.__package__+'.elimination_batch')
    assert inspect.getsource(old_plan.apply_batch)==inspect.getsource(apply_batch)
    for name in ('elimination_batch_verify','compressed_group','compressed_words'):
        assert hashes[name+'.py']==sha256((ROOT/'fastunknot'/f'{name}.py').read_bytes()).hexdigest()
    from fastunknot import group_certificate as current_group
    for name in ('_presentation','_reduce','verify_group_certificate'):
        assert inspect.getsource(getattr(old_group,name))==inspect.getsource(getattr(current_group,name))
    result=prior.audit(old,old_search,old_group,hashes)
    comparisons=0
    for row in result['cases']:
        d=old.Diagram.from_pd(row['source']['pd'])
        try:c=old_search.compressed_certificate(d,elimination_batch=True,relator_moves=True,max_work=2000000)
        except old_group.GroupLimit:c=None
        key=sha256(encode(c)).hexdigest() if c else None
        assert key==row['direct']['certificate_sha256'];comparisons+=1
    rng=random.Random(SEED);planner_comparisons=0
    for _ in range(750):
        labels=[1,3,19,41,103,1009];words=[[rng.choice((-1,1))*rng.choice(labels) for _ in range(rng.randrange(20))] for _ in range(rng.randrange(1,15))]
        a=WordArena();b=old_search.WordArena();roots=[a.from_word(w) for w in words];rr=[b.from_word(w) for w in words];ca={};cb={}
        for phase in range(3):
            indices=list(range(len(words)))
            if phase:rng.shuffle(indices);indices+=indices[:2]
            alive=set(labels) if phase<2 else {g for g in labels if rng.randrange(3)}
            current=plan_batch(a,[roots[i] for i in indices],alive,ca)
            previous=old_plan.plan_batch(b,[rr[i] for i in indices],alive,cb)
            assert current==previous==literal_plan([words[i] for i in indices],alive);planner_comparisons+=1
    large=[]
    for n in (128,256,512):
        pd=Diagram.from_braid(n+1,list(range(1,n+1))).pd
        before=old_group.group_decide(old.Diagram.from_pd(pd),elimination_batch=True,seconds=None,max_work=2000000)
        after=group_decide(Diagram.from_pd(pd),elimination_batch=True,seconds=None,max_work=2000000)
        assert after['status']=='UNKNOT'
        for item in (before,after):
            if 'certificate' in item:
                for compressed in (False,True):assert verify_group_certificate(Diagram.from_pd(pd),item['certificate'],compressed=compressed,max_letters=2000000,max_work=20000000)
        large.append(dict(crossings=n,pd=pd,old=before,current=after))
    result.update(direct_prior_comparisons=comparisons,direct_prior_results_identical=True,planner_comparisons=planner_comparisons,large_source_trials=large,
        unchanged_modules=['elimination_batch_verify','compressed_group','compressed_words'],unchanged_functions=['apply_batch','_presentation','_reduce','verify_group_certificate'],
        scope='Same direct greedy witnesses and independent replay, with incremental exact reachability. The host separates source recovery from a 50000-work continuation cap inside a total quarter-budget trial. Common 80-diagram results and larger source-bound circle trials are recorded separately; finite-budget outcomes need not agree universally.')
    return result


def checked_direct(d,**options):
    prior=options.pop('_prior',None)
    producer=prior[0].compressed_certificate if prior else compressed_certificate
    verifier=prior[1].verify_group_certificate if prior else verify_group_certificate
    local_limit=prior[1].GroupLimit if prior else GroupLimit
    start=time.perf_counter();stats={};seconds=options.get('seconds',20)
    def check():
        if seconds is not None and time.perf_counter()-start>seconds:raise GroupLimit('direct local allowance exhausted')
    try:
        c=producer(d,elimination_batch=True,relator_moves=options.get('relator_moves',False),max_work=options['max_work'],check=check,stats=stats)
        if c:
            assert verifier(d,c,compressed=True,max_work=options['max_work'],check=check)
            return dict(status='UNKNOT',certificate=c,search_stats=stats)
        return dict(status='INCONCLUSIVE',search_stats=stats)
    except (GroupLimit,local_limit) as exc:return dict(status='INCONCLUSIVE',reason=str(exc),search_stats=stats)


def benchmark(old,old_search,old_group,hashes,stage=False):
    if stage:
        base=dict(old_direct=(old.Diagram,lambda d,**kw: checked_direct(d,_prior=(old_search,old_group),**kw),{}),direct=(Diagram,checked_direct,{}),old_portfolio=(old.Diagram,old_group.group_decide,dict(elimination_batch=True)),portfolio=(Diagram,group_decide,dict(elimination_batch=True)))
        inputs=[dict(name=f'circle-{n}',crossings=n,pd=Diagram.from_braid(n+1,list(range(1,n+1))).pd,expected='UNKNOT') for n in (8,16,32,64,128,256,512)]
        common=dict(seconds=20,max_work=20000000,compressed_search=True)
    else:
        base=dict(old=(old.Diagram,old.recognize,{}),current=(Diagram,recognize,{}),old_portfolio=(old.Diagram,old.recognize,dict(group_elimination_batch=True)),portfolio=(Diagram,recognize,dict(group_elimination_batch=True)))
        inputs=harness.corpus();common=dict(use_group=True,group_relators=True,group_compressed_search=True,group_seconds=10,group_max_work=20000000,seconds=12,max_objects=50000)
    functions={arm+suffix:fn for arm,fn in base.items() for suffix in ('','_AA')}
    rng=random.Random(SEED+(2 if stage else 1));rows=[];proofs={}
    for source in inputs:
        samples=[];warmups=[]
        for iteration in range(-1,5):
            order=list(functions);rng.shuffle(order);measurements={}
            for arm in order:
                diagram,fn,extra=functions[arm];start=time.perf_counter();result=fn(diagram.from_pd(source['pd']),**common,**extra);elapsed=time.perf_counter()-start
                status=result['status'] if stage else result.status;complete=status in ('UNKNOT','KNOTTED')
                if complete:assert status==source['expected']
                groups=[]
                for group in ([result] if stage else stage_records(result.evidence)):
                    record={k:v for k,v in group.items() if k!='certificate'}
                    if 'certificate' in group:
                        c=group['certificate'];raw=encode(c);key=sha256(raw).hexdigest();proofs[key]=c
                        record.update(certificate_sha256=key,certificate_bytes=len(raw),certificate_version=c['version'])
                    groups.append(record)
                measurements[arm]=dict(seconds=elapsed,status=status,completed=complete,groups=groups)
            (warmups if iteration<0 else samples).append(dict(order=order,measurements=measurements))
        medians={arm:median([s['measurements'][arm]['seconds'] for s in samples if s['measurements'][arm]['completed']]) if any(s['measurements'][arm]['completed'] for s in samples) else None for arm in functions}
        pairs=([('direct','old_direct','direct'),('portfolio','old_portfolio','portfolio')] if stage else [('current','old','current'),('portfolio','old_portfolio','portfolio'),('versus_default','current','portfolio')])+[(arm+'_AA',arm,arm+'_AA') for arm in base]
        ratios=harness.ratios(samples,pairs);rows.append(dict(source=source,samples=samples,warmups=warmups,medians=medians,paired_ratios=ratios))
        print(source['name'],json.dumps(dict(medians=medians,ratios=ratios)),flush=True)
    return dict(cases=rows,certificates=proofs,baseline_source_sha256=hashes,measured_calls=len(inputs)*5*len(functions),warmup_calls=len(inputs)*len(functions),completed_calls=sum(m['completed'] for r in rows for s in r['samples'] for m in s['measurements'].values()),
        scope=('Checked group stage on actual circles, including production and source replay; earlier simplification bypassed. Prior/current direct batching and phase-aware portfolios measured separately. ' if stage else 'Complete recognition on fresh PDs including mandatory source replay; old/current defaults and old/current elimination portfolios. ')+ 'Full pinned prior package and A/A controls, five shuffled measured rounds; all incomplete outcomes retained.')


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('mode',choices=('audit','benchmark','stages'));parser.add_argument('--output',required=True,type=Path);args=parser.parse_args();before=sources();start=time.perf_counter()
    with tempfile.TemporaryDirectory(prefix='unknot-elimination-baseline-') as directory:
        harness.BASELINE=BASELINE;old=harness.baseline(directory);result=audit(*old) if args.mode=='audit' else benchmark(*old,stage=args.mode=='stages')
    assert before==sources()
    result.update(mode=args.mode,baseline_commit=BASELINE,seed=SEED+(0 if args.mode=='audit' else 2 if args.mode=='stages' else 1),seconds=time.perf_counter()-start,python=platform.python_version(),platform=platform.platform(),source_sha256=before,source_hashes_unchanged=True)
    args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(json.dumps(json_safe(result),indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('cases','certificates','capacity','source_sha256','baseline_source_sha256')},indent=2))


if __name__=='__main__':main()
