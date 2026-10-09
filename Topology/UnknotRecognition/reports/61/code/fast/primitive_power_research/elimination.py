"""Source-bound acyclic elimination audits and controlled portfolio timings."""
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
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from primitive_power_research import forests as harness
from fastunknot import Diagram, DiagramError, recognize
from fastunknot.compressed_search import compressed_certificate
from fastunknot.group_certificate import group_decide, verify_group_certificate, GroupLimit
from fastunknot.integer_codec import json_safe
from fastunknot.elimination_batch import apply_batch
from fastunknot.elimination_batch_verify import replay_compressed_batch
from cyclic_overlap_research.native import stage_records
from test_elimination_batch import tower
BASELINE='3346396cd135b1c03a27f51fa96aee278641baf2';SEED=261008514
harness.BASELINE=BASELINE


def sources():
    paths=list((ROOT/'fastunknot').rglob('*.py'))+[Path(__file__),Path(harness.__file__),ROOT/'tests/test_elimination_batch.py',ROOT/'cyclic_overlap_research/native.py',harness.CORPUS]
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
    inputs=list(harness.corpus());rng=random.Random(261008504)
    for i in range(240):
        strands=rng.randrange(2,6);word=[rng.choice((-1,1))*rng.randrange(1,strands) for _ in range(rng.randrange(1,15))]
        try:d=Diagram.from_braid(strands,word)
        except DiagramError:continue
        inputs.append(dict(name=f'random-{i}',pd=d.pd))
    for strands in (4,5,9,17,33,65):inputs.append(dict(name=f'stabilized-circle-{strands}',pd=Diagram.from_braid(strands,list(range(1,strands))).pd))
    rows=[];proofs={}
    def keep(d,c):
        if c is None:return None
        for compressed in (False,True):assert verify_group_certificate(d,c,compressed=compressed,max_work=20000000)
        key=sha256(encode(c)).hexdigest();proofs[key]=c;return key
    for source in inputs:
        d=Diagram.from_pd(source['pd']);od=old.Diagram.from_pd(source['pd']);modes={}
        for name,extra in (('default',{}),('projection',dict(primitive_projection=True)),('forest',dict(primitive_forest=True))):
            opts=dict(relator_moves=True,max_work=20000000,**extra)
            prior=old_search.compressed_certificate(od,**opts);current=compressed_certificate(d,**opts);assert prior==current
            modes[name]=keep(d,current)
        stats={};reason=None
        try:direct=compressed_certificate(d,elimination_batch=True,relator_moves=True,max_work=2000000,stats=stats)
        except GroupLimit as exc:direct=None;reason=str(exc)
        direct_key=keep(d,direct)
        host=group_decide(d,elimination_batch=True,relator_moves=True,max_work=2000000,seconds=None)
        key=keep(d,host.pop('certificate',None))
        if key and not modes['default']:assert recognize(Diagram.from_pd(source['pd']),seconds=30).status=='UNKNOT'
        rows.append(dict(source=source,legacy_modes=modes,direct=dict(certificate_sha256=direct_key,reason=reason,stats=stats),portfolio=dict(certificate_sha256=key,result=host)))
    return dict(cases=rows,certificates=proofs,diagrams=len(rows),legacy_mode_comparisons=3*len(rows),legacy_results_identical=True,
        direct_positives=sum(bool(r['direct']['certificate_sha256']) for r in rows),portfolio_positives=sum(bool(r['portfolio']['certificate_sha256']) for r in rows),
        direct_lost_default=sum(bool(r['legacy_modes']['default'] and not r['direct']['certificate_sha256']) for r in rows),
        portfolio_lost_default=sum(bool(r['legacy_modes']['default'] and not r['portfolio']['certificate_sha256']) for r in rows),
        portfolio_new_default=sum(bool(not r['legacy_modes']['default'] and r['portfolio']['certificate_sha256']) for r in rows),capacity=capacity(),baseline_source_sha256=hashes,
        scope='Actual validated PDs; old modes exactly preserved. Every positive has literal and compressed source replay. Direct batch search can lose discovery; the host caps its trial at min(max_work//4,50000), charges/reserves its work and falls back to the original source. Finite shared allowances do not guarantee identical coverage universally.')


def checked_direct(d,**options):
    start=time.perf_counter();stats={};seconds=options.get('seconds',20)
    def check():
        if seconds is not None and time.perf_counter()-start>seconds:raise GroupLimit('direct local allowance exhausted')
    try:
        c=compressed_certificate(d,elimination_batch=True,relator_moves=options.get('relator_moves',False),max_work=options['max_work'],check=check,stats=stats)
        if c:
            assert verify_group_certificate(d,c,compressed=True,max_work=options['max_work'],check=check)
            return dict(status='UNKNOT',certificate=c,search_stats=stats)
        return dict(status='INCONCLUSIVE',search_stats=stats)
    except GroupLimit as exc:return dict(status='INCONCLUSIVE',reason=str(exc),search_stats=stats)


def benchmark(old,old_search,old_group,hashes,stage=False):
    if stage:
        base=dict(old=(old.Diagram,old_group.group_decide,{}),old_forest=(old.Diagram,old_group.group_decide,dict(primitive_forest=True)),direct=(Diagram,checked_direct,{}),portfolio=(Diagram,group_decide,dict(elimination_batch=True)))
        inputs=[dict(name=f'circle-{n}',crossings=n,pd=Diagram.from_braid(n+1,list(range(1,n+1))).pd,expected='UNKNOT') for n in (8,16,32,64,128,256)]
        common=dict(seconds=20,max_work=20000000,compressed_search=True)
    else:
        base=dict(old=(old.Diagram,old.recognize,{}),current=(Diagram,recognize,{}),portfolio=(Diagram,recognize,dict(group_elimination_batch=True)))
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
        pairs=([('direct','old','direct'),('portfolio','old','portfolio'),('versus_forest','old_forest','direct')] if stage else [('current','old','current'),('portfolio','old','portfolio')])+[(arm+'_AA',arm,arm+'_AA') for arm in base]
        ratios=harness.ratios(samples,pairs);rows.append(dict(source=source,samples=samples,warmups=warmups,medians=medians,paired_ratios=ratios))
        print(source['name'],json.dumps(dict(medians=medians,ratios=ratios)),flush=True)
    return dict(cases=rows,certificates=proofs,baseline_source_sha256=hashes,measured_calls=len(inputs)*5*len(functions),warmup_calls=len(inputs)*len(functions),completed_calls=sum(m['completed'] for r in rows for s in r['samples'] for m in s['measurements'].values()),
        scope=('Checked group stage on actual circles, including production and source replay; earlier simplification bypassed. Direct batching and capped portfolio measured separately. ' if stage else 'Complete recognition on fresh PDs including mandatory source replay; default and optional capped elimination portfolio. ')+ 'Full pinned prior package and A/A controls, five shuffled measured rounds; all incomplete outcomes retained.')


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('mode',choices=('audit','benchmark','stages'));parser.add_argument('--output',required=True,type=Path);args=parser.parse_args();before=sources();start=time.perf_counter()
    with tempfile.TemporaryDirectory(prefix='unknot-elimination-baseline-') as directory:
        old=harness.baseline(directory);result=audit(*old) if args.mode=='audit' else benchmark(*old,stage=args.mode=='stages')
    assert before==sources()
    result.update(mode=args.mode,baseline_commit=BASELINE,seed=SEED+(0 if args.mode=='audit' else 2 if args.mode=='stages' else 1),seconds=time.perf_counter()-start,python=platform.python_version(),platform=platform.platform(),source_sha256=before,source_hashes_unchanged=True)
    args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(json.dumps(json_safe(result),indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('cases','certificates','capacity','source_sha256','baseline_source_sha256')},indent=2))


if __name__=='__main__':main()
