"""Bounded-run normalization audits, full recognition and source replay timings."""
import argparse
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
from fastunknot.group_certificate import verify_group_certificate, group_decide, GroupLimit
from fastunknot.compressed_words import WordArena
from fastunknot.integer_codec import json_safe
from cyclic_overlap_research.native import stage_records

BASELINE='483b7397a1086206bc463222094315390c42550d';SEED=261008508
harness.BASELINE=BASELINE


def sources():
    paths=list((ROOT/'fastunknot').rglob('*.py'))+[Path(__file__).resolve(),Path(harness.__file__),
        ROOT/'tests/test_primitive_planner.py',ROOT/'tests/test_syllable_normalize.py',ROOT/'tests/test_primitive_projection.py',ROOT/'tests/test_primitive_forest.py',
        ROOT/'cyclic_overlap_research/native.py',harness.CORPUS]
    return {str(p.relative_to(ROOT.parent)):sha256(p.read_bytes()).hexdigest() for p in paths}


def encode(c):return json.dumps(json_safe(c),sort_keys=True,separators=(',',':')).encode()


def normalization_audit():
    from itertools import product
    from fastunknot.syllable_normalize import bounded_cyclic_roots
    from fastunknot.syllable_normalize_verify import replay_cyclic_roots
    from test_syllable_normalize import literal
    counts=dict(words=0,hits=0,declined=0)
    for length in range(9):
        for word in product((1,-1,2,-2),repeat=length):
            a=WordArena();root=a.from_word(word)
            before=len(a.rules);left=bounded_cyclic_roots(a,[root],min_length=0)
            if left is None:assert before==len(a.rules)
            right=replay_cyclic_roots(a,[root],min_length=0)
            assert (left is None)==(right is None)
            if left is not None:
                assert a.expand(left[0])==a.expand(right[0])==literal(word)
            counts['words']+=1;counts['hits']+=left is not None;counts['declined']+=left is None
    return dict(**counts,scope='All signed rank-two words through length eight, literal reduction and independently implemented run evaluation. A declined bounded probe is not a negative equality or knot claim.')


def audit(old,old_search,old_group,hashes):
    for name in ('compressed_words','group_certificate','recognize','primitive_projection','primitive_forest','primitive_power_verify','primitive_projection_verify','primitive_forest_verify'):
        assert hashes[name+'.py']==sha256((ROOT/'fastunknot'/f'{name}.py').read_bytes()).hexdigest(),name
    inputs=list(harness.corpus());rng=random.Random(261008504)
    for i in range(240):
        strands=rng.randrange(2,6);word=[rng.choice((-1,1))*rng.randrange(1,strands) for _ in range(rng.randrange(1,15))]
        try:d=Diagram.from_braid(strands,word)
        except DiagramError:continue
        inputs.append(dict(name=f'random-{i}',pd=d.pd))
    for strands in (4,5,9,17,33,65):inputs.append(dict(name=f'stabilized-circle-{strands}',pd=Diagram.from_braid(strands,list(range(1,strands))).pd))
    rows=[];proofs={}
    modes=dict(default={},projection=dict(primitive_projection=True),forest=dict(primitive_forest=True))
    for source in inputs:
        d=Diagram.from_pd(source['pd']);od=old.Diagram.from_pd(source['pd']);m={}
        for mode,extra in modes.items():
            opts=dict(relator_moves=True,max_work=20000000,**extra);before_stats={};after_stats={}
            before=old_search.compressed_certificate(od,stats=before_stats,**opts)
            after=compressed_certificate(d,stats=after_stats,**opts);assert before==after
            key=None
            if after:
                key=sha256(encode(after)).hexdigest();proofs[key]=after
                for compressed in (False,True):assert verify_group_certificate(d,after,compressed=compressed,max_work=20000000)
            m[mode]=dict(certificate_sha256=key,old_stats=before_stats,new_stats=after_stats)
        rows.append(dict(source=source,modes=m))
    return dict(cases=rows,certificates=proofs,diagrams=len(rows),mode_comparisons=3*len(rows),
        positive_mode_results=sum(bool(v['certificate_sha256']) for r in rows for v in r['modes'].values()),
        all_certificates_and_nondecisions_identical=True,normalization=normalization_audit(),baseline_source_sha256=hashes,
        scope='Three source-bound modes on actual validated PDs against the entire pinned prior package. Every positive passes both full independent replayers. Existing arithmetic/move kernels, host and word implementation are byte-identical; normalization replay has a separate new evaluator. Shared-budget exhaustion can differ because charged or elapsed work changes; no stronger discovery claim.')


def benchmark(old,old_search,old_group,hashes,stage=False):
    functions={}
    for mode in ('projection','forest'):
        for prefix,diagram,fn in (('old_',old.Diagram,old_group.group_decide if stage else old.recognize),('',Diagram,group_decide if stage else recognize)):
            extra={('primitive_' if stage else 'group_primitive_')+mode:True}
            for suffix in ('','_AA'):functions[prefix+mode+suffix]=(diagram,fn,extra)
    common=(dict(seconds=20,max_work=20000000,compressed_search=True) if stage else
        dict(use_group=True,group_relators=True,group_compressed_search=True,group_seconds=10,group_max_work=20000000,seconds=12,max_objects=50000))
    inputs=([dict(name=f'circle-{r}',crossings=r,pd=Diagram.from_braid(r+1,list(range(1,r+1))).pd,expected='UNKNOT') for r in (8,16,32,64,128)] if stage else harness.corpus())
    rng=random.Random(SEED+(2 if stage else 1));rows=[];proofs={}
    for source in inputs:
        samples=[];warmups=[]
        for iteration in range(-1,5):
            order=list(functions);rng.shuffle(order);measurements={}
            for arm in order:
                diagram,fn,extra=functions[arm];opts=dict(common,**extra)
                start=time.perf_counter();result=fn(diagram.from_pd(source['pd']),**opts);elapsed=time.perf_counter()-start
                status=result['status'] if stage else result.status;complete=status in ('UNKNOT','KNOTTED')
                if complete:assert status==source['expected']
                records=[result] if stage else list(stage_records(result.evidence));groups=[]
                for group in records:
                    record={k:v for k,v in group.items() if k!='certificate'}
                    if 'certificate' in group:
                        c=group['certificate'];raw=encode(c);key=sha256(raw).hexdigest();proofs[key]=c
                        record.update(certificate_sha256=key,certificate_bytes=len(raw),certificate_version=c['version'])
                    groups.append(record)
                measurements[arm]=dict(seconds=elapsed,status=status,completed=complete,groups=groups)
            (warmups if iteration<0 else samples).append(dict(order=order,measurements=measurements))
        medians={arm:median([s['measurements'][arm]['seconds'] for s in samples if s['measurements'][arm]['completed']]) if any(s['measurements'][arm]['completed'] for s in samples) else None for arm in functions}
        pairs=[(mode,'old_'+mode,mode) for mode in ('projection','forest')]+[(arm+'_AA',arm,arm+'_AA') for arm in ('old_projection','projection','old_forest','forest')]
        q=harness.ratios(samples,pairs);rows.append(dict(source=source,samples=samples,warmups=warmups,medians=medians,paired_ratios=q))
        print(source['name'],json.dumps(dict(medians=medians,ratios=q)),flush=True)
    return dict(cases=rows,certificates=proofs,baseline_source_sha256=hashes,rounds=5,measured_calls=len(rows)*40,warmup_calls=len(rows)*8,
        completed_calls=sum(m['completed'] for r in rows for s in r['samples'] for m in s['measurements'].values()),
        scope=('Checked group stage only on actual stabilized circles, including fresh PD validation, production and mandatory replay; earlier simplification bypassed, not a whole-recognition gain. ' if stage else 'Complete fresh PD recognition including mandatory independent source reconstruction and replay. ')+
        'Eight shuffled arms compare previous/current projection and forest modes, each with A/A controls. Entire baseline package pinned; incomplete results retained and excluded from completed ratios.')


def kernels(old,old_search,old_group,hashes):
    from fastunknot.syllable_normalize import bounded_cyclic_roots
    from fastunknot.compressed_words import CompressedLimit
    from test_primitive_projection import inflated_source
    rng=random.Random(SEED+3);rows=[];proofs={}
    definitions=[(kind,bits) for kind in ('conjugate','source-replay') for bits in (16,64,256,1024,4096)]
    definitions += [('wide-cancellation',bits) for bits in (64,1024)]
    for kind,bits in definitions:
        source=None;certificate=None
        if kind=='source-replay':
            source,certificate=inflated_source(bits);key=sha256(encode(certificate)).hexdigest();proofs[key]=certificate
        samples=[];warmups=[]
        for iteration in range(-1,5):
            order=['old','old_AA','current','current_AA'];rng.shuffle(order);measurements={}
            for arm in order:
                stats={};prior=arm.startswith('old');start=time.perf_counter();reason=None;completed=False
                def check():
                    if time.perf_counter()-start>5:raise CompressedLimit('local five-second allowance exhausted')
                try:
                    if kind=='source-replay':
                        d=(old.Diagram if prior else Diagram).from_pd(source.pd)
                        verifier=old_group.verify_group_certificate if prior else verify_group_certificate
                        completed=verifier(d,certificate,compressed=True,max_work=20000000,check=check,stats=stats)
                        assert completed
                    else:
                        a=(old_search.WordArena if prior else WordArena)(max_work=20000000,check=check)
                        n=1<<bits
                        if kind=='conjugate':
                            p=a.power(a.letter(1),n);m=a.power(a.letter(2),n+3);q=a.power(a.letter(-1),n)
                            root=a.concat(a.concat(p,m),q)
                        else:
                            w=a.power(a.from_word([1,2]),n);root=a.concat(w,a.inverse(w))
                        result=None if prior else bounded_cyclic_roots(a,[root])
                        value=a.cyclic_reduce(root) if result is None else result[0]
                        if kind=='conjugate':assert a.uniform[value]==2 and a.lengths[value]==n+3
                        else:assert value==0
                        stats=dict(a.stats,nodes=len(a.rules)-1);completed=True
                except (CompressedLimit,old_search.CompressedLimit,GroupLimit,old_group.GroupLimit) as exc:reason=str(exc)
                measurements[arm]=dict(seconds=time.perf_counter()-start,completed=completed,stats=stats,reason=reason)
            (warmups if iteration<0 else samples).append(dict(order=order,measurements=measurements))
        medians={arm:median([s['measurements'][arm]['seconds'] for s in samples if s['measurements'][arm]['completed']]) if any(s['measurements'][arm]['completed'] for s in samples) else None for arm in order}
        q=harness.ratios(samples,[('current','old','current'),('old_AA','old','old_AA'),('current_AA','current','current_AA')])
        rows.append(dict(kind=kind,bits=bits,certificate_sha256=sha256(encode(certificate)).hexdigest() if certificate else None,samples=samples,warmups=warmups,medians=medians,paired_ratios=q))
        print(kind,bits,json.dumps(dict(medians=medians,ratios=q)),flush=True)
    return dict(cases=rows,certificates=proofs,baseline_source_sha256=hashes,rounds=5,measured_calls=len(rows)*20,warmup_calls=len(rows)*4,
        completed_calls=sum(m['completed'] for r in rows for s in r['samples'] for m in s['measurements'].values()),
        scope='Conjugate/wide rows are fresh grammar construction plus normalization kernels with fixed known results. Source-replay rows time complete fresh-PD reconstruction and verification of an explicitly supplied powered-prefix proof. Neither is a whole-recognition speedup or a claim of finding those prefixes. Five-second/20M-work caps; incomplete samples retained and excluded from completed ratios.')


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('mode',choices=('audit','benchmark','stages','kernels'));parser.add_argument('--output',required=True,type=Path);args=parser.parse_args()
    before=sources();start=time.perf_counter()
    with tempfile.TemporaryDirectory(prefix='unknot-planner-baseline-') as directory:
        old=harness.baseline(directory)
        result=audit(*old) if args.mode=='audit' else kernels(*old) if args.mode=='kernels' else benchmark(*old,stage=args.mode=='stages')
    assert before==sources()
    result.update(mode=args.mode,baseline_commit=BASELINE,seed=SEED+(0 if args.mode=='audit' else 1 if args.mode=='benchmark' else 3 if args.mode=='kernels' else 2),seconds=time.perf_counter()-start,
        python=platform.python_version(),platform=platform.platform(),source_sha256=before,source_hashes_unchanged=True)
    args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(json.dumps(json_safe(result),indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('cases','certificates','source_sha256','baseline_source_sha256')},indent=2))


if __name__=='__main__':main()
