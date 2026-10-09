"""Pinned three-mode certificate equivalence and complete planner measurements."""
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
from fastunknot.group_certificate import verify_group_certificate, group_decide
from fastunknot.compressed_words import WordArena
from fastunknot.primitive_projection import plan_projection
from fastunknot.primitive_forest import plan_forest
from fastunknot.integer_codec import json_safe
from cyclic_overlap_research.native import stage_records

BASELINE='b5b0ae50c4e4456f2ee8df2e8ce8587d68d0d329';SEED=261008507
harness.BASELINE=BASELINE


def sources():
    paths=list((ROOT/'fastunknot').rglob('*.py'))+[Path(__file__).resolve(),Path(harness.__file__),
        ROOT/'tests/test_primitive_planner.py',ROOT/'tests/test_primitive_projection.py',ROOT/'tests/test_primitive_forest.py',
        ROOT/'cyclic_overlap_research/native.py',harness.CORPUS]
    return {str(p.relative_to(ROOT.parent)):sha256(p.read_bytes()).hexdigest() for p in paths}


def encode(c):return json.dumps(json_safe(c),sort_keys=True,separators=(',',':')).encode()


def plans(old_search):
    old_pair=importlib.import_module(old_search.__package__+'.primitive_projection').plan_projection
    old_forest=importlib.import_module(old_search.__package__+'.primitive_forest').plan_forest
    rng=random.Random(SEED);comparisons=0
    for index in range(200):
        arena=WordArena(max_work=20000000);words=[]
        for _ in range(10):
            if rng.random()<.6:
                a,b=rng.sample(range(1,9),2);sign=rng.choice((-1,1))
                w=[a]*rng.randrange(1,8)+[b*sign];words.append(w*rng.randrange(1,4))
            else:words.append([rng.choice((-8,-7,-6,-5,-4,-3,-2,-1,1,2,3,4,5,6,7,8)) for _ in range(rng.randrange(18))])
        roots=[arena.from_word(w) for w in words];roots.extend((0,roots[0],roots[2]));old_cache={};new_cache={}
        for phase in range(5):
            rng.shuffle(roots);alive=set(rng.sample(range(1,9),rng.randrange(2,9)))
            assert old_forest(arena,roots,alive,old_cache)==plan_forest(arena,roots,alive,new_cache)
            assert old_pair(arena,roots,alive,old_cache)==plan_projection(arena,roots,alive,new_cache)
            comparisons+=2
    return dict(states=1000,planner_comparisons=comparisons,seed=SEED,scope='Arbitrary raw words and changing slots/live sets test planning equivalence only; no knot verdict.')


def audit(old,old_search,old_group,hashes):
    for name in ('compressed_words','group_certificate','compressed_group','recognize','primitive_power_verify','primitive_projection_verify','primitive_forest_verify'):
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
        all_certificates_and_nondecisions_identical=True,plans=plans(old_search),baseline_source_sha256=hashes,
        scope='Three source-bound modes on actual validated PDs against the entire pinned prior package. Every positive passes both full independent replayers. All verifier/host/word modules are byte-identical to baseline. Shared-budget exhaustion can differ because charged or elapsed work changes; no stronger discovery claim.')


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


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('mode',choices=('audit','benchmark','stages'));parser.add_argument('--output',required=True,type=Path);args=parser.parse_args()
    before=sources();start=time.perf_counter()
    with tempfile.TemporaryDirectory(prefix='unknot-planner-baseline-') as directory:
        old=harness.baseline(directory)
        result=audit(*old) if args.mode=='audit' else benchmark(*old,stage=args.mode=='stages')
    assert before==sources()
    result.update(mode=args.mode,baseline_commit=BASELINE,seed=SEED+(0 if args.mode=='audit' else 1 if args.mode=='benchmark' else 2),seconds=time.perf_counter()-start,
        python=platform.python_version(),platform=platform.platform(),source_sha256=before,source_hashes_unchanged=True)
    args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(json.dumps(json_safe(result),indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('cases','certificates','source_sha256','baseline_source_sha256')},indent=2))


if __name__=='__main__':main()
