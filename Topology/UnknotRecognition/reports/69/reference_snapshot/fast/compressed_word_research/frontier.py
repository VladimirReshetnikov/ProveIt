"""Exact word-cache frontier audits, kernels and whole-recognition timings."""
import argparse
from copy import deepcopy
from hashlib import sha256
import importlib
from itertools import product
import json
from pathlib import Path
import platform
import random
from statistics import median
import sys
import tempfile
import time
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from primitive_power_research import projections as loader, forests as harness
from fastunknot import Diagram, DiagramError, recognize
from fastunknot.compressed_search import compressed_certificate
from fastunknot.group_certificate import group_decide, verify_group_certificate, GroupLimit
from fastunknot.compressed_words import WordArena, CompressedLimit
from fastunknot.integer_codec import json_safe
from cyclic_overlap_research.native import stage_records
from test_compressed_words import explicit_reduce, inflated_certificate
from test_primitive_projection import inflated_source
BASELINE='4cef49dffbc300ea5a6ae82d9aec4b1eadad637c';SEED=261008519


def sources():
    paths=list((ROOT/'fastunknot').rglob('*.py'))+[Path(__file__),Path(loader.__file__),Path(harness.__file__),
        ROOT/'tests/test_word_cache_frontier.py',ROOT/'tests/test_compressed_words.py',ROOT/'tests/test_primitive_projection.py',
        ROOT/'tests/test_primitive_forest.py',ROOT/'hard_unknots.py',ROOT/'cyclic_overlap_research/native.py',harness.CORPUS]
    return {str(p.relative_to(ROOT.parent)):sha256(p.read_bytes()).hexdigest() for p in paths}


def encode(c):return json.dumps(json_safe(c),sort_keys=True,separators=(',',':')).encode()


def baseline(directory):
    loader.BASELINE=BASELINE;old,search,hashes=loader.baseline(directory)
    group=importlib.import_module(search.__package__+'.group_certificate')
    changed=[name for name,h in hashes.items() if h!=sha256((ROOT/'fastunknot'/name).read_bytes()).hexdigest()]
    assert changed==['compressed_words.py'],changed
    return old,search,group,hashes


def audit(old,old_search,old_group,hashes):
    words=0
    for length in range(8):
        for word in product((1,-1,2,-2),repeat=length):
            a=WordArena();b=old_search.WordArena();u=a.from_word(word);v=b.from_word(word)
            for op,expected in (('inverse',[-x for x in reversed(word)]),('reduce',explicit_reduce(word)),('cyclic_reduce',explicit_reduce(word,True))):
                assert a.expand(getattr(a,op)(u))==b.expand(getattr(b,op)(v))==expected
            words+=1
    inputs=list(harness.corpus());rng=random.Random(261008504)
    for i in range(240):
        strands=rng.randrange(2,6);word=[rng.choice((-1,1))*rng.randrange(1,strands) for _ in range(rng.randrange(1,15))]
        try:d=Diagram.from_braid(strands,word)
        except DiagramError:continue
        inputs.append(dict(name=f'random-{i}',pd=d.pd))
    for strands in (4,5,9,17,33,65):inputs.append(dict(name=f'stabilized-circle-{strands}',pd=Diagram.from_braid(strands,list(range(1,strands))).pd))
    rows=[];proofs={}
    def keep(source,c):
        if c is None:return None
        for diagram,verify in ((Diagram,verify_group_certificate),(old.Diagram,old_group.verify_group_certificate)):
            for compressed in (False,True):assert verify(diagram.from_pd(source['pd']),c,compressed=compressed,max_letters=2000000,max_work=20000000)
        key=sha256(encode(c)).hexdigest();proofs[key]=c;return key
    for source in inputs:
        modes={}
        for name,extra in (('default',{}),('projection',dict(primitive_projection=True)),('forest',dict(primitive_forest=True)),('direct_batch',dict(elimination_batch=True)),('portfolio',dict(elimination_batch=True))):
            records={}
            for label,diagram,search,group in (('old',old.Diagram,old_search.compressed_certificate,old_group),('current',Diagram,compressed_certificate,sys.modules[group_decide.__module__])):
                d=diagram.from_pd(source['pd']);stats={};reason=None
                if name=='portfolio':
                    outcome=group.group_decide(d,seconds=None,max_work=2000000,relator_moves=True,**extra)
                    c=outcome.pop('certificate',None);records[label]=dict(certificate_sha256=keep(source,c),result=outcome)
                else:
                    try:c=search(d,max_work=2000000 if name=='direct_batch' else 20000000,relator_moves=True,stats=stats,**extra)
                    except group.GroupLimit as exc:c=None;reason=str(exc)
                    records[label]=dict(certificate_sha256=keep(source,c),stats=stats,reason=reason)
            records['identical']=records['old']['certificate_sha256']==records['current']['certificate_sha256'];modes[name]=records
        rows.append(dict(source=source,modes=modes))
    supplied=[]
    for kind,size in (('whitehead',4),('whitehead',8),('projection',4),('projection',8),('projection',1024)):
        d,c=inflated_certificate(size) if kind=='whitehead' else inflated_source(size)
        for package,group in ((old,old_group),(sys.modules[Diagram.__module__.split('.')[0]],sys.modules[group_decide.__module__])):
            for compressed in ((False,True) if size<=8 else (True,)):
                assert group.verify_group_certificate(package.Diagram.from_pd(d.pd),c,compressed=compressed,max_letters=2000000,max_work=20000000)
                bad=deepcopy(c);bad['input_pd'][0][0]+=1
                assert not group.verify_group_certificate(package.Diagram.from_pd(d.pd),bad,compressed=compressed,max_work=20000000)
        key=sha256(encode(c)).hexdigest();proofs[key]=c;supplied.append(dict(kind=kind,size=size,pd=d.pd,certificate_sha256=key))
    return dict(cases=rows,certificates=proofs,diagrams=len(rows),mode_comparisons=5*len(rows),identical_outcomes=sum(v['identical'] for r in rows for v in r['modes'].values()),
        changed_outcomes=[dict(name=r['source']['name'],mode=k) for r in rows for k,v in r['modes'].items() if not v['identical']],
        word_oracles=dict(words=words,operations=3*words),supplied_proofs=supplied,baseline_source_sha256=hashes,
        scope='Five source-bound modes against the entire pinned prior package. Every positive passes old/current literal and compressed replay. Exhaustive short-word oracles and source rebinding tests supplement the independently implemented move checkers. Only the shared word engine changes; finite budget outcomes and allocation-dependent heuristics need not agree universally.')


def benchmark(old,old_search,old_group,hashes):
    base=dict(old=(old.Diagram,old.recognize,{}),current=(Diagram,recognize,{}),old_portfolio=(old.Diagram,old.recognize,dict(group_elimination_batch=True)),portfolio=(Diagram,recognize,dict(group_elimination_batch=True)))
    functions={arm+suffix:fn for arm,fn in base.items() for suffix in ('','_AA')}
    common=dict(use_group=True,group_relators=True,group_compressed_search=True,group_seconds=10,group_max_work=20000000,seconds=12,max_objects=50000)
    rng=random.Random(SEED+1);rows=[];proofs={}
    for source in harness.corpus():
        samples=[];warmups=[]
        for iteration in range(-1,5):
            order=list(functions);rng.shuffle(order);measurements={}
            for arm in order:
                diagram,fn,extra=functions[arm];start=time.perf_counter();result=fn(diagram.from_pd(source['pd']),**common,**extra);elapsed=time.perf_counter()-start
                complete=result.status in ('UNKNOT','KNOTTED')
                if complete:assert result.status==source['expected']
                groups=[]
                for group in stage_records(result.evidence):
                    record={k:v for k,v in group.items() if k!='certificate'}
                    if 'certificate' in group:
                        c=group['certificate'];raw=encode(c);key=sha256(raw).hexdigest();proofs[key]=c
                        record.update(certificate_sha256=key,certificate_bytes=len(raw),certificate_version=c['version'])
                    groups.append(record)
                measurements[arm]=dict(seconds=elapsed,status=result.status,completed=complete,groups=groups)
            (warmups if iteration<0 else samples).append(dict(order=order,measurements=measurements))
        medians={arm:median([s['measurements'][arm]['seconds'] for s in samples if s['measurements'][arm]['completed']]) if any(s['measurements'][arm]['completed'] for s in samples) else None for arm in functions}
        pairs=[('current','old','current'),('portfolio','old_portfolio','portfolio')]+[(arm+'_AA',arm,arm+'_AA') for arm in base]
        ratios=harness.ratios(samples,pairs);rows.append(dict(source=source,samples=samples,warmups=warmups,medians=medians,paired_ratios=ratios))
        print(source['name'],json.dumps(dict(medians=medians,ratios=ratios)),flush=True)
    return dict(cases=rows,certificates=proofs,baseline_source_sha256=hashes,measured_calls=len(rows)*40,warmup_calls=len(rows)*8,completed_calls=sum(m['completed'] for r in rows for s in r['samples'] for m in s['measurements'].values()),scope='Complete fresh-PD recognition including mandatory source reconstruction and replay. Prior/current defaults and adaptive batch hosts with A/A controls; five shuffled measured rounds, all incomplete outcomes retained.')


def word_case(arena_type,kind,size):
    a=arena_type(max_nodes=200000,max_work=50000000)
    root=a.from_word([1,2]);operation='inverse' if kind.startswith('inverse') else 'reduce'
    if kind.endswith('power'):root=a.power(root,1<<size)
    getattr(a,operation)(root)
    count=128 if kind.endswith('power') else size
    for i in range(count):
        root=a.concat(root,a.letter(1+i%2));out=getattr(a,operation)(root)
    return a,root,out


def kernels(old,old_search,old_group,hashes):
    rng=random.Random(SEED+2);rows=[];proofs={};arms=('old','current','old_AA','current_AA')
    cases=[(kind,size) for kind in ('inverse-chain','reduce-chain') for size in (64,256,1024,2048)]
    cases += [(kind,size) for kind in ('inverse-power','reduce-power') for size in (1024,4096)]
    cases += [('source-proof',size) for size in (64,256,1024)]
    for kind,size in cases:
        supplied=inflated_source(size) if kind=='source-proof' else None
        if supplied:
            d,c=supplied;key=sha256(encode(c)).hexdigest();proofs[key]=c
        samples=[];warmups=[]
        for iteration in range(-1,5):
            order=list(arms);rng.shuffle(order);measurements={}
            for arm in order:
                prior=arm.startswith('old');start=time.perf_counter();stats={};reason=None
                try:
                    if supplied:
                        group=old_group if prior else sys.modules[group_decide.__module__];diagram=old.Diagram if prior else Diagram
                        complete=group.verify_group_certificate(diagram.from_pd(d.pd),c,compressed=True,max_work=50000000,max_nodes=200000,stats=stats)
                        assert complete
                        elapsed=time.perf_counter()-start;record=dict(stats=stats,certificate_sha256=key)
                    else:
                        a,root,out=word_case(old_search.WordArena if prior else WordArena,kind,size)
                        elapsed=time.perf_counter()-start;complete=True;record=dict(stats=dict(a.stats),nodes=len(a.rules)-1,output_length_bits=a.lengths[out].bit_length())
                        # Bounded literal checking is outside the measured kernel.
                        if kind.endswith('chain'):
                            expected=[1,2]+[1+i%2 for i in range(size)]
                            if kind.startswith('inverse'):expected=[-x for x in reversed(expected)]
                            assert a.expand(out,limit=10000)==expected
                        else:
                            assert a.lengths[out]==(2<<size)+128
                            if kind.startswith('inverse'):assert a.inverse(out)==root
                            else:assert out==root
                except (CompressedLimit,GroupLimit,old_group.GroupLimit,old_search.CompressedLimit) as exc:
                    elapsed=time.perf_counter()-start;complete=False;reason=str(exc);record=dict(stats=stats)
                measurements[arm]=dict(seconds=elapsed,completed=complete,reason=reason,**record)
            (warmups if iteration<0 else samples).append(dict(order=order,measurements=measurements))
        medians={arm:median([s['measurements'][arm]['seconds'] for s in samples if s['measurements'][arm]['completed']]) if any(s['measurements'][arm]['completed'] for s in samples) else None for arm in arms}
        ratios=harness.ratios(samples,[('current','old','current'),('old_AA','old','old_AA'),('current_AA','current','current_AA')])
        rows.append(dict(kind=kind,size=size,samples=samples,warmups=warmups,medians=medians,paired_ratios=ratios));print(kind,size,json.dumps(dict(medians=medians,ratios=ratios)),flush=True)
    return dict(cases=rows,certificates=proofs,baseline_source_sha256=hashes,measured_calls=len(rows)*20,warmup_calls=len(rows)*4,completed_calls=sum(m['completed'] for r in rows for s in r['samples'] for m in s['measurements'].values()),scope='Fresh arena construction and repeated word queries, with bounded literal assertions after timing. Power cases have huge represented length and no expansion. Source-proof cases time full independent reconstruction and replay of a fixed supplied certificate, not proof discovery. Four shuffled arms, five measured rounds and one warm-up; all incomplete outcomes retained.')


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('mode',choices=('audit','benchmark','kernels'));p.add_argument('--output',type=Path,required=True);args=p.parse_args()
    before=sources();start=time.perf_counter()
    with tempfile.TemporaryDirectory(prefix='unknot-word-frontier-') as directory:
        prior=baseline(directory);result={'audit':audit,'benchmark':benchmark,'kernels':kernels}[args.mode](*prior)
    assert before==sources()
    result.update(mode=args.mode,baseline_commit=BASELINE,seed=SEED+{'audit':0,'benchmark':1,'kernels':2}[args.mode],seconds=time.perf_counter()-start,python=platform.python_version(),platform=platform.platform(),source_sha256=before,source_hashes_unchanged=True)
    args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(json.dumps(json_safe(result),indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('cases','certificates','source_sha256','baseline_source_sha256')},indent=2))


if __name__=='__main__':main()
