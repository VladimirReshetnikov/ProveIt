"""Native report-45 arithmetic and source-bound terminal audit and timings."""
import argparse
from hashlib import sha256
import importlib
import json
from pathlib import Path
import platform
import random
from statistics import median
import subprocess
import sys
import time
from types import ModuleType, SimpleNamespace
from unittest.mock import patch

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from fastunknot import Diagram, DiagramError, recognize
from fastunknot import group_certificate as group_module
from fastunknot.compressed_search import compressed_certificate
from fastunknot.compressed_words import WordArena
from fastunknot.primitive_power import primitive_power_terminal
from fastunknot.primitive_power_verify import verify_compressed_terminal
from fastunknot.integer_codec import json_safe
from cyclic_overlap_research.native import stage_records

BASELINE='cd77d1bee8faa311054d4a7fdad856c65004d242'
REPORT=ROOT.parent/'reports/45/code'
CORPUS=ROOT.parent/'reports/46/repo_overlay/Topology/UnknotRecognition/fast/cyclic_overlap_research/results.json'
SEED=261008504


def sources():
    paths=list((ROOT/'fastunknot').glob('*.py'))+[Path(__file__).resolve(),ROOT/'tests/test_primitive_power.py',CORPUS]
    paths += [REPORT/name for name in ('christoffel.py','checker.py','oracle.py')]
    return {str(p.relative_to(ROOT.parent)):sha256(p.read_bytes()).hexdigest() for p in paths}


def baseline():
    package=ModuleType('_primitive_pinned');package.__path__=[str(ROOT/'fastunknot')]
    sys.modules[package.__name__]=package
    hashes={}
    for name in ('group_certificate','compressed_group','compressed_search'):
        path='Topology/UnknotRecognition/fast/fastunknot/'+name+'.py'
        raw=subprocess.check_output(['git','show',BASELINE+':'+path],cwd=ROOT)
        module=ModuleType(package.__name__+'.'+name);module.__package__=package.__name__
        sys.modules[module.__name__]=module
        exec(compile(raw,BASELINE+':'+path,'exec'),module.__dict__)
        hashes[name]=sha256(raw).hexdigest()
    for name in ('recognize','compressed_words','whitehead_power','relator_overlap',
                 'cyclic_overlap_index','compressed_overlap','compressed_match','compressed_lcs',
                 'compressed_endpoint','diagram'):
        path='Topology/UnknotRecognition/fast/fastunknot/'+name+'.py'
        raw=subprocess.check_output(['git','show',BASELINE+':'+path],cwd=ROOT)
        assert raw==(ROOT/'fastunknot'/f'{name}.py').read_bytes(),name
        hashes[name]=sha256(raw).hexdigest()
    return sys.modules[package.__name__+'.compressed_search'],sys.modules[package.__name__+'.group_certificate'],hashes


def delivered():
    package=ModuleType('_primitive_report45');package.__path__=[str(REPORT)]
    sys.modules[package.__name__]=package
    return tuple(importlib.import_module(package.__name__+'.'+name) for name in ('christoffel','checker','oracle'))


def corpus():
    return json.loads(CORPUS.read_text())['rows']


def algebra_audit():
    query,checker,oracle=delivered()
    words=[()];counts=dict(words=0,positive=0)
    for n in range(1,10):
        words=[w+(x,) for w in words for x in (1,-1,2,-2) if not w or w[-1]!=-x]
        for word in words:
            if word[0]==-word[-1]:continue
            arena=WordArena();root=arena.from_word(word)
            result=primitive_power_terminal(arena,[root],{1,2})
            expected,exponent=oracle.whitehead_primitive_power(word)
            report=query.classify(arena.rules,root)
            assert (result is not None)==expected==(report.certificate is not None)
            if result:
                assert result['exponent']==exponent
                assert verify_compressed_terminal(arena,[root],{1,2},result)
                assert checker.verify_power(arena.rules,SimpleNamespace(root=root,
                    u=result['primitive_vector'][0],v=result['primitive_vector'][1],
                    exponent=result['exponent'],width=result['width']))
            counts['words']+=1;counts['positive']+=bool(result)
    return counts


def audit():
    old,old_group,hashes=baseline()
    algebra=algebra_audit()
    inputs=list(corpus());rng=random.Random(SEED)
    for index in range(240):
        strands=rng.randrange(2,6)
        word=[rng.choice((-1,1))*rng.randrange(1,strands) for _ in range(rng.randrange(1,15))]
        try:d=Diagram.from_braid(strands,word)
        except DiagramError:continue
        inputs.append(dict(name=f'random-{index}',pd=d.pd,braid=dict(strands=strands,word=word)))
    rows=[]
    for source in inputs:
        d=Diagram.from_pd(source['pd'])
        options=dict(relator_moves=True,max_work=20_000_000)
        before=old.compressed_certificate(d,**options)
        disabled=compressed_certificate(d,primitive_power=False,**options)
        assert before==disabled
        stats={};after=compressed_certificate(d,stats=stats,**options)
        if before:
            assert old_group.verify_group_certificate(d,before,compressed=True,max_work=20_000_000)
            assert group_module.verify_group_certificate(d,before,compressed=True,max_work=20_000_000)
        if after:
            for compressed in (False,True):
                assert group_module.verify_group_certificate(d,after,compressed=compressed,max_work=20_000_000)
        # If the new positive theorem closes a previously stalled state, check
        # the full independent knot recognizer as an additional finite oracle.
        if after and not before:
            assert recognize(Diagram.from_pd(source['pd']),use_group=False,seconds=30).status=='UNKNOT'
        rows.append(dict(source=source,old_certificate=before,new_certificate=after,stats=stats))
    return dict(algebra=algebra,cases=rows,diagrams=len(rows),baseline_source_sha256=hashes,
        terminal_hits=sum(bool(r['new_certificate'] and r['new_certificate']['version']==5) for r in rows),
        proper_power_hits=sum(bool(r['new_certificate'] and r['new_certificate'].get('terminal',{}).get('exponent',1)>1) for r in rows),
        newly_closed=sum(bool(r['new_certificate'] and not r['old_certificate']) for r in rows),
        scope='Literal KMP-root/Whitehead oracle, delivered arithmetic query/checker and native independent replay on cyclically reduced words. Actual validated diagram proofs are fully replayed; no arbitrary group is accepted as a knot. Disabled producer equals pinned baseline exactly.')


def benchmark():
    old,old_group,hashes=baseline();current=group_module.group_decide
    functions=dict(old=old_group.group_decide,old_AA=old_group.group_decide,
                   current=current,current_AA=current)
    rng=random.Random(SEED+1);rows=[];proofs={}
    options=dict(use_group=True,group_relators=True,group_compressed_search=True,
        group_seconds=10,group_max_work=20_000_000,seconds=12,max_objects=50_000)
    for source in corpus():
        samples,warmups=[],[]
        for iteration in range(-1,5):
            order=list(functions);rng.shuffle(order);measurements={}
            for arm in order:
                with patch.object(group_module,'group_decide',functions[arm]):
                    start=time.perf_counter()
                    result=recognize(Diagram.from_pd(source['pd']),**options)
                    elapsed=time.perf_counter()-start
                complete=result.status in ('UNKNOT','KNOTTED')
                if complete:assert result.status==source['expected']
                groups=[]
                for group in stage_records(result.evidence):
                    record={k:v for k,v in group.items() if k!='certificate'}
                    if 'certificate' in group:
                        c=group['certificate'];encoded=json.dumps(json_safe(c),sort_keys=True,separators=(',',':')).encode()
                        key=sha256(encoded).hexdigest();proofs[key]=c
                        record.update(certificate_sha256=key,certificate_bytes=len(encoded),certificate_version=c['version'])
                    groups.append(record)
                measurements[arm]=dict(seconds=elapsed,completed=complete,status=result.status,
                    method=result.method,groups=groups,reason=result.evidence.get('reason'))
            (warmups if iteration<0 else samples).append(dict(order=order,measurements=measurements))
        medians={arm:median([s['measurements'][arm]['seconds'] for s in samples if s['measurements'][arm]['completed']])
                 if any(s['measurements'][arm]['completed'] for s in samples) else None for arm in functions}
        ratios={}
        for label,a,b in [('current','old','current'),('old_AA','old','old_AA'),('current_AA','current','current_AA')]:
            pairs=[s['measurements'][a]['seconds']/s['measurements'][b]['seconds'] for s in samples
                   if s['measurements'][a]['completed'] and s['measurements'][b]['completed']]
            ratios[label]=dict(count=len(pairs),median=median(pairs) if pairs else None)
        row=dict(source=source,samples=samples,warmups=warmups,medians=medians,paired_ratios=ratios)
        rows.append(row);print(source['name'],json.dumps(dict(medians=medians,ratios=ratios)),flush=True)
    return dict(cases=rows,certificates=proofs,baseline_source_sha256=hashes,rounds=5,
        measured_calls=len(rows)*20,warmup_calls=len(rows)*4,
        completed_calls=sum(m['completed'] for r in rows for s in r['samples'] for m in s['measurements'].values()),
        scope='Complete fresh PD recognition through the compressed group route, including independent source reconstruction and proof replay, four shuffled arms with old/new A/A controls. Current group host versus pinned old group host and old search/replay modules; unchanged downstream operations verified by source equality. Timed-out/stalled calls retained, excluded from complete medians and paired ratios. No kernel-only ratio is advertised as pipeline speedup.')


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode',choices=('audit','benchmark'));parser.add_argument('--output',required=True,type=Path)
    args=parser.parse_args();before=sources();start=time.perf_counter()
    result=(audit if args.mode=='audit' else benchmark)()
    assert before==sources()
    result.update(mode=args.mode,baseline_commit=BASELINE,seed=SEED if args.mode=='audit' else SEED+1,
        seconds=time.perf_counter()-start,python=platform.python_version(),platform=platform.platform(),
        source_sha256=before,source_hashes_unchanged=True)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(json_safe(result),indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('cases','certificates','source_sha256')},indent=2))


if __name__=='__main__':main()
