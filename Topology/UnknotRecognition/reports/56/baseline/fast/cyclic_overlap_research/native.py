"""Rebase report-46 overlap queries on the maintained donor-pruned recognizer."""
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
from types import ModuleType
from unittest.mock import patch

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from fastunknot import Diagram, recognize, relator_overlap
from fastunknot.cyclic_overlap_index import bounded_overlap_move
from fastunknot.group_certificate import _Budget, group_certificate, verify_group_certificate
from fastunknot.relator_overlap import overlap_move

BASELINE='bec1afd07cd231b545080e771692f37b7f52e8a9'
REPORT=ROOT.parent/'reports/46/repo_overlay/Topology/UnknotRecognition/fast'
REPORT_DATA=REPORT/'cyclic_overlap_research/results.json'
SEED=261008613
ARMS=('old','old_AA','current','current_AA','report','joint')


def digest(value):
    return sha256(json.dumps(value,sort_keys=True,separators=(',',':')).encode()).hexdigest()


def sources():
    paths=list((ROOT/'fastunknot').glob('*.py'))+[Path(__file__).resolve(),ROOT/'tests/test_cyclic_overlap_index.py',
        REPORT_DATA,REPORT/'fastunknot/cyclic_overlap_index.py',REPORT/'fastunknot/relator_overlap.py']
    return {str(p.relative_to(ROOT.parent)):sha256(p.read_bytes()).hexdigest() for p in paths}


def baseline():
    path='Topology/UnknotRecognition/fast/fastunknot/relator_overlap.py'
    raw=subprocess.check_output(['git','show',BASELINE+':'+path])
    old=ModuleType('pinned_overlap');exec(compile(raw,BASELINE+':'+path,'exec'),old.__dict__)
    report=ModuleType('fastunknot._report46_overlap');report.__path__=[str(REPORT/'fastunknot')]
    sys.modules[report.__name__]=report
    delivered=importlib.import_module(report.__name__+'.relator_overlap')
    record=json.loads(REPORT_DATA.read_text())
    for p in ('fastunknot/relator_overlap.py','fastunknot/cyclic_overlap_index.py'):
        assert sha256((REPORT/p).read_bytes()).hexdigest()==record['source_sha256'][p]
    # Search and checker hosts are unchanged since the actual maintained baseline.
    hosts={}
    for name in ('group_certificate.py','compressed_group.py','compressed_search.py','recognize.py','diagram.py'):
        path='Topology/UnknotRecognition/fast/fastunknot/'+name
        data=subprocess.check_output(['git','show',BASELINE+':'+path])
        assert data==(ROOT/'fastunknot'/name).read_bytes(),name
        hosts[path]=sha256(data).hexdigest()
    return old,delivered,dict(overlap=sha256(raw).hexdigest(),unchanged_host_sources=hosts,
                              delivered_source_sha256=record['source_sha256'])


def gain(words,move):
    return 0 if move is None else 2*move['overlap']-len(words[move['donor']])


def queries(old,report):
    def prior(words,budget,stats):
        move=old.overlap_move(words,budget);stats.update(backend='old',best_gain=gain(words,move));return move
    def current(words,budget,stats):return overlap_move(words,budget,stats=stats)
    def incoming(words,budget,stats):return report.overlap_move(words,budget,stats=stats)
    def joint(words,budget,stats):return overlap_move(words,budget,backend='joint',stats=stats)
    return dict(old=prior,old_AA=prior,current=current,current_AA=current,report=incoming,joint=joint)


def summarize(samples):
    medians={};ratios={}
    for arm in ARMS:
        values=[r['measurements'][arm]['seconds'] for r in samples if r['measurements'][arm]['completed']]
        medians[arm]=median(values) if values else None
        pairs=[r['measurements']['old']['seconds']/r['measurements'][arm]['seconds'] for r in samples
               if r['measurements']['old']['completed'] and r['measurements'][arm]['completed']]
        ratios[arm]=dict(count=len(pairs),median=median(pairs) if pairs else None)
    aa=[r['measurements']['current']['seconds']/r['measurements']['current_AA']['seconds'] for r in samples
        if r['measurements']['current']['completed'] and r['measurements']['current_AA']['completed']]
    return dict(medians=medians,paired_ratios=ratios,current_AA_ratio=median(aa) if aa else None)


def kernels(functions,rounds):
    cases=json.loads(REPORT_DATA.read_text())['kernels']
    cases += [dict(name='duplicate-native-cutoff',words=[list(range(1,129)) for _ in range(128)],
                   provenance='synthetic full-donor bound'),
              dict(name='many-empty-slots',words=[[] for _ in range(10000)]+[[1,2,3],[2,3,1]],
                   provenance='synthetic original-slot input size')]
    rng=random.Random(SEED);rows=[]
    for case in cases:
        words=case['words'];expected=gain(words,functions['old'](words,_Budget(lambda:None,10**9,10**9),{}))
        samples,warmups=[],[]
        for iteration in range(-1,rounds):
            order=list(ARMS);rng.shuffle(order);measurements={}
            for arm in order:
                budget=_Budget(lambda:None,10**9,10**9);stats={}
                start=time.perf_counter();move=functions[arm](words,budget,stats);elapsed=time.perf_counter()-start
                assert gain(words,move)==expected
                measurements[arm]=dict(seconds=elapsed,completed=True,status='EXACT',gain=expected,move=move,
                                       work=10**9-budget.left,stats=stats)
            (warmups if iteration<0 else samples).append(dict(order=order,measurements=measurements))
        row=dict(name=case['name'],words=words,provenance=case['provenance'],input_sha256=digest(words),
                 total_length=sum(map(len,words)),slots=len(words),nonempty=sum(bool(w) for w in words),
                 samples=samples,warmups=warmups,**summarize(samples))
        rows.append(row);print(case['name'],json.dumps({k:row[k] for k in ('medians','paired_ratios')}),flush=True)
    return dict(rows=rows,rounds=rounds,excluded_warmups=1,
                scope='Complete exact query including preparation, failed prelude, index and search; explicit source words supplied equally to every arm. Synthetic presentations are not hard-knot recognition examples.')


def stage_records(evidence):
    found=[]
    for key,value in evidence.items():
        if key=='group':found.append(value)
        elif isinstance(value,dict):found.extend(stage_records(value))
        elif isinstance(value,list):
            for item in value:
                if isinstance(item,dict):found.extend(stage_records(item))
    return found


def pipeline(functions,rounds):
    cases=json.loads(REPORT_DATA.read_text())['rows'];rng=random.Random(SEED+1);rows=[];proofs={}
    modes=dict(explicit=dict(use_group=True,group_relators=True,group_seconds=10,
                            group_max_work=20_000_000,seconds=12,max_objects=50_000),
               compressed=dict(use_group=True,group_relators=True,group_seconds=10,
                               group_max_work=20_000_000,group_compressed_search=True,
                               seconds=12,max_objects=50_000))
    for case in cases:
        row={k:case[k] for k in ('name','pd','crossings','expected')};row['modes']={}
        for mode,options in modes.items():
            samples,warmups=[],[]
            for iteration in range(-1,rounds):
                order=list(ARMS);rng.shuffle(order);measurements={}
                for arm in order:
                    queries_seen=[]
                    def query(words,budget):
                        stats={};move=functions[arm](words,budget,stats);queries_seen.append(stats);return move
                    with patch.object(relator_overlap,'overlap_move',query):
                        start=time.perf_counter()
                        result=recognize(Diagram.from_pd(case['pd']),**options)
                        elapsed=time.perf_counter()-start
                    complete=result.status in ('UNKNOT','KNOTTED')
                    if complete:assert result.status==case['expected'],(case['name'],mode,arm,result)
                    groups=[]
                    for group in stage_records(result.evidence):
                        record={k:v for k,v in group.items() if k!='certificate'}
                        if 'certificate' in group:
                            key=digest(group['certificate']);proofs[key]=group['certificate'];record['certificate_sha256']=key
                        groups.append(record)
                    measurements[arm]=dict(seconds=elapsed,completed=complete,status=result.status,
                        method=result.method,queries=queries_seen,groups=groups,reason=result.evidence.get('reason'))
                (warmups if iteration<0 else samples).append(dict(order=order,measurements=measurements))
            out=dict(samples=samples,warmups=warmups,**summarize(samples));row['modes'][mode]=out
            print(case['name'],mode,json.dumps(out['medians']),flush=True)
        rows.append(row)
    return dict(rows=rows,certificates=proofs,configurations=modes,rounds=rounds,excluded_warmups=1,
                scope='Fresh PD validation, all recognition stages and mandatory certificate replay. Corpus loading, policy binding and result serialization outside timers. UNKNOWN/INCONCLUSIVE retained and excluded from completed medians and pairs.')


def audit(functions):
    cases=json.loads(REPORT_DATA.read_text())['rows'];rows=[]
    for case in cases:
        d=Diagram.from_pd(case['pd']);proofs={};queries_seen={}
        for arm in ('old','current','report','joint'):
            seen=[]
            def query(words,budget):
                stats={};move=functions[arm](words,budget,stats);seen.append(dict(words=[list(w) for w in words],stats=stats,move=move));return move
            with patch.object(relator_overlap,'overlap_move',query):
                proof=group_certificate(d,relator_moves=True,max_work=20_000_000)
            if proof is not None:
                for compressed in (False,True):
                    assert verify_group_certificate(d,proof,compressed=compressed,max_work=20_000_000)
            proofs[arm]=proof;queries_seen[arm]=seen
        assert (proofs['old'] is None)==(proofs['current'] is None)
        # Longest-first donors and joint continuation can change tied moves;
        # archive observed trace equality instead of assuming it.
        rows.append(dict(name=case['name'],pd=case['pd'],proofs=proofs,queries=queries_seen,
                         same_native_certificate=proofs['old']==proofs['current']))
    return dict(rows=rows,comparisons=len(rows),native_identical=sum(r['same_native_certificate'] for r in rows),
                scope='Complete native group production and both independent replay backends on actual diagrams; no knot conclusion from absent proofs.')


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode',choices=('audit','kernels','pipeline'))
    parser.add_argument('--rounds',type=int,default=5)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args();assert args.rounds>0
    before=sources();old,report,hashes=baseline();start=time.perf_counter();fn=queries(old,report)
    result=audit(fn) if args.mode=='audit' else (kernels if args.mode=='kernels' else pipeline)(fn,args.rounds)
    assert sources()==before
    result.update(mode=args.mode,baseline=BASELINE,baseline_source_sha256=hashes,source_sha256=before,
                  sources_unchanged=True,seed=SEED,python=platform.python_version(),platform=platform.platform(),
                  seconds=time.perf_counter()-start)
    args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('rows','certificates','source_sha256','baseline_source_sha256')},indent=2))


if __name__=='__main__':main()
