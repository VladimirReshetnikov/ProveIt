"""Cross-replay and whole-call measurements for lazy compressed forest preparation."""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import platform
import random
from statistics import median
import sys
import tempfile
import time
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from fastunknot.compressed_braid import recognize, verify, forest
from compressed_braid_research import adaptive
from compressed_braid_research.exceptional import grammar, join
from compressed_braid_research.families import sleeve, singleton_forest

BASELINE = '586bfc8d0ffc1325cb06b61af42b7321fb58e79b'
SEED = 261008501


def sources():
    paths=list((ROOT/'fastunknot/compressed_braid').glob('*.py'))
    paths += [ROOT/p for p in ('fastunknot/compressed_words.py','fastunknot/braid_reduction.py',
        'fastunknot/braid_descent.py','compressed_braid_research/adaptive.py',
        'compressed_braid_research/exceptional.py','compressed_braid_research/families.py')]
    paths += [Path(__file__).resolve()]
    return {str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}


def projected_call(module, data, **options):
    target=sys.modules[module.__name__+'.forest']
    original=target.project; calls=[]
    def track(source,low,high,**kwargs):
        calls.append([low,high])
        return original(source,low,high,**kwargs)
    with patch.object(target,'project',track):
        result=module.recognize(data,**options)
    return result,calls


def audit(old):
    prior_path=ROOT.parent/'synthesis/data/exceptional-cube-audit.json'
    prior=json.loads(prior_path.read_text())['cases']
    cases=[('prior'+str(i),grammar(r['strands'],r['word']),r['status']) for i,r in enumerate(prior)]
    rng=random.Random(SEED)
    for i in range(80):
        factors=rng.randrange(2,9)
        kinds=[rng.randrange(4) for _ in range(factors)]
        data=None
        for kind in kinds:
            leaf=(sleeve(rng.randrange(5),negative=kind==1) if kind<2 else
                  grammar(2,[1,-1,1] if kind==2 else [1,1,1]))
            data=leaf if data is None else join(data,leaf)
        cases.append(('forest'+str(i),data,'KNOTTED' if any(k in (1,3) for k in kinds) else 'UNKNOT'))
    rows=[]
    for name,data,expected in cases:
        previous,current=old.recognize(data),recognize(data)
        assert previous['status']==current['status']==expected
        assert verify(data,previous['certificate'])==expected
        assert old.verify(data,current['certificate'])==expected
        assert verify(data,current['certificate'])==expected
        if expected=='UNKNOT':assert previous['certificate']==current['certificate']
        s=forest.summarize(data)
        if s['knot']:
            ends=[0]+sorted(g for g,n in s['counts'].items() if n==1)+[data['strands']]
            for _,bound,_,lo,hi,length,exponent in forest._factor_plan(data,s,list(zip(ends,ends[1:])),lambda:None):
                leaf=forest.project(data,lo+1,hi);ls=forest.summarize(leaf)
                assert (ls['length'],ls['exponent'])==(length,exponent)
                assert bound>=len(leaf['rules'])
        rows.append(dict(name=name,input=data,status=expected,old_work=previous['resources']['work'],
            current_work=current['resources']['work'],old_order=previous.get('factor_order'),
            current_order=current.get('factor_order'),same_certificate=previous['certificate']==current['certificate']))
    data=join(singleton_forest(24,32),grammar(2,[1,1,1]))
    full=recognize(data,max_nodes=0,fallback_max_generators=0)
    previous=old.recognize(data,max_nodes=0,fallback_max_generators=0,max_work=full['resources']['work'])
    assert full['status']=='KNOTTED' and previous['status']=='INCONCLUSIVE'
    return dict(cases=rows,comparisons=len(rows),status_counts=dict(Counter(r['status'] for r in rows)),
        prior_input_sha256=hashlib.sha256(prior_path.read_bytes()).hexdigest(),
        bounded_progress=dict(old=previous['status'],current=full['status'],allowance=full['resources']['work'],
            input=data,certificate=full['certificate']))


def benchmark(old):
    import fastunknot.compressed_braid as current_module
    rng=random.Random(SEED+1)
    wider=grammar(4,[1,2,3,1,-1,2,-2,3,-3])
    cases=[('late_finite_'+str(f),join(singleton_forest(f,32),grammar(2,[1,1,1]))) for f in (8,24,64)]
    cases += [('late_compressed',singleton_forest(24,32,negative_index=23)),
              ('early_compressed',singleton_forest(24,32,negative_index=0)),
              ('positive_forest',singleton_forest(16,32)),
              ('all_singleton',grammar(128,list(range(1,128)))),
              ('positive_mixed',join(wider,sleeve(32))),
              ('single_wider',wider),('direct_three',sleeve(32))]
    rows=[];arms=('old','old_AA','current','current_AA','eager')
    for name,data in cases:
        previous,old_calls=projected_call(old,data)
        current,new_calls=projected_call(current_module,data)
        expected=previous['status'];assert current['status']==expected
        samples,warmups=[],[]
        for iteration in range(-1,5):
            order=list(arms);rng.shuffle(order);times={}
            for arm in order:
                start=time.perf_counter()
                result=(old.recognize(data) if arm.startswith('old') else
                        recognize(data,use_lazy_factors=arm!='eager'))
                times[arm]=time.perf_counter()-start
                assert result['status']==expected and result['verified']
            (warmups if iteration<0 else samples).append(dict(order=order,seconds=times))
        medians={a:median(r['seconds'][a] for r in samples) for a in arms}
        ratios={a:median(r['seconds']['old']/r['seconds'][a] for r in samples) for a in arms}
        rows.append(dict(name=name,input=data,status=expected,samples=samples,warmups=warmups,
            medians=medians,paired_ratios=ratios,
            current_AA_ratio=median(r['seconds']['current']/r['seconds']['current_AA'] for r in samples),
            old_projection_calls=old_calls,new_projection_calls=new_calls,
            old_order=previous.get('factor_order'),new_order=current.get('factor_order'),
            old_resources=previous['resources'],new_resources=current['resources'],
            old_certificate_bytes=previous['certificate_bytes'],new_certificate_bytes=current['certificate_bytes']))
        print(name,json.dumps(dict(medians=medians,ratios=ratios)),flush=True)
    return dict(cases=rows,rounds=5,excluded_warmups=1,
        scope='Complete public recognition including source checks, proof production, transport cap accounting and mandatory independent replay. Projection counts are separate untimed instrumented calls. No expanded-word preprocessing is excluded.')


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode',choices=('audit','benchmark'))
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args();before=sources();start=time.perf_counter()
    adaptive.BASE=BASELINE
    with tempfile.TemporaryDirectory(prefix='lazy-forest-baseline-') as directory:
        old,hashes=adaptive.baseline(Path(directory))
        result=(audit if args.mode=='audit' else benchmark)(old)
    assert sources()==before
    result.update(mode=args.mode,seed=SEED if args.mode=='audit' else SEED+1,baseline=BASELINE,
        baseline_source_sha256=hashes,source_sha256=before,source_hashes_unchanged=True,
        seconds=time.perf_counter()-start,python=platform.python_version(),platform=platform.platform())
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('cases','source_sha256','baseline_source_sha256','bounded_progress')},indent=2))


if __name__=='__main__':main()
