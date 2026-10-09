"""Native differential audit and complete-call measurements of compact permutations."""
import argparse
from collections import Counter
from contextlib import nullcontext
import hashlib
import json
from pathlib import Path
import platform
import random
from statistics import median
import sys
import tempfile
import time
import tracemalloc
from unittest.mock import patch

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from fastunknot.compressed_braid import recognize, verify, forest
from compressed_braid_research import adaptive
from compressed_braid_research.exceptional import grammar, join
from compressed_braid_research.families import sleeve, singleton_forest

BASELINE='d0f0e37761b5375ff9d0f71cca95a2ce1f6423ca'
SEED=261008611


def sources():
    paths=list((ROOT/'fastunknot/compressed_braid').glob('*.py'))
    paths += [ROOT/p for p in ('fastunknot/compressed_words.py','fastunknot/braid_reduction.py',
        'fastunknot/braid_descent.py','compressed_braid_research/adaptive.py',
        'compressed_braid_research/exceptional.py','compressed_braid_research/families.py',
        'tests/test_compressed_braid_permutations.py')]
    paths.append(Path(__file__).resolve())
    return {str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}


def fixtures():
    rng=random.Random(SEED)
    cases=[('late_finite_'+str(f),join(singleton_forest(f,32),grammar(2,[1,1,1]))) for f in (8,24,64)]
    cases += [('early_compressed',singleton_forest(24,32,negative_index=0)),
              ('positive_forest',singleton_forest(16,32)),
              ('all_singleton',grammar(128,list(range(1,128)))),
              ('single_wider',grammar(4,[1,2,3,1,-1,2,-2,3,-3])),
              ('direct_three',sleeve(32))]
    # Squaring a full-support permutation on an even strand count cannot
    # produce one cycle. Keep these controls in the component-only path.
    dense=grammar(128,list(range(1,128))+[rng.randrange(1,128) for _ in range(1000)])
    root=dense['root'];dense['rules'].append(['c',root,root]);dense['root']=len(dense['rules'])-1
    cases.append(('dense_random_link',dense))
    powered=grammar(128,list(range(1,128)))
    for _ in range(512):
        root=powered['root'];powered['rules'].append(['c',root,root]);powered['root']=len(powered['rules'])-1
    cases.append(('dense_power_link',powered))
    dead=grammar(64,list(range(1,64)))
    for _ in range(1000):
        node=len(dead['rules']);dead['rules'].append(['g',rng.randrange(1,64)])
        dead['rules'].append(['c',node,node])
    cases.append(('unreachable_rules',dead))
    cases.append(('huge_strand_gap',dict(strands=10**100,rules=[['e']],root=0)))
    return cases


def audit(old):
    prior_path=ROOT.parent/'synthesis/data/lazy-forest-audit.json'
    prior=json.loads(prior_path.read_text())['cases']
    cases=[(r['name'],r['input']) for r in prior]+fixtures()
    rng=random.Random(SEED+2)
    # Small random explicit diagrams plus reachable and unreachable shared DAG
    # powers. Disable the exponential fallback for these additional controls.
    for trial in range(150):
        m=rng.randrange(4,33)
        data=grammar(m,list(range(1,m))+[rng.choice((-1,1))*rng.randrange(1,m) for _ in range(50)])
        for _ in range(rng.randrange(40)):
            node=rng.randrange(len(data['rules']))
            data['rules'].append(['c',node,node])
            if rng.randrange(2):data['root']=len(data['rules'])-1
        cases.append(('random'+str(trial),data))
    rows=[]
    for name,data in cases:
        previous=old.recognize(data,fallback_max_crossings=0)
        current=recognize(data,fallback_max_crossings=0)
        assert previous==current,(name,previous['status'],current['status'])
        assert verify(data,previous['certificate'],fallback_max_crossings=0)==current['status']
        assert old.verify(data,current['certificate'],fallback_max_crossings=0)==current['status']
        assert old.forest.summarize(data)==forest.summarize(data)
        rows.append(dict(name=name,input=data,status=current['status'],resources=current['resources'],
            identical_public_result=True,certificate_bytes=current['certificate_bytes']))
    return dict(comparisons=len(rows),cases=rows,status_counts=dict(Counter(r['status'] for r in rows)),
        prior_input_sha256=hashlib.sha256(prior_path.read_bytes()).hexdigest(),
        scope='All complete public result fields, exact root summaries and bidirectional certificate replay; fallback disabled equally in both arms.')


def peak_summary(fn,data):
    tracemalloc.start()
    try:
        fn(data)
        return tracemalloc.get_traced_memory()[1]
    finally:
        tracemalloc.stop()


def benchmark(old):
    original=forest._root_permutation
    def dense(*args,**kwargs):return original(*args,**kwargs,compact=False)
    rng=random.Random(SEED+1);rows=[]
    arms=('old','old_AA','current','current_AA','live_dense')
    for name,data in fixtures():
        previous,current=old.recognize(data),recognize(data)
        assert previous==current
        samples,warmups=[],[]
        for iteration in range(-1,7):
            order=list(arms);rng.shuffle(order);times={}
            for arm in order:
                context=patch.object(forest,'_root_permutation',dense) if arm=='live_dense' else nullcontext()
                # Only policy selection is outside the timed call; no input
                # validation, permutation, proof or transport work is excluded.
                with context:
                    start=time.perf_counter()
                    result=(old.recognize(data) if arm.startswith('old') else recognize(data))
                    times[arm]=time.perf_counter()-start
                assert result==previous and result['verified']
            (warmups if iteration<0 else samples).append(dict(order=order,seconds=times))
        medians={a:median(r['seconds'][a] for r in samples) for a in arms}
        ratios={a:median(r['seconds']['old']/r['seconds'][a] for r in samples) for a in arms}
        peaks=dict(old=peak_summary(old.forest.summarize,data),current=peak_summary(forest.summarize,data))
        with patch.object(forest,'_root_permutation',dense):
            peaks['live_dense']=peak_summary(forest.summarize,data)
        rows.append(dict(name=name,input=data,status=current['status'],samples=samples,warmups=warmups,
            medians=medians,paired_ratios=ratios,
            current_AA_ratio=median(r['seconds']['current']/r['seconds']['current_AA'] for r in samples),
            root_summary_peak_traced_bytes=peaks,resources=current['resources'],
            certificate_bytes=current['certificate_bytes'],identical_public_result=True))
        print(name,json.dumps(dict(medians=medians,paired_ratios=ratios,peaks=peaks)),flush=True)
    return dict(cases=rows,rounds=7,excluded_warmups=1,
        scope='Complete public recognition including all source checks, proof construction, canonical JSON allowance accounting and mandatory replay. Policy binding is outside the timer. Memory measured separately on complete root summaries with tracemalloc; not process RSS or a hard memory cap.')


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode',choices=('audit','benchmark'))
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args();before=sources();start=time.perf_counter()
    adaptive.BASE=BASELINE
    with tempfile.TemporaryDirectory(prefix='compact-permutations-baseline-') as directory:
        old,hashes=adaptive.baseline(Path(directory))
        result=(audit if args.mode=='audit' else benchmark)(old)
    assert sources()==before
    result.update(mode=args.mode,seed=SEED,baseline=BASELINE,baseline_source_sha256=hashes,
        source_sha256=before,source_hashes_unchanged=True,seconds=time.perf_counter()-start,
        python=platform.python_version(),platform=platform.platform())
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('cases','source_sha256','baseline_source_sha256')},indent=2))


if __name__=='__main__':main()
