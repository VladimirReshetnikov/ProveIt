"""Pinned prior/current audits and timings for cached support substitution."""
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
from compressed_word_research import frontier as f
from fastunknot.integer_codec import json_safe
BASELINE='f9e20ed6f3f1b8f9864516fd0a00a1047825508e';SEED=261008522


def sources():
    result=f.sources()
    for p in (Path(__file__),ROOT/'tests/test_sparse_substitution.py'):
        result[str(p.relative_to(ROOT.parent))]=sha256(p.read_bytes()).hexdigest()
    return result


def kernel(arena_type,kind,size):
    a=arena_type(max_nodes=200000,max_work=50000000)
    if kind=='singleton-chain':
        root=0
        for i in range(size):
            root=a.concat(root,a.letter(1+i%2));answer=a.singletons([root])
        assert answer==[[]]
    else:
        prefix=a.reduce(a.power(a.from_word([1,2]),1<<size))
        root=a.concat(prefix,a.letter(3));roots=[root,prefix]
        for i in range(128):
            if kind=='warm-tail':a.singletons(roots)
            roots=a.substitute(roots,{3+i%2:a.letter(4-i%2)})
        root=roots[0]
        assert roots[1]==prefix and a.last[root]==3 and a.lengths[root]==(2<<size)+1
    return dict(stats=dict(a.stats),nodes=len(a.rules)-1,output_length_bits=a.lengths[root].bit_length())


def kernels(old,old_search,old_group,hashes):
    rng=random.Random(SEED+2);rows=[];arms=('old','current','old_AA','current_AA')
    cases=[('singleton-chain',s) for s in (64,256,1024,2048)]
    cases += [(kind,s) for kind in ('warm-tail','cold-tail') for s in (64,256,1024,4096)]
    for kind,size in cases:
        samples=[];warmups=[]
        for iteration in range(-1,5):
            order=list(arms);rng.shuffle(order);measurements={}
            for arm in order:
                start=time.perf_counter()
                record=kernel(old_search.WordArena if arm.startswith('old') else f.WordArena,kind,size)
                measurements[arm]=dict(seconds=time.perf_counter()-start,completed=True,**record)
            (warmups if iteration<0 else samples).append(dict(order=order,measurements=measurements))
        medians={arm:median(s['measurements'][arm]['seconds'] for s in samples) for arm in arms}
        ratios=f.harness.ratios(samples,[('current','old','current'),('old_AA','old','old_AA'),('current_AA','current','current_AA')])
        rows.append(dict(kind=kind,size=size,samples=samples,warmups=warmups,medians=medians,paired_ratios=ratios))
        print(kind,size,json.dumps(dict(medians=medians,ratios=ratios)),flush=True)
    return dict(cases=rows,baseline_source_sha256=hashes,measured_calls=len(rows)*20,warmup_calls=len(rows)*4,
        completed_calls=len(rows)*20,scope='Fresh construction, initial reduction and all metadata queries included. Huge positive prefixes are never expanded. Warm and cold repeated tail substitution use the same immutable source prefix. Four shuffled arms including A/A controls; five measured rounds and one warm-up. These are word-operation kernels, not knot discovery.')


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('mode',choices=('audit','benchmark','kernels'));p.add_argument('--output',type=Path,required=True);args=p.parse_args()
    f.BASELINE=BASELINE;f.SEED=SEED;before=sources();start=time.perf_counter()
    with tempfile.TemporaryDirectory(prefix='unknot-sparse-substitution-') as directory:
        prior=f.baseline(directory);result={'audit':f.audit,'benchmark':f.benchmark,'kernels':kernels}[args.mode](*prior)
    assert before==sources()
    result.update(mode=args.mode,baseline_commit=BASELINE,seed=SEED+{'audit':0,'benchmark':1,'kernels':2}[args.mode],seconds=time.perf_counter()-start,
        python=platform.python_version(),platform=platform.platform(),source_sha256=before,source_hashes_unchanged=True)
    args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(json.dumps(json_safe(result),indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('cases','certificates','source_sha256','baseline_source_sha256')},indent=2))


if __name__=='__main__':main()
