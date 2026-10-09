"""Full source replay timings for fixed, valid split-batch knot certificates.

The certificate is supplied, not discovered in the timed call. Each call does
fresh PD validation and the verifier's independent presentation reconstruction.
The ordinary producer still emits the unsplit batch on these circle fixtures.
"""
from hashlib import sha256
import json
from pathlib import Path
import platform
import random
from statistics import median
import sys
import tempfile
import time
ROOT=Path(__file__).resolve().parents[2]/'fast';sys.path.insert(0,str(ROOT))
from compressed_word_research import persistent_replay as native
from fastunknot import Diagram
from fastunknot.compressed_search import compressed_certificate
from fastunknot.group_certificate import verify_group_certificate


def main():
    before=native.sources();before['synthesis/data/'+Path(__file__).name]=sha256(Path(__file__).read_bytes()).hexdigest()
    native.prior.harness.BASELINE=native.BASELINE
    rng=random.Random(native.SEED+2);records=[];proofs={};begin=time.perf_counter()
    with tempfile.TemporaryDirectory(prefix='unknot-persistent-source-') as directory:
        old,search,group,hashes=native.prior.harness.baseline(directory)
        for crossings in (8,32,128,256):
            diagram=Diagram.from_braid(crossings+1,list(range(1,crossings+1)))
            proof=compressed_certificate(diagram,elimination_batch=True,max_work=20000000)
            assert proof['version']==8 and len(proof['moves'])==1
            proof['moves']=[dict(kind='elimination_batch',entries=[e]) for e in proof['moves'][0]['entries']]
            raw=native.prior.encode(proof);key=sha256(raw).hexdigest();proofs[key]=proof
            assert verify_group_certificate(diagram,proof,compressed=False,max_work=100000000)
            samples=[];warmups=[];arms=('old','current','old_AA','current_AA')
            for iteration in range(-1,5):
                order=list(arms);rng.shuffle(order);measurements={}
                for arm in order:
                    prior=arm.startswith('old');stats={};start=time.perf_counter()
                    d=(old.Diagram if prior else Diagram).from_pd(diagram.pd)
                    assert (group.verify_group_certificate if prior else verify_group_certificate)(d,proof,compressed=True,max_work=100000000,max_nodes=1000000,stats=stats)
                    end=time.perf_counter()
                    measurements[arm]=dict(seconds=end-start,completed=True,stats=stats,certificate_sha256=key,certificate_bytes=len(raw))
                (warmups if iteration<0 else samples).append(dict(order=order,measurements=measurements))
            medians={a:median(s['measurements'][a]['seconds'] for s in samples) for a in arms}
            ratios=native.prior.harness.ratios(samples,[('current','old','current'),('old_AA','old','old_AA'),('current_AA','current','current_AA')])
            records.append(dict(source=dict(crossings=crossings,pd=diagram.pd),samples=samples,warmups=warmups,medians=medians,paired_ratios=ratios))
            print(crossings,ratios,flush=True)
    after=native.sources();after['synthesis/data/'+Path(__file__).name]=sha256(Path(__file__).read_bytes()).hexdigest();assert before==after
    result=dict(cases=records,certificates=proofs,measured_calls=80,warmup_calls=16,completed_calls=80,source_sha256=before,
                source_hashes_unchanged=True,baseline_commit=native.BASELINE,baseline_source_sha256=hashes,seconds=time.perf_counter()-begin,
                python=platform.python_version(),platform=platform.platform(),seed=native.SEED+2,
                scope='Identical supplied v8 certificates split into consecutive singleton batches; fresh diagram validation plus complete independent source reconstruction/replay. Proof discovery/splitting and serialization outside timers. The existing producer does not emit these split proofs by default. Four shuffled arms with five rounds and retained warm-ups; no whole-discovery timing.')
    Path(__file__).with_name('persistent-replay-source.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('cases','certificates','source_sha256','baseline_source_sha256')},indent=2))


if __name__=='__main__':main()
