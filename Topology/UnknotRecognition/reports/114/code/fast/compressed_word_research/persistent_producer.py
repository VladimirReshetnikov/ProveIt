"""Pinned producer integration audit and complete source-bound timings."""
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

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT));sys.path.insert(0,str(ROOT/'tests'))
from compressed_word_research import ordered_batch as prior
from fastunknot import Diagram
from fastunknot import group_certificate as current_group
from fastunknot.integer_codec import json_safe
from test_persistent_producer import PD

BASELINE='4360509f450e1d8e4ac4b3c1e145d9d893172d57'
SEED=261009437


def sources():
    return {str(p.relative_to(ROOT.parent)):sha256(p.read_bytes()).hexdigest()
            for p in list(ROOT.rglob('*.py'))+[prior.harness.CORPUS]}


def source_stage(old,group):
    """Actual multibatch PD, including discovery and mandatory replay."""
    rng=random.Random(SEED+1);samples=[];warmups=[];proofs={}
    arms=('old','current','old_AA','current_AA')
    for iteration in range(-1,5):
        order=list(arms);rng.shuffle(order);measurements={}
        for arm in order:
            historical=arm.startswith('old');engine=group if historical else current_group
            package=old if historical else sys.modules['fastunknot']
            begin=time.perf_counter()
            result=engine.group_decide(package.Diagram.from_pd(PD),elimination_batch=True,
                compressed_search=True,relator_moves=True,max_work=20000000,seconds=20)
            elapsed=time.perf_counter()-begin
            c=result.get('certificate');data={k:v for k,v in result.items() if k!='certificate'}
            if c:
                key=sha256(prior.encode(c)).hexdigest();proofs[key]=c
                data.update(certificate_sha256=key,certificate_bytes=len(prior.encode(c)))
                # Additional literal source replay is outside the timed call.
                assert current_group.verify_group_certificate(Diagram.from_pd(PD),c,max_work=20000000)
            completed=result['status']=='UNKNOT'
            assert result['status'] in ('UNKNOT','INCONCLUSIVE')
            measurements[arm]=dict(seconds=elapsed,completed=completed,status=result['status'],groups=[data])
        (warmups if iteration<0 else samples).append(dict(order=order,measurements=measurements))
    medians={a:median(s['measurements'][a]['seconds'] for s in samples if s['measurements'][a]['completed'])
             if any(s['measurements'][a]['completed'] for s in samples) else None for a in arms}
    ratios=prior.harness.ratios(samples,[('current','old','current'),('old_AA','old','old_AA'),('current_AA','current','current_AA')])
    return dict(cases=[dict(source=dict(name='survivor-10',pd=PD),samples=samples,warmups=warmups,medians=medians,paired_ratios=ratios)],
        certificates=proofs,measured_calls=20,warmup_calls=4,
        completed_calls=sum(m['completed'] for s in samples for m in s['measurements'].values()),
        scope='Fresh PD validation, optional batch group discovery and mandatory compressed source replay; additional literal replay outside timer.')


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode',choices=('audit','stages','source','pipeline'))
    parser.add_argument('--output',type=Path,required=True);args=parser.parse_args()
    before=sources();prior.harness.BASELINE=BASELINE;prior.SEED=SEED;begin=time.perf_counter()
    with tempfile.TemporaryDirectory(prefix='unknot-persistent-producer-') as directory:
        old,search,group,hashes=prior.harness.baseline(directory)
        changed={n for n,h in hashes.items() if h!=sha256((ROOT/'fastunknot'/n).read_bytes()).hexdigest()}
        assert changed=={'compressed_search.py','elimination_batch.py'},changed
        # Every preexisting verifier is byte-identical to the pinned baseline.
        assert all(h==sha256((ROOT/'fastunknot'/n).read_bytes()).hexdigest()
                   for n,h in hashes.items() if 'verify' in n or n in ('compressed_group.py','group_certificate.py'))
        replay=importlib.import_module(search.__package__+'.elimination_batch_verify').replay_compressed_batch
        if args.mode=='audit':
            result=prior.audit(old,search,group,replay)
            result['batch_certificates_changed']=sum(r['modes']['batch']['old']['certificate_sha256']!=r['modes']['batch']['current']['certificate_sha256'] for r in result['cases'])
            result['persistent_source_cases']=sum(bool(r['modes']['batch']['current']['stats'].get('persistent_search_blocks')) for r in result['cases'])
        elif args.mode=='source':result=source_stage(old,group)
        else:result=prior.benchmark(old,search,group,replay,args.mode)
    assert before==sources()
    result.update(mode=args.mode,baseline_commit=BASELINE,source_sha256=before,baseline_source_sha256=hashes,
        checker_sources_unchanged=True,source_hashes_unchanged=True,seconds=time.perf_counter()-begin,
        seed=SEED,python=platform.python_version(),platform=platform.platform())
    args.output.write_text(json.dumps(json_safe(result),indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('cases','certificates','abstract','source_sha256','baseline_source_sha256')},indent=2))


if __name__=='__main__':main()
