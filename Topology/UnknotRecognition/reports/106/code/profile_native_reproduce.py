"""Reproduce the full native profile at the pinned baseline or patched runtime."""
import argparse
from collections import Counter
import cProfile
import hashlib
import io
import json
from pathlib import Path
import pstats
import subprocess
import tarfile
import tempfile
import time

from benchmark_source_contraction import PIN, namespace


def run(args, directory):
    produce,replay=namespace('profile_native_variant',directory)
    corpus=(args.repo/'Topology/UnknotRecognition/fast/marked_parallelity_research/corpus.json').read_bytes()
    counts=Counter();records=[];start=time.perf_counter();profile=cProfile.Profile();profile.enable()
    for case in json.loads(corpus)['cases']:
        at=time.perf_counter();result=produce(case['triangulation'],case['coordinates'],record_certificate=True)
        produce_seconds=time.perf_counter()-at;replay_seconds=None
        if result['status']=='COMPLETE':
            at=time.perf_counter();assert replay(case['triangulation'],case['coordinates'],result['certificate'])
            replay_seconds=time.perf_counter()-at
        counts[result['status']]+=1
        records.append(dict(id=case['id'],n=len(case['coordinates']),status=result['status'],reason=result.get('reason'),
                            produce=produce_seconds,replay=replay_seconds))
    profile.disable();args.output.mkdir(parents=True,exist_ok=True)
    profile.dump_stats(str(args.output/'native_profile.pstats'))
    with (args.output/'native_profile.txt').open('w') as f:
        pstats.Stats(profile,stream=f).strip_dirs().sort_stats('cumtime').print_stats(80)
    report=dict(pin=PIN if args.variant=='baseline' else 'patched',variant=args.variant,
                corpus_sha256=hashlib.sha256(corpus).hexdigest(),counts=counts,
                seconds=time.perf_counter()-start,records=records)
    (args.output/'native_profile.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(dict(counts=counts,seconds=report['seconds'])))


if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--repo',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--variant',choices=('baseline','final'),default='baseline')
    args=p.parse_args()
    if args.variant=='final':run(args,args.repo/'Topology/UnknotRecognition/fast/fastunknot')
    else:
        with tempfile.TemporaryDirectory(prefix='unknot-profile-') as directory:
            archive=subprocess.check_output(['git','archive',PIN+':Topology/UnknotRecognition/fast/fastunknot'],cwd=args.repo)
            with tarfile.open(fileobj=io.BytesIO(archive)) as f:f.extractall(directory,filter='data')
            run(args,Path(directory))
