"""Paired complete recognition with an optional certified Garside probe.

All existing cheap certificates remain enabled. Timers include probe search,
independent replay, candidate construction and restarted recognition. Each call
uses a fresh validated Diagram prepared outside timing. Inputs and common imports
are excluded; no raw-scanner ablation is presented as a pipeline speedup.
"""
import argparse
import gc
import hashlib
import json
from math import ceil
from pathlib import Path
import platform
import random
import statistics
import sys
from time import perf_counter

FAST = Path(__file__).resolve().parents[1]
sys.path.insert(0,str(FAST))
from fastunknot import Diagram, recognize
from fastunknot.cyclic_garside.oracles import old_barrier, inverse_word, geodesic_unknot


def cases():
    def braid(name, b, word):
        return name, {'braid': {'strands':b, 'word':list(word)}}
    rows = [braid('barrier_h4',4,old_barrier(4)),
            braid('rectangle_m16',4,(-1,)*16+(3,)*16+(1,)*17+(-3,)*15+(2,)),
            braid('geodesic_m12',3,geodesic_unknot(12)),
            braid('hidden_sleeve_m8',3,(1,2,1)+(1,)*8+(1,2)+inverse_word((2,1,2)+(1,)*8))]
    rng = random.Random(2026100825)
    for m in (2,8,16):
        for core_name, core in (('unknot',(1,2,3)), ('figure8',(1,-2,1,-2,3)),
                                ('positive',(1,2,3)*3)):
            for length in (8,16):
                u = tuple(rng.choice((-3,-2,-1,1,2,3)) for _ in range(length))
                word = u+old_barrier(m)[:-3]+inverse_word(u)+core
                rows.append(braid(f'{core_name}_h{m}_u{length}',4,word))
    for name in ('conway','hard_unknot_8','stress_braid5_36'):
        rows.append((name,json.loads((FAST/'examples'/f'{name}.json').read_text())))
    return rows


def evidence_summary(result):
    probe = result.evidence.get('garside')
    if 'before_garside' in result.evidence:
        probe = result.evidence['before_garside']['garside']
    return dict(status=result.status, method=result.method,
                reduced_crossings=result.reduced_crossings,
                probe=None if probe is None else {k:probe[k] for k in
                    ('status','used','ticks','reason','statistics') if k in probe})


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--rounds',type=int,default=7)
    args=parser.parse_args()
    if args.rounds<1:
        parser.error('rounds must be positive')
    arms={'off':{},'control':{},'radius1':dict(use_garside=True,garside_radius=1),
          'radius2':dict(use_garside=True,garside_radius=2)}
    rng=random.Random(2026100826)
    source_files=[*sorted((FAST/'fastunknot/cyclic_garside').glob('*.py')),
                  FAST/'fastunknot/garside_probe.py',FAST/'fastunknot/recognize.py',
                  FAST/'fastunknot/diagram.py',FAST/'fastunknot/scan_fast.py']
    data=dict(scope=__doc__,python=platform.python_version(),rounds=args.rounds,
              seed=2026100826,fixture_seed=2026100825,global_seconds=2,max_objects=50000,
              local_seconds=0.1,max_ticks=100000,max_targets=100000,
              timing='seven shuffled paired warm rounds; gc enabled, collect before batch',
              batch_target_seconds=0.015,batch_cap=16,
              source_sha256={str(p.relative_to(FAST)):hashlib.sha256(p.read_bytes()).hexdigest()
                             for p in source_files},
              driver_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),cases=[])
    def call(d,arm):
        return recognize(d,seconds=2,max_objects=50000,**arms[arm])
    for name,source in cases():
        repetitions={}
        for arm in arms:
            d=Diagram.from_json(source)
            start=perf_counter();call(d,arm);elapsed=perf_counter()-start
            repetitions[arm]=min(16,max(1,ceil(0.015/elapsed)))
        repetitions['off']=repetitions['control']=max(repetitions['off'],repetitions['control'])
        samples=[]
        expected=None
        for _ in range(args.rounds):
            order=list(arms);rng.shuffle(order);sample=dict(order=order,seconds={},results={})
            for arm in order:
                batch=[Diagram.from_json(source) for _ in range(repetitions[arm])]
                gc.collect()
                start=perf_counter()
                answers=[call(d,arm) for d in batch]
                elapsed=(perf_counter()-start)/len(batch)
                for answer in answers:
                    if answer.status!='UNKNOWN':
                        if expected is None: expected=answer.status
                        assert answer.status==expected,(name,arm,answer.status,expected)
                sample['seconds'][arm]=elapsed
                sample['results'][arm]=[evidence_summary(a) for a in answers]
            samples.append(sample)
        ratios={}
        for arm in ('control','radius1','radius2'):
            if all(a['status']!='UNKNOWN' for s in samples for key in ('off',arm) for a in s['results'][key]):
                ratios['off_over_'+arm]=statistics.median(s['seconds']['off']/s['seconds'][arm] for s in samples)
            else:
                ratios['off_over_'+arm]=None
        row=dict(name=name,source=source,crossings=Diagram.from_json(source).crossings,
                 repetitions=repetitions,samples=samples,paired_ratios=ratios,
                 median_seconds={a:statistics.median(s['seconds'][a] for s in samples) for a in arms})
        data['cases'].append(row)
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(data,indent=2)+'\n')
        print(name,json.dumps(ratios),flush=True)


if __name__=='__main__':
    main()
