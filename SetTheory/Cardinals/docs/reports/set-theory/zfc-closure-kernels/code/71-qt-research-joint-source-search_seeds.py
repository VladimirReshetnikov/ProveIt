#!/usr/bin/env python3
"""Bounded parallel discovery with independent post-search grammar checks."""
import argparse
import concurrent.futures
import json
from pathlib import Path
import subprocess
import sys
import time


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--seeds', type=Path, required=True)
    ap.add_argument('--fine', type=Path, required=True)
    ap.add_argument('--executable', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--seconds', type=float, default=20)
    ap.add_argument('--jobs', type=int, default=4)
    ap.add_argument('--dne-mask', type=int, default=32)
    args = ap.parse_args()
    sys.path.insert(0, str(args.fine.resolve()/'runtime/code'))
    from audit_fine_grammar import audit
    args.output.mkdir(parents=True, exist_ok=True)
    seeds = [p for p in args.seeds.glob('mask*/seed.json')
             if int(p.parent.name[4:]) % 64 == args.dne_mask]
    seeds.sort(key=lambda p:int(p.parent.name[4:]))

    def one(p):
        mask = int(p.parent.name[4:])
        seed = json.loads(p.read_text())
        out = args.output/p.parent.name
        out.mkdir(exist_ok=True)
        dest = out/'candidate.json'
        command = [str(args.executable.resolve()), str((p.parent/'grammar.txt').resolve()),
                   str((p.parent/'constraints.txt').resolve()), str(dest.resolve()),
                   str(args.seconds), str(2026101900+mask), '127',
                   str((args.fine/'fine-lock54.txt').resolve()),
                   str((p.parent/'resume.txt').resolve())]
        start = time.monotonic()
        with (out/'search.log').open('w') as log:
            proc = subprocess.run(command, stdout=log, stderr=subprocess.STDOUT)
        rec = dict(mask=mask, command=command, returncode=proc.returncode,
                   seconds=time.monotonic()-start, initial_rules=seed['rules_count'])
        if proc.returncode == 0:
            data = json.loads(dest.read_text())
            data['source_override'] = seed['source_override']
            data['short_scan'] = True
            data['status'] = 'SOURCE_GRAMMAR_ONLY_REQUIRES_BINARY_AND_LOGIC_CALIBRATION'
            dest.write_text(json.dumps(data, indent=2)+'\n')
            rec.update(rules=data['rules_count'], properties=data['properties'],
                       proposals=data['iterations'])
            try:
                result=audit(dest,short_scan=True)
                (out/'audit.json').write_text(json.dumps(result,indent=2)+'\n')
                rec['audit_status']=result['status']
                rec['working_states_charged']=result['working_states']
            except Exception as err:
                rec['audit_status']='FAILED'
                rec['error']=repr(err)
        else:
            rec['audit_status']='SEARCH_PROCESS_FAILED'
        print(json.dumps({k:v for k,v in rec.items() if k!='command'}),flush=True)
        (out/'result.json').write_text(json.dumps(rec,indent=2)+'\n')
        return rec
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        results = list(pool.map(one,seeds))
    (args.output/'summary.json').write_text(json.dumps(dict(
        scope='Time-bounded source grammar discovery; neither a machine lower bound nor binary verification.',
        results=results),indent=2)+'\n')


if __name__=='__main__':
    main()
