#!/usr/bin/env python3
"""Time-bounded source-family screening with an independent grammar auditor."""
import argparse
import json
from pathlib import Path
import subprocess
import sys
import time

HERE=Path(__file__).resolve().parent
PACK=HERE/'build/zfc-below245-source-search-20261018'

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--seconds',type=float,default=4)
    p.add_argument('--seeds',type=Path,default=HERE/'seeds')
    p.add_argument('--output',type=Path,default=HERE/'screen')
    p.add_argument('--max-initial',type=int,default=200)
    p.add_argument('--only-dne32',action='store_true')
    a=p.parse_args()
    sys.path.insert(0,str(PACK/'work/fine_grammar/runtime/code'))
    from audit_fine_grammar import audit
    a.output.mkdir(parents=True,exist_ok=True)
    results=[]
    for directory in sorted(a.seeds.glob('mask*')):
        if not (directory/'seed.json').exists(): continue
        seed=json.loads((directory/'seed.json').read_text())
        ident=int(directory.name[4:])
        if seed['rules_count']>a.max_initial:continue
        if a.only_dne32 and (ident-10000)%64!=32: continue
        out=a.output/directory.name
        out.mkdir(exist_ok=True)
        cand=out/'grammar.json'
        cmd=[str(HERE/'anneal_combined'),str(directory/'grammar.txt'),
             str(directory/'constraints.txt'),str(cand),str(a.seconds),
             str(202610180+ident),'127',str(PACK/'work/fine_grammar/fine-lock54.txt'),
             str(directory/'resume.txt')]
        t=time.monotonic()
        with (out/'search.log').open('w') as log:
            run=subprocess.run(cmd,stdout=log,stderr=subprocess.STDOUT)
        r=dict(mask=ident,initial_rules=seed['rules_count'],returncode=run.returncode,
               command=cmd,seconds=time.monotonic()-t)
        if run.returncode==0 and cand.exists():
            data=json.loads(cand.read_text())
            data['source_override']=seed['source_override']
            data['short_scan']=True
            data['status']='CANDIDATE_REQUIRES_COMPLETE_BINARY_AND_SOURCE_PROOFS'
            cand.write_text(json.dumps(data,indent=2)+'\n')
            try:
                report=audit(cand,short_scan=True)
                (out/'audit.json').write_text(json.dumps(report,indent=2)+'\n')
                r.update(status='GRAMMAR_PASS',rules=data['rules_count'],iterations=data['iterations'])
            except Exception as exc:
                r.update(status='GRAMMAR_FAIL',error=repr(exc))
        else: r['status']='SEARCH_DID_NOT_COMPLETE'
        results.append(r)
        (a.output/'summary.json').write_text(json.dumps(dict(
            scope='Time-bounded heuristic proposals; no minimality conclusion and no complete machine count',
            results=results),indent=2)+'\n')
        print(json.dumps({k:v for k,v in r.items() if k!='command'}),flush=True)
        if r.get('rules',999)<=127:
            print('STRICT_GRAMMAR_IMPROVEMENT_REQUIRES_VERIFICATION',flush=True)
            break

if __name__=='__main__': main()
