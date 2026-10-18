#!/usr/bin/env python3
"""Reproduce a bounded, local incoming-edge action search.

Successful local domains are NOT successful deletions: simultaneous reroutes
must be checked separately. Unchanged register-macro rows are prerequisites
of these symbolic oracles. Python 3.10+; standard library only.
"""
from pathlib import Path
from collections import Counter,defaultdict
import argparse,importlib,itertools,json,sys,time
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'code'))
import common as C

def main():
    if not __debug__:raise SystemExit('Assertions required; do not use -O.')
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--oracle',choices=('strict','source','exact','quiet','workspace','combined','arithmetic'),default='arithmetic')
    ap.add_argument('--seconds',type=float,help='Optional time limit; a cutoff is reported as partial.')
    ap.add_argument('--output',type=Path,default=ROOT/'results/recomputed-incoming.json')
    args=ap.parse_args()
    names=dict(source='source_invariant_affine',exact='source_exactroot_affine',
        quiet='source_block_affine',workspace='workspace_affine',
        combined='workspace_block_affine',arithmetic='arithmetic_affine')
    A=C.A if args.oracle=='strict' else importlib.import_module(names[args.oracle])
    cases=C.cases if args.oracle=='strict' else [c for c in C.cases if A.case_allowed(c[0],c[1])]
    table=C.T
    protected={2,4,6,20,48,63,73,75,83,95,109,112,131,255,60,44,31,56,38,40,28,64,69}
    states=sorted({int(q) for q,b in table})
    class Tracking(dict):
        def __getitem__(self,k):
            self.keys_read.add(k);return super().__getitem__(k)
    tracked=Tracking(table);uses=defaultdict(list)
    for i,(p,branch,target,halt) in enumerate(cases):
        tracked.keys_read=set()
        A.run(tracked,p,branch,target,halt=halt,fuel=1000)
        for key in tracked.keys_read:uses[key].append(i)
    incoming=defaultdict(list)
    for key,row in table.items():
        if key[0]!=row[2]:incoming[int(row[2])].append(key)
    began=time.monotonic();tested=0;records=[];possible=[];complete=True
    for removed in sorted(states,key=lambda q:(len(incoming[q]),q)):
        if removed in protected or removed==96:continue
        edges=sorted(incoming[removed],key=lambda e:-len(uses[e]))
        if any(int(e[0]) in protected for e in edges):continue
        choices={};missing=None
        for edge in edges:
            alternatives=[];failures=Counter();w0,d0,_=table[edge]
            actions=sorted(itertools.product((0,1),('L','R'),[str(q) for q in states+[254] if q!=removed]),
                key=lambda a:(a[0]!=w0,a[1]!=d0,int(a[2])))
            for action in actions:
                if args.seconds is not None and time.monotonic()-began>=args.seconds:
                    complete=False;break
                candidate=table.copy();candidate[edge]=action;valid=True
                for i in sorted(uses[edge],key=lambda i:-failures[i]):
                    p,branch,target,halt=cases[i]
                    try:A.run(candidate,p,branch,target,halt=halt,fuel=1000)
                    except (AssertionError,KeyError):
                        failures[i]+=1;valid=False;break
                tested+=1
                if valid:alternatives.append(action)
            if not complete:break
            choices[str(edge)]=alternatives
            if not alternatives:missing=edge;break
        if not complete:break
        record=dict(state=removed,choices=choices,missing=missing)
        records.append(record)
        if missing is None:possible.append(record)
        print('state',removed,'trials',tested,'locally_admissible',missing is None,flush=True)
    result=dict(status='completed' if complete else 'partial',oracle=args.oracle,
        tested=tested,guard_cases=len(cases),seconds=time.monotonic()-began,
        candidates=possible,states=records,
        scope='Local sufficient-checker action domains, not successful joint state deletions.')
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('states','candidates')},indent=2))
if __name__=='__main__':main()
