#!/usr/bin/env python3
"""Finite exact-small-value/residue abstract interpretation of literal Prog254.

This is a source-program invariant certificate checker, not a TM simulation.
Tail atoms represent {cap+j+k*period : k>=0}; finite atoms represent singletons.
"""
from __future__ import annotations
import argparse
from collections import defaultdict, deque
import hashlib
import json
from pathlib import Path
import sys
import time

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'upstream/Computability/BusyBeaver/Research/ZFC'))
import permutation252_phase_analysis as original

class Domain:
    def __init__(self,cap,period):
        assert cap>=2 and period>=1
        self.cap,self.period=cap,period
        self.low=(1<<cap)-1
        self.high=(1<<period)-1
        self.full=(1<<(cap+period))-1
    def inc(self,value):
        tail=value>>self.cap
        rotate=((tail<<1)|(tail>>(self.period-1)))&self.high
        return ((value<<1)&self.low)|((rotate|((value>>(self.cap-1))&1))<<self.cap)
    def dec(self,value):
        tail=value>>self.cap
        rotate=(tail>>1)|((tail&1)<<(self.period-1))
        return ((value&self.low)>>1)|(rotate<<self.cap)|((tail&1)<<(self.cap-1))
    def transfer(self,values,case):
        _,_,op,r,zero=case
        result=list(values)
        if op=='CI':result[r]=self.inc(result[r])
        elif op=='CD':
            if zero:
                if not result[r]&1:return None
                result[r]=1
            else:
                if not result[r]&~1:return None
                result[r]=self.dec(result[r]&~1)
        return tuple(result)

def analyze(sites,cases,targets,first,domain):
    by_site=defaultdict(list)
    for index,case in enumerate(cases):by_site[case[0]].append(index)
    values=[None]*len(sites);values[first]=(1,)*9
    queue=deque([first]);queued={first};pops=0
    while queue:
        site=queue.popleft();queued.remove(site);pops+=1
        for index in by_site[site]:
            target=targets[index]
            if target is None:continue
            after=domain.transfer(values[site],cases[index])
            if after is None:continue
            old=values[target]
            joined=after if old is None else tuple(a|b for a,b in zip(old,after))
            if old!=joined:
                values[target]=joined
                if target not in queued:queue.append(target);queued.add(target)
    enabled=[];edges=0
    assert all(v&1 for v in values[first])
    for case,target in zip(cases,targets):
        old=values[case[0]]
        after=None if old is None else domain.transfer(old,case)
        enabled.append(after is not None)
        if after is not None and target is not None:
            assert values[target] is not None
            assert all(a&~b==0 for a,b in zip(after,values[target]))
            edges+=1
    return values,enabled,pops,edges

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--caps',type=int,nargs='+',default=[2,3,4,8,16,32])
    parser.add_argument('--periods',type=int,nargs='+',default=[1,2,4,8])
    args=parser.parse_args()
    raw=(ROOT/'upstream/lib/jeff-busy-beaver-zfc254/ZF/m254/coq/tm/Prog254.v').read_bytes()
    sites,cases,targets,first=original.program_graph(raw)
    results=[];best=None
    for cap in args.caps:
        for period in args.periods:
            start=time.perf_counter();domain=Domain(cap,period)
            values,enabled,pops,edges=analyze(sites,cases,targets,first,domain)
            excluded=[i for i,yes in enumerate(enabled) if not yes]
            result={'cap':cap,'period':period,'pops':pops,'edges':edges,
                    'seconds':time.perf_counter()-start,'excluded':excluded,
                    'additional_exclusions':sorted(set(excluded)-set(original.EXCLUDED))}
            results.append(result);print(json.dumps(result),flush=True)
            if best is None or len(excluded)>len(best['excluded']):
                best={**result,'values':values}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps({'scope':__doc__,'source_sha256':hashlib.sha256(raw).hexdigest(),
        'results':results,'best':best},indent=2)+'\n')
if __name__=='__main__':main()
