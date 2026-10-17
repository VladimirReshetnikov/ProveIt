#!/usr/bin/env python3
"""Full relational finite abstraction of nine natural registers.

A register has singleton atoms 0..cap-1 and a final >=cap atom. Each control
stores an arbitrary subset of all (cap+1)^9 tuples, retaining all correlations.
Unbounded counters are overapproximated: decrement(>=cap) may be cap-1 or >=cap.
The returned postfix certificate concerns the source RM, never a changed TM.
"""
from __future__ import annotations
import argparse
from collections import defaultdict,deque
import hashlib,json,time,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'upstream/Computability/BusyBeaver/Research/ZFC'))
import permutation252_phase_analysis as original

def masks(base):
    size=base**9;allbits=(1<<size)-1
    values=[]
    for r in range(9):
        weight=base**r;stride=weight*base
        rep=allbits//((1<<stride)-1)
        m0=((1<<weight)-1)*rep
        values.append(tuple(m0<<(j*weight) for j in range(base)))
    return values

def analyze(sites,cases,targets,first,cap):
    base=cap+1;by_site=defaultdict(list)
    for i,c in enumerate(cases):by_site[c[0]].append(i)
    bitmasks=masks(base);weights=[base**r for r in range(9)]
    zero_masks=[m[0] for m in bitmasks]
    last_masks=[m[-1] for m in bitmasks]
    allbits=(1<<(base**9))-1
    positive_masks=[allbits^m[0] for m in bitmasks]
    nonlast_masks=[allbits^m[-1] for m in bitmasks]
    def transfer(v,case):
        _,_,op,r,zero=case
        if op=='CI':return ((v&nonlast_masks[r])<<weights[r])|(v&last_masks[r])
        if op=='CD':
            if zero:return v&zero_masks[r]
            return ((v&positive_masks[r])>>weights[r])|(v&last_masks[r])
        return v
    values=[0]*len(sites);delta=[0]*len(sites)
    values[first]=delta[first]=1;pending=deque([first]);queued={first};pops=0
    start=time.perf_counter();reported=start
    while pending:
        site=pending.popleft();queued.remove(site);pops+=1
        change=delta[site];delta[site]=0
        for index in by_site[site]:
            target=targets[index]
            if target is None:continue
            new=transfer(change,cases[index])&~values[target]
            if new:
                values[target]|=new;delta[target]|=new
                if target not in queued:pending.append(target);queued.add(target)
        if pops%100000==0 and time.perf_counter()-reported>15:
            print(json.dumps({'progress_pops':pops,'queue':len(pending),'seconds':time.perf_counter()-start}),flush=True)
            reported=time.perf_counter()
    assert values[first]&1
    excluded=[];edges=0
    for index,(case,target) in enumerate(zip(cases,targets)):
        after=transfer(values[case[0]],case)
        if not after:excluded.append(index)
        elif target is not None:
            assert after&~values[target]==0
            edges+=1
    return values,excluded,edges,pops,time.perf_counter()-start

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--cap',type=int,default=2)
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args();assert 1<=a.cap<=3
    raw=(ROOT/'upstream/lib/jeff-busy-beaver-zfc254/ZF/m254/coq/tm/Prog254.v').read_bytes()
    sites,cases,targets,first=original.program_graph(raw)
    values,excluded,edges,pops,seconds=analyze(sites,cases,targets,first,a.cap)
    result={'scope':__doc__,'cap':a.cap,'tuple_count_per_control':(a.cap+1)**9,
            'source_sha256':hashlib.sha256(raw).hexdigest(),'pops':pops,'edges':edges,
            'seconds':seconds,'excluded':excluded,
            'additional_exclusions':sorted(set(excluded)-set(original.EXCLUDED)),
            'max_abstract_tuples_at_control':max(v.bit_count() for v in values),
            'total_reached_abstract_tuples':sum(v.bit_count() for v in values)}
    a.output.parent.mkdir(parents=True,exist_ok=True)
    result['postfix_certificate_masks_hex']=[hex(v) for v in values]
    a.output.write_text(json.dumps(result,indent=2)+'\n')
    del result['postfix_certificate_masks_hex'];print(json.dumps(result),flush=True)
if __name__=='__main__':main()
