#!/usr/bin/env python3
"""Simultaneous association rewrites that share a common adjacent pair.

Groups different A;(B;C_i) contexts and rotates them together, or dually
(A_i;B);C. Exact full source control must agree after the whole rewrite.
"""
from collections import defaultdict
import json
import time
import rotation_search as r

def grouped_rotate(root,pivots,direction):
    memo={}
    def rec(i):
        if i in memo:return memo[i]
        v=r.entries[i]
        if v[0]!='N':return i
        left,right=v[1:]
        if i in pivots:
            if direction=='left':
                b,c=r.entries[right][1:]
                result=r.mk(('N',r.mk(('N',rec(left),rec(b))),rec(c)))
            else:
                a,b=r.entries[left][1:]
                result=r.mk(('N',rec(a),r.mk(('N',rec(b),rec(right)))))
        else:result=r.mk(('N',rec(left),rec(right)))
        memo[i]=result;return result
    return rec(root)

def main():
    start=time.monotonic();raw=r.a.PROGRAM.read_bytes();ls,cases,by,first=r.a.read_program(raw)
    original=r.load(raw);rotated=r.rotate(original,95,'left')
    results=[]
    for name,base in [('original',original),('rotated',rotated)]:
        counts=defaultdict(int)
        for direction in ['left','right']:
            groups=defaultdict(set)
            for p in r.reachable(base):
                _,a,b=r.entries[p]
                if direction=='left' and r.entries[b][0]=='N':
                    _,bb,c=r.entries[b];groups[(a,bb)].add(p)
                if direction=='right' and r.entries[a][0]=='N':
                    _,aa,bb=r.entries[a];groups[(bb,b)].add(p)
            for key,pivots in groups.items():
                if len(pivots)<2:continue
                candidate=grouped_rotate(base,pivots,direction)
                size=len(r.reachable(candidate));counts[size]+=1
                if size>202:continue
                z=r.check(candidate,ls,cases,set())
                if z is None:continue
                z.update(base=name,direction=direction,pivots=sorted(pivots),common_pair=key)
                results.append(z);r.dump_graph(candidate,r.OUT/f'rotation_factor_{len(results):02}.json',z)
                print(json.dumps(z),flush=True)
        print(json.dumps({'base':name,'size_histogram':dict(counts)}),flush=True)
    out={'results':results,'seconds':time.monotonic()-start}
    (r.OUT/'rotation_factor_results.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'successes':len(results),'minimum':min([z['unique_pairs'] for z in results],default=None),'seconds':out['seconds']}),flush=True)

if __name__=='__main__':main()
