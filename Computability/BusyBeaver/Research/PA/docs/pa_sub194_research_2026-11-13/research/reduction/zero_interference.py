#!/usr/bin/env python3
"""Sound zero/nonzero abstraction for increment/decrement register programs.

Positive decrements nondeterministically leave zero or positive. This is an
overapproximation; absence of an interference proves safety of direct aliasing.
Presence does not disprove a stronger invariant.
"""
import argparse, collections, hashlib, json, pathlib, time

def analyze(path, entry=25):
    raw = path.read_bytes()
    ins = json.loads(raw)
    seen = [0] * len(ins)
    todo = collections.deque([(entry,1)])
    seen[entry] = 1<<1
    conflicts = [[set() for _ in range(9)] for _ in range(9)]
    masks = [[] for _ in ins]
    count=0
    def add(pc,mask):
        flag=1<<mask
        if not seen[pc]&flag:
            seen[pc]|=flag; todo.append((pc,mask))
    while todo:
        pc,mask=todo.popleft(); count+=1
        masks[pc].append(mask)
        x=ins[pc]
        if x[0] in ('inc','dec'):
            r=x[1]
            for s in range(9):
                if s!=r and mask>>s&1:
                    conflicts[min(r,s)][max(r,s)].add(pc)
            if x[0]=='inc':add(x[2],mask|1<<r)
            elif not mask>>r&1:add(x[2],mask)
            else:add(x[3],mask);add(x[3],mask&~(1<<r))
        elif x[0]=='jump':add(x[1],mask)
        elif x[0]=='halt':pass
        else:raise ValueError(x)
    result={'program':str(path),'sha256':hashlib.sha256(raw).hexdigest(),
            'entry':entry,'initial_nonzero_mask':1,'reachable_abstract_states':count,
            'reachable_sites':sum(bool(x) for x in seen),'sites':len(ins),
            'sound_abstraction':'0/positive; positive decrement branches to 0 or positive',
            'pair_interference':[{'pair':[r,s],'conflicting_sites':len(conflicts[r][s]),
                                  'first_sites':sorted(conflicts[r][s])[:20]}
                                 for r in range(9) for s in range(r+1,9)],
            'known_zero_at_site':[[r for r in range(9) if all(not m>>r&1 for m in ms)]
                                  if ms else None for ms in masks],
            'known_positive_at_site':[[r for r in range(9) if all(m>>r&1 for m in ms)]
                                  if ms else None for ms in masks]}
    return result

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('input',type=pathlib.Path);p.add_argument('output',type=pathlib.Path)
    a=p.parse_args();t=time.monotonic();r=analyze(a.input)
    r['elapsed_seconds']=round(time.monotonic()-t,3)
    a.output.write_text(json.dumps(r,indent=2)+'\n')
    print(json.dumps({k:v for k,v in r.items() if not k.endswith('_at_site')},indent=2))
