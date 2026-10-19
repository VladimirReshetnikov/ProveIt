#!/usr/bin/env python3
"""Finite search for stronger guarded congruences, with exact certificates.
For every original state q and every mathematically admitted read b, its action
must equal the quotient action after target projection. This generalizes disjoint
symbol pairing. Ports and distinguished failures remain singleton classes.
No trace observation is used to select a read domain.
"""
if not __debug__:raise RuntimeError('Assertions required')
from pathlib import Path
import sys,random,json,time,argparse
HERE=Path(__file__).resolve().parent;sys.path.insert(0,str(HERE))
import build_library as B

def search(data,seeds=20):
    working=sorted(data['domains']);ports=sorted(data['ports']);states=working+ports
    ids={q:i for i,q in enumerate(states)};n=len(working)
    protected={ids[q]for q in data['protected']}|set(range(n,len(states)))
    admitted={i:[b for b in data['domains'][q]]for i,q in enumerate(working)}
    trans={(ids[q],b):(w,m,ids[t])for(q,b),(w,m,t)in data['rows'].items()}
    base=B.quotient(data)
    groups=[{ids[q]for q in g}for g in base['universal_classes']]+[{ids[q]}for q in ports]
    def trial(groups,i,j):
        groups=[set(g)for g in groups];where={q:k for k,g in enumerate(groups)for q in g};todo=[(next(iter(groups[i])),next(iter(groups[j])))];merges=0
        while todo:
            a,b=todo.pop();ga,gb=where[a],where[b]
            if ga==gb:continue
            if any(q in protected for q in groups[ga]|groups[gb]):return None
            members=groups[ga]|groups[gb];groups[ga]=members;groups[gb]=set();merges+=1
            for q in members:where[q]=ga
            for bit in (0,1):
                actions=[trans[q,bit]for q in members if bit in admitted[q]]
                if len(set((w,m)for w,m,t in actions))>1:return None
                if actions:
                    first=actions[0][2]
                    todo.extend((first,t)for w,m,t in actions[1:])
        return [g for g in groups if g]
    best=groups;log=[];beg=time.monotonic()
    for seed in range(seeds):
        rng=random.Random(1222246+seed);current=[set(g)for g in groups];checks=success=0
        while True:
            candidates=[(i,j)for i in range(len(current))for j in range(i)if not(current[i]&protected or current[j]&protected)]
            rng.shuffle(candidates);changed=False
            for i,j in candidates:
                checks+=1;merged=trial(current,i,j)
                if merged is not None:
                    current=merged;success+=1;changed=True;break
            if not changed:break
        if len(current)<len(best):best=current
        log.append({'seed':seed,'working_states':len(current)-len(ports),'tested_merges':checks,'accepted_merges':success,'best':len(best)-len(ports)})
        print(json.dumps(log[-1]),flush=True)
    classes=sorted([sorted(states[q]for q in g)for g in best if not g&set(range(n,len(states)))],key=lambda g:g[0])
    pi={q:i for i,g in enumerate(classes)for q in g};pids={q:len(classes)+i for i,q in enumerate(ports)};pi.update(pids)
    table={};certificate=[]
    for i,g in enumerate(classes):
        for b in (0,1):
            eligible=[q for q in g if b in data['domains'][q]];chosen=eligible[0]if eligible else g[0]
            w,m,t=data['rows'][chosen,b];table[i,b]=(w,m,pi[t])
            for q in eligible:
                w0,m0,t0=data['rows'][q,b];assert table[i,b]==(w0,m0,pi[t0]);certificate.append([q,b,i,w0,m0,pi[t0]])
    result={'table':table,'projection':pi,'classes':classes,'universal_classes':base['universal_classes'],'pairs':[], 'ports':pids,'entries':{k:pi[q]for k,q in data['entries'].items()},'structural':certificate,'guarded_search':log,'elapsed':time.monotonic()-beg}
    return result

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--seeds',type=int,default=10);p.add_argument('--selector-guards',action='store_true');p.add_argument('--comparator27',action='store_true');p.add_argument('--without-comparator',action='store_true');p.add_argument('--output',type=Path,default=HERE/'guarded_congruence');a=p.parse_args()
    d=B.build_retained(reverse_guards=True,selector_guards=a.selector_guards,comparator27=a.comparator27,include_compare=not a.without_comparator);r=search(d,a.seeds);m=B.save(d,r,a.output)
    m['forced_symbol_savings']=None;m['guarded_congruence_savings_after_universal']=len(r['universal_classes'])-len(r['classes']);m['packing_method']='Guarded row congruence; every admitted original row structurally checked, not merely disjoint pairing.'
    (a.output/'manifest.json').write_text(json.dumps(m,indent=2)+'\n')
    print(json.dumps({k:m[k]for k in ('working_states','rows','guarded_congruence_savings_after_universal','sha256')},indent=2))
