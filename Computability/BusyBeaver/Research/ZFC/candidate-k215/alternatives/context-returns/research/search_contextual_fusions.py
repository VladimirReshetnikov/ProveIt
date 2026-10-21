#!/usr/bin/env python3
"""Reproduce a restricted contextual-fusion search and exact rejection filter.

This is synthesis, not an acceptance certificate. The search considers pairs
of pure decoder states sharing one transition, synthesizes a two-row helper
from existing targets, and tries to reuse each existing state as that helper.
A trial passes a full-prefix and primitive-delivery-class filter. Quantified
primitive derivations then reject it, or leave it explicitly UNACCEPTED.

Only rejected trials were found in the recorded experiment. No lower bound
on Turing-machine size follows from this finite search.
"""
from pathlib import Path
from collections import defaultdict
import argparse, hashlib, itertools, json, sys, time

def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p, x): p.write_text(json.dumps(x, indent=2, sort_keys=True)+'\n')

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    for name in ('table','sites','engine','mapping','witnesses','support-dir','runtime-dir','output'):
        ap.add_argument('--'+name,type=Path,required=True)
    ap.add_argument('--keep-trials',action='store_true')
    args=ap.parse_args()
    if not __debug__: raise RuntimeError('Assertions must be enabled')
    args.output.mkdir(parents=True,exist_ok=False)
    sys.path[:0]=[str(args.support_dir.resolve()),str(args.runtime_dir.resolve())]
    import build221 as b
    import source_language as sl
    import symbolic_runtime as sr
    started=time.monotonic()
    T=b.read_table(args.table.read_bytes())
    sites=json.loads(args.sites.read_text());tree=sl.tree(sites)
    groups,paths=b.decoder_map(T,tree)
    states={q for q,_ in T}
    engine={tuple(r)for r in json.loads(args.engine.read_text())['rows']}
    pure=[q for q in paths if q!=84 and all(T[q,j][:2]==(j,1)and(q,j)not in engine for j in(0,1))]
    pairs=[(bit,q,r)for bit in(0,1)for q,r in itertools.combinations(pure,2)
           if T[q,1-bit]==T[r,1-bit]and T[q,bit]!=T[r,bit]]
    actions={(w,d,q)for q in states for d in(-1,1)for w in(0,1)}

    def continuation(word,action,target,excluded):
        tape=[1]+[int(c)for c in word];before=tape[:]
        head=len(word)-1;state=None;used=set();seen=set()
        for tick in range(80):
            if tick and head==len(tape):
                return used if state==target and tape==before else None
            if not 0<=head<len(tape):return None
            if tick:
                if state in excluded:return None
                key=state,head,tuple(tape)
                if key in seen:return None
                seen.add(key);used.add(state)
                if(state,tape[head])not in T:return None
            w,d,state=action if tick==0 else T[state,tape[head]]
            tape[head]=w;head+=d
        return None

    profiles={};interiors={}
    for P in pairs:
        bit,q,r=P;allowed={j:set(actions)for j in(0,1)}
        used={j:defaultdict(set)for j in(0,1)}
        for z in(q,r):
            for prefix in paths[z]:
                marker=int(prefix[-1]);word=prefix+str(bit);target=T[z,bit][2]
                for action in list(allowed[marker]):
                    touched=continuation(word,action,target,{q,r})
                    if touched is None:allowed[marker].remove(action)
                    else:used[marker][action].update(touched)
                if not allowed[marker]:break
            if any(not allowed[j]for j in(0,1)):break
        if all(allowed[j]for j in(0,1)):profiles[P]=allowed;interiors[P]=used

    leaf_actions=defaultdict(set)
    for q,nodes in groups.items():
        for node in nodes:
            for bit,child in enumerate(node):
                if sl.leaf(child):leaf_actions[child,bit].add(T[q,bit])
    for op,arg,q in [('CC',1,1),('CC',2,16),('CB',1,302)]:
        leaf_actions[(op,arg),1].add((0,-1,q))
    mapping={int(k):int(v)for k,v in json.loads(args.mapping.read_text()).items()}
    for q in states|{254}:mapping.setdefault(q,q+1000)
    witnesses={tuple(x['row']):tuple(x['case'])for x in json.loads(args.witnesses.read_text())}
    records=[];specifications=0;prefix_pass=0
    for P,allowed in profiles.items():
        bit,q,r=P
        for x,y in itertools.product(sorted(allowed[0]),sorted(allowed[1])):
            touched=interiors[P][0][x]|interiors[P][1][y]
            for helper in sorted(states-{q,r}-touched):
                specifications+=1
                N={(z,j):(w,d,q if t==r else t)for(z,j),(w,d,t)in T.items()if z!=r}
                N[q,bit]=(bit,-1,helper);N[helper,0]=x;N[helper,1]=y
                try:new_groups,_=b.decoder_map(N,tree)
                except Exception:continue
                prefix_pass+=1
                if not all(N[z,j]in leaf_actions[child,j]
                           for z,nodes in new_groups.items()for node in nodes
                           for j,child in enumerate(node)if sl.leaf(child)):continue
                raw=b.table_bytes(N);record=dict(pair=P,helper=helper,helper_rows=[x,y],
                    deleted_state=r,declared_working_states=len(N)//2,table_sha256=hashlib.sha256(raw).hexdigest())
                L={(mapping[z],j):(w,d,mapping[t])for(z,j),(w,d,t)in N.items()}
                record['status']='UNACCEPTED_FILTER_SURVIVOR'
                try:
                    lemmas,_=sr.prove_blocks(L)
                    tests=sorted({witnesses[helper,j]for j in(0,1)if(helper,j)in witnesses})
                    record['test_cases']=tests
                    for site_index,positive in tests:
                        record['current_case']=[site_index,positive]
                        sr.case(L,lemmas,sites[site_index],positive)
                except Exception as exc:
                    record['status']='REJECTED_BY_QUANTIFIED_DERIVATION'
                    record['reason']=str(exc)
                records.append(record)
                if args.keep_trials or record['status']=='UNACCEPTED_FILTER_SURVIVOR':
                    (args.output/f'trial_{len(records):04d}.native.tm').write_bytes(raw)
                if len(records)%50==0:print('filtered',len(records),flush=True)
    pins={k:digest(getattr(args,k))for k in('table','sites','engine','mapping','witnesses')}
    pins.update(build221=digest(Path(b.__file__)),source_language=digest(Path(sl.__file__)),
                symbolic_runtime=digest(Path(sr.__file__)),independent_runtime=digest(Path(sr.r.__file__)))
    receipt=dict(status='SEARCH_COMPLETE_NO_ACCEPTED_CANDIDATE',scope=__doc__,inputs=pins,
        pair_count=len(pairs),pairs_with_synthesizable_helpers=len(profiles),specifications=specifications,
        prefix_pass=prefix_pass,delivery_class_pass=len(records),
        rejected=sum(r['status']=='REJECTED_BY_QUANTIFIED_DERIVATION'for r in records),
        unaccepted_survivors=sum(r['status']=='UNACCEPTED_FILTER_SURVIVOR'for r in records),
        seconds=time.monotonic()-started,trials=records)
    dump(args.output/'receipt.json',receipt)
    print(json.dumps({k:v for k,v in receipt.items()if k not in('scope','inputs','trials')},indent=2))
if __name__=='__main__':main()
