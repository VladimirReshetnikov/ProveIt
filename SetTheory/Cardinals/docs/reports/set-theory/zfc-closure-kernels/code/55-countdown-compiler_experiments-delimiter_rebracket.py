#!/usr/bin/env python3
"""Joint decoder layout / delimiter-cost experiment on permutation252.

Closed rotations preserve the ordered program word and binding depths. The
candidate emitter adapts attributed source27's existing fingerprint emission
to the current physical-register permutation; its output is untrusted data.
State counts here use literal graph reachability from blank start64. A shorter
delimiter is attempted only when every source path has at most6 consecutive0s.
Such a shape condition alone is NOT a simulation or startup proof.
"""
from __future__ import annotations
import argparse
from collections import Counter,deque
from functools import lru_cache
import hashlib,importlib.util,json,random,sys,time
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
UP=ROOT/'upstream';Z=UP/'Computability/BusyBeaver/Research/ZFC'
HOST=UP/'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels'
CODE=HOST/'code';DATA=HOST/'data'
sys.path.insert(0,str(Z))
import candidate252_independent_audit as audit
for mod in ('dag_tools','rotate_search'):
    spec=importlib.util.spec_from_file_location(mod,CODE/f'27-variant-experiments-machine_search-grammar_search-{mod}.py')
    module=importlib.util.module_from_spec(spec);sys.modules[mod]=module;spec.loader.exec_module(module)
import rotate_search as rot

OLD=json.loads((DATA/'27-variant-experiments-machine_search-grammar_search-decoder_entries.json').read_text())
NODES={int(k):tuple(map(tuple,v)) for k,v in OLD['nodes'].items()}
ENTRY=OLD['root'];OLD_FP={v:int(n) for n,v in OLD['fingerprints'].items()}
BASE=audit.read_table((Z/'candidate-permutation252/zfc_permutation252_old.tm').read_bytes())
CONTROLS={}
for n,pair in NODES.items():
    for b,e in enumerate(pair):
        if e[0] not in 'BC':continue
        counts=CONTROLS.setdefault((e,b),Counter())
        for state,weight in OLD['state_entries'][str(n)].items():counts[BASE[int(state),b]]+=weight

def emit(nodes,root,short_delimiter=False):
    @lru_cache(None)
    def fingerprint(e):
        if e[0]=='N':
            a,b=nodes[e[1]];s='N('+fingerprint(a)+','+fingerprint(b)+')'
        else:s=':'.join(map(str,e))
        return hashlib.sha256(s.encode()).hexdigest()
    table=BASE.copy();entries={};allocate=255
    modal=lambda d:max(d,key=d.get)
    for n in nodes:
        f=fingerprint(('N',n))
        if n==root:entries[n]=96
        elif f in OLD_FP:entries[n]=int(modal(OLD['state_entries'][str(OLD_FP[f])]))
        else:entries[n]=allocate;allocate+=1
    def action(e,b):
        if e[0]=='N':return b,'R',entries[e[1]]
        if e[0]=='B' and e[1]==1:return 0,'L',7 if b==0 else 33
        if e[0] in 'BC':return CONTROLS[e,b].most_common(1)[0][0]
        return b,'R',int(modal(OLD['leaf_entries'][':'.join(map(str,e))]))
    for n in nodes:
        if entries[n]==96 or fingerprint(('N',n)) not in OLD_FP:
            for b,e in enumerate(nodes[n]):table[entries[n],b]=action(e,b)
    if short_delimiter:
        assert rot.zero_metrics(nodes,root)[1]<=6
        table={key:(w,d,84 if t==74 else t) for key,(w,d,t) in table.items() if key[0]!=74}
    return table

def prune(table):
    states={64};todo=[64]
    while todo:
        q=todo.pop()
        for b in (0,1):
            target=table[q,b][2]
            if target!=254 and target not in states:states.add(target);todo.append(target)
    return {k:v for k,v in table.items() if k[0] in states}

def metric(nodes,root):
    @lru_cache(None)
    def f(e,run):
        if e[0]!='N':return int(run>=7)
        a,b=nodes[e[1]]
        # Count path violations even when a long run ends before the leaf.
        return g(a,run+1,run+1>=7)+g(b,0,False)
    @lru_cache(None)
    def g(e,run,bad):
        if e[0]!='N':return int(bad)
        a,b=nodes[e[1]]
        return g(a,run+1,bad or run+1>=7)+g(b,0,bad)
    bad=g(('N',root),0,False)
    prefix,zero,depth=rot.zero_metrics(nodes,root)
    try:table=prune(emit(nodes,root,zero<=6));states=len(table)//2
    except KeyError:return (10**6,bad,depth,len(nodes)),None
    return (states,bad,depth,len(nodes)),table

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--rounds',type=int,default=10)
    p.add_argument('--width',type=int,default=12)
    a=p.parse_args();a.output.mkdir(parents=True,exist_ok=True)
    assert emit(NODES,ENTRY)==BASE
    initial_metric,initial_table=metric(NODES,ENTRY)
    beam=[(NODES,ENTRY,[],initial_metric)];seen=set();rounds=[];best=None;start=time.perf_counter()
    for round in range(a.rounds):
        pool=[];examined=Counter()
        for nodes,root,history,score in beam:
            for q,exp,kind in rot.options(nodes):
                nn,rr=rot.mutate(nodes,root,q,exp)
                key=rot.unfold(nn,rr)
                if key in seen:continue
                seen.add(key);m,table=metric(nn,rr);examined['evaluated']+=1
                if m[2]>39 or m[0]>300:continue
                # Only decrease the bad-path frontier. This is a bounded greedy
                # beam family, deliberately not an exhaustive reassociation claim.
                if m[1]>=score[1]:continue
                h=history+[{'node':q,'kind':kind,'expression':exp}]
                item=(nn,rr,h,m)
                if m[1]==0:
                    examined['zero6_layouts']+=1
                    if best is None or m<best[3]:
                        best=item
                        (a.output/'best_dag.json').write_text(json.dumps({'root':rr,'nodes':nn,'history':h,'metric':m},indent=2)+'\n')
                        (a.output/'best_unvalidated.tm').write_bytes(audit.encode(table))
                        print(json.dumps({'new_best':m,'rotations':len(h)}),flush=True)
                else:pool.append(item)
        pool.sort(key=lambda x:(x[3][1],x[3][0],x[3][2],x[3][3]))
        beam=pool[:a.width]
        record={'round':round+1,**examined,'frontier':len(beam),
                'best_frontier':beam[0][3] if beam else None,'seconds':time.perf_counter()-start}
        rounds.append(record);print(json.dumps(record),flush=True)
        if not beam:break
    result={'scope':__doc__,'initial_metric':initial_metric,
            'rounds':rounds,'best_metric':best[3] if best else None,
            'best_rotation_count':len(best[2]) if best else None,
            'seen_layouts':len(seen),'seconds':time.perf_counter()-start,
            'search_rule':'strictly reduce number of leaves containing7zero run, width-limited beam',
            'binary_contract_checked':False,'blank_entry_checked':False,'new_ZFC_state_bound':False}
    (a.output/'results.json').write_text(json.dumps(result,indent=2)+'\n')
if __name__=='__main__':main()
