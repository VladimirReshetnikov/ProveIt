#!/usr/bin/env python3
"""Search exact-word compiler reductions of the retained 268-state source.

Inputs are pinned ProveIt source-19 artifacts and the upstream Wade backend.
Searches use overlap-safe Re-Pair and charge the actual zero-run dispatcher.
This is a compiler control, not an end-to-end ZFC consistency construction.
"""
from __future__ import annotations
import argparse, hashlib, importlib.util, json, random, sys, time
from collections import Counter
from functools import cache
from pathlib import Path

def load(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    mod=importlib.util.module_from_spec(spec);sys.modules[name]=mod;spec.loader.exec_module(mod)
    return mod

def expand(seq,grammar):
    words={}
    for i,(a,b) in enumerate(grammar): words[300+i]=words.get(a,[a])+words.get(b,[b])
    return [x for t in seq for x in words.get(t,[t])]

def repair(word,seed,alpha):
    rng=random.Random(seed);seq=list(word);grammar=[]
    while True:
        counts=Counter(zip(seq,seq[1:]))
        for pair in list(counts):
            if pair[0]==pair[1]:
                k=i=0
                while i+1<len(seq):
                    if (seq[i],seq[i+1])==pair:k+=1;i+=2
                    else:i+=1
                counts[pair]=k
        choices=[(p,n) for p,n in counts.items() if n>=2]
        if not choices: break
        pair=rng.choices([p for p,n in choices],[n**alpha for p,n in choices])[0]
        new=[];i=0
        while i<len(seq):
            if i+1<len(seq) and (seq[i],seq[i+1])==pair:new.append(300+len(grammar));i+=2
            else:new.append(seq[i]);i+=1
        assert len(seq)-len(new)>=2
        grammar.append(pair);seq=new
    return seq,grammar

def dispatch(nodes):
    @cache
    def left_depth(q):
        e=nodes[q][0]
        return 1+(left_depth(int(e.split()[1])) if e.startswith('ENode ') else 0)
    return max(2,max(map(left_depth,nodes)))

def coarsen(word):
    seq=[];i=0
    while i<len(word):
        if word[i:i+2]==[166,119]:seq.append(161);i+=2
        else:seq.append(word[i]);i+=1
    return seq

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repo',type=Path,required=True);p.add_argument('--upstream',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True);p.add_argument('--seeds',type=int,default=2048)
    p.add_argument('--start-seed',type=int,default=0);p.add_argument('--exponents',type=int,nargs='+',default=[1,2,4,8])
    a=p.parse_args();out=a.output.resolve();out.mkdir(parents=True,exist_ok=True)
    rp=a.repo.resolve()/'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels'
    h=load('inherited_rebracket',rp/'code/19-subst-engineering-vendor-one_schema_machine-rebracket_axioms.py')
    r=load('recover_wade_dag',a.repo.resolve()/'Computability/BusyBeaver/Research/ZFC/recover_wade_dag.py')
    nodes,names=r.parse_dag((a.upstream/'ZF/m254/coq/prog/Dag254.v').read_text())
    source=json.loads((rp/'data/19-subst-engineering-artifacts-full_logic_results.json').read_text())
    primitive=source['macro_word'];words={'coarse':coarsen(primitive),'expanded':primitive}
    assert source['recipe']=={'order':[1,2,3,4,5,6,7,8],'perms':[0]*8,'C':2,'G':1,'outer_order':16,'tree':1,'seed':341,'alpha':4}
    assert all(h.bounder(nodes)(f'ENode {x}')==(0,0) for word in words.values() for x in set(word))
    oldseq,oldgr=h.repair(words['coarse'],341,4);oldnodes,oldnames,_=h.transform(nodes,names,oldseq,oldgr)
    assert len(oldnodes)==206 and dispatch(oldnodes)==7
    best=None;hist={};records=[];t0=time.monotonic()
    for lane,word in words.items():
        hist[lane]={}
        for alpha in a.exponents:
            counts=Counter()
            for seed in range(a.start_seed,a.start_seed+a.seeds):
                seq,gr=repair(word,seed,alpha)
                nn,nm,ax=h.transform(nodes,names,seq,gr)
                depth=dispatch(nn);cost=len(nn)+55+depth
                counts[cost]+=1
                key=cost,len(nn),depth,len(gr),len(seq),lane,alpha,seed
                if best is None or key<best['key']:
                    assert expand(seq,gr)==word
                    best=dict(key=key,lane=lane,seed=seed,alpha=alpha,nodes=nn,names=nm,axioms_root=ax,residual=seq,grammar=gr,word=word)
                    rec={'cost':cost,'nodes':len(nn),'dispatcher_depth':depth,'lane':lane,'seed':seed,'alpha':alpha}
                    records.append(rec);print(json.dumps(rec),flush=True)
            hist[lane][alpha]=dict(sorted(counts.items()))
            print(json.dumps({'lane':lane,'alpha':alpha,'best':best['key'][0],'elapsed':time.monotonic()-t0}),flush=True)
    sys.path.insert(0,str(a.upstream.resolve()/'ZF/generator'))
    import TMBuilder as backend
    machine=h.compile_dag(backend,best['nodes'],best['names']);h.reextract(machine,best['nodes'],best['names'])
    working={q for q,b in machine.states};assert len(working)==best['key'][0]
    machine.save(str(out/'candidate.named.tm'))
    norm=load('normalize_named_input',a.repo.resolve()/'Computability/BusyBeaver/Research/ZFC/audit_raw_candidate.py')
    table,labels,meta=norm.normalize_named((out/'candidate.named.tm').read_bytes())
    (out/'candidate.tm').write_bytes(table)
    def write(fn,x):(out/fn).write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
    write('candidate.labels.json',labels)
    write('candidate.dag.json',{'nodes':best['nodes'],'names':best['names'],'root':0,'axioms_root':best['axioms_root']})
    ref=json.loads((rp/'data/19-subst-engineering-artifacts-full_logic_reference.dag.json').read_text())
    rn={int(q):tuple(es) for q,es in ref['nodes'].items()}
    cert,stats=h.bisimulation(rn,best['nodes']);write('rm_certificate.json',cert);write('reference.dag.json',ref)
    write('grammar.json',{k:best[k] for k in ('lane','seed','alpha','residual','grammar','word')})
    result={'control_source':'source19 revised full-original-logic conjunction layout','baseline_states':268,'candidate_states':len(working),'improves_268':len(working)<268,'decision_nodes':len(best['nodes']),'dispatcher_depth':dispatch(best['nodes']),'framework_states':len(working)-len(best['nodes']),'winner':{k:best[k] for k in ('lane','seed','alpha')},'table':meta,'search':{'seeds':a.seeds,'start_seed':a.start_seed,'exponents':a.exponents,'lanes':list(words)},'histograms':hist,'records':records,'rm_certificate_stats':stats,'binary_simulation_or_ZFC_endpoint_proved':False,'elapsed_seconds':time.monotonic()-t0}
    write('results.json',result);print(json.dumps(result),flush=True)
if __name__=='__main__':main()
