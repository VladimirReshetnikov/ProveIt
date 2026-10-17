#!/usr/bin/env python3
"""Search exact-word grammar rotations; charge the complete Wade dispatcher.

An experiment only: it preserves the reviewed full-logic macro word, not a
new TM/ZFC endpoint. Inputs are the pinned ProveIt source-19 control and its
public Wade backend. No source input is modified.
"""
from __future__ import annotations
import argparse, hashlib, importlib, json, math, random, sys, time
from collections import Counter
from functools import lru_cache
from pathlib import Path

BASE = Path(__file__).resolve().parent
sys.path.insert(0, str(BASE/'research-inputs/Computability/BusyBeaver/Research/ZFC'))
import recover_wade_dag as recover
import theory_backend_experiment as theory
import layout_grammar_experiment as layout
import full_grammar_experiment as common

def expand(t):
    return (t,) if isinstance(t,int) else expand(t[0])+expand(t[1])

def from_grammar(g):
    rules={}
    for i,(a,b) in enumerate(g['productions']):
        rules[300+i]=(rules.get(a,a),rules.get(b,b))
    ts=[rules.get(q,q) for q in g['residual']]
    t=ts[-1]
    for q in reversed(ts[:-1]): t=(q,t)
    return t

def to_grammar(t):
    ids={}; prods=[]
    def visit(x):
        if isinstance(x,int): return x
        if x not in ids:
            a,b=visit(x[0]),visit(x[1])
            ids[x]=300+len(prods); prods.append([a,b])
        return ids[x]
    root=visit(t)
    return [root],prods

def subtrees(t):
    seen=set(); out=[]; pending=[t]
    while pending:
        x=pending.pop()
        if isinstance(x,tuple) and x not in seen:
            seen.add(x);out.append(x);pending.extend(x)
    return out

def replace(t,old,new):
    @lru_cache(None)
    def go(x):
        if x==old:return new
        return x if isinstance(x,int) else (go(x[0]),go(x[1]))
    return go(t)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--steps',type=int,default=20000)
    ap.add_argument('--chains',type=int,default=8)
    ap.add_argument('--seed',type=int,default=20261016)
    ap.add_argument('--temperature',type=float,default=0.8)
    ap.add_argument('--restart-period',type=int,default=0)
    args=ap.parse_args(); out=args.output.resolve();out.mkdir(parents=True,exist_ok=True)
    source=recover.git_bytes(None,'ZF/m254/coq/prog/Dag254.v')
    nodes,names=recover.parse_dag(source.decode())
    word,_=layout.selected_word(nodes)
    token_word=layout.tokenizations(nodes,word)['coarse']
    g=json.loads((BASE/'grammar-baseline/grammar.json').read_text())
    start=from_grammar(g)
    assert expand(start)==tuple(token_word)
    helper=common.load_file('source08',common.REPORT/'code/08-schema-machine-rebracket_axioms.py')
    engine=common.load_file('independent_source08',common.REPORT/'code/08-schema-machine-verify_rm_certificate.py')
    backend_path=out/'backend';backend_path.mkdir(exist_ok=True)
    for name in ('TMBuilder.py','tm.py','tmdb.py','LICENSE.wade'):
        (backend_path/name).write_bytes(recover.git_bytes(None,'ZF/generator/'+name))
    sys.path.insert(0,str(backend_path));backend=importlib.import_module('TMBuilder')
    trials=0;hist=Counter();best=999;best_tree=start;best_details={}
    original_leaves=common.framework_leaves(nodes)
    def make(t):
        residual,productions=to_grammar(t)
        return (*layout.transform(nodes,names,token_word,residual,productions),residual,productions)
    def measure(t):
        nn,nm,root,seq,prod=make(t)
        assert common.framework_leaves(nn)==original_leaves
        d=layout.dispatch_depth(nn)
        return len(nn)+55+d,len(nn),d
    assert measure(start)[0]==268
    begin=time.monotonic();accepted=0;rejected=0
    for chain in range(args.chains):
        rng=random.Random(args.seed+chain)
        current=best_tree
        cc=measure(current)[0]
        for step in range(args.steps):
            if args.restart_period and step and step%args.restart_period==0:
                current=best_tree;cc=measure(current)[0]
            candidates=subtrees(current)
            target=rng.choice(candidates)
            options=[]
            if isinstance(target[0],tuple):
                (a,b),c=target;options.append((a,(b,c)))
            if isinstance(target[1],tuple):
                a,(b,c)=target;options.append(((a,b),c))
            if not options:continue
            new=rng.choice(options)
            candidate=replace(current,target,new)
            nc,nd,depth=measure(candidate)
            trials+=1;hist[nc]+=1
            # Repeated cooling permits crossing one/two-node grammar barriers.
            phase=(step%5000)/5000
            temp=max(0.02,args.temperature*(1-phase))
            if nc<=cc or rng.random()<math.exp((cc-nc)/temp):
                current,cc=candidate,nc;accepted+=1
            else:rejected+=1
            if nc<best:
                assert expand(candidate)==tuple(token_word)
                best=nc;best_tree=candidate
                best_details=dict(chain=chain,step=step,states=nc,decision=nd,dispatcher=depth)
                seq,prod=to_grammar(candidate)
                common.write_json(out/'best_grammar.json',dict(token_word=token_word,primitive_word=word,residual=seq,productions=prod))
                print(json.dumps(dict(new_best=best_details,seconds=time.monotonic()-begin)),flush=True)
        print(json.dumps(dict(chain=chain,best=best,current=cc,trials=trials,seconds=time.monotonic()-begin)),flush=True)
    nn,nm,root,seq,prod=make(best_tree)
    assert expand(best_tree)==tuple(token_word)
    machine=helper.compile_dag(backend,nn,nm);helper.reextract(machine,nn,nm)
    actual_states=len({q for q,_ in machine.states});assert actual_states==best
    machine.save(str(out/'candidate.named.tm'))
    table,labels,missing=common.normalize(machine);(out/'candidate.tm').write_bytes(table)
    common.write_json(out/'labels.json',labels)
    refpath=BASE/'grammar-baseline/reference_dag.json'
    reference=json.loads(refpath.read_text())
    rn={int(k):tuple(v) for k,v in reference['nodes'].items()}
    cert,stats=helper.bisimulation(rn,nn)
    candidate_path=out/'candidate_dag.json';certpath=out/'rm_bisimulation.json'
    common.write_json(candidate_path,dict(root=0,nodes=nn,names=nm,axioms_root=root))
    common.write_json(certpath,cert)
    common.write_json(out/'reference_dag.json',reference)
    checked=layout.independent_check(engine,out/'reference_dag.json',candidate_path,certpath)
    result=dict(best=best_details,working_states=actual_states,decision_nodes=len(nn),framework_states=actual_states-len(nn),
                exact_macro_word=True,source_upstream=recover.COMMIT,proveit_pin='426592ce97e52d309bfb8f0132411556650b7ac1',
                trials=trials,accepted=accepted,rejected=rejected,chains=args.chains,steps=args.steps,seed=args.seed,
                temperature=args.temperature,restart_period=args.restart_period,
                histogram=dict(sorted(hist.items())),seconds=time.monotonic()-begin,rm_bisimulation=stats,independent_check=checked,
                total_table_sha256=hashlib.sha256(table).hexdigest(),binary_compiler_or_ZFC_endpoint_proved=False)
    common.write_json(out/'results.json',result);print(json.dumps(result,indent=2),flush=True)

if __name__=='__main__':main()
