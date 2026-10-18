#!/usr/bin/env python3
"""Whole Wade-backend costs for two proof-search protocol simplifications.

AX omits saving the old theorem before loading a, so its GEN binder becomes
a+old_T. MP may omit a redundant pushed zero. The theory rows remain exact.
Semantic calibration is a separate proof obligation; compiler counts are real.
"""
from __future__ import annotations
import argparse
from collections import Counter
import copy
import hashlib
import importlib
import json
from pathlib import Path
import sys
import time

HERE=Path(__file__).resolve().parent
BASE=HERE.parent/'source/Computability/BusyBeaver/Research/ZFC'
sys.path.insert(0,str(BASE))
import recover_wade_dag as recover
import theory_backend_experiment as theory
from full_grammar_experiment import load_file,safe_repair,expand,normalize,dispatch_depth,framework_leaves


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--seeds',type=int,default=1000)
    args=ap.parse_args()
    out=args.output.resolve();out.mkdir(parents=True,exist_ok=True)
    helper=load_file('destructive_helper',HERE/'08-schema-machine-rebracket_axioms.py')
    nodes,names=recover.parse_dag(recover.git_bytes(None,'ZF/m254/coq/prog/Dag254.v').decode())
    full,_,contract=theory.old_contract(nodes)
    coarse=list(helper.axiom_word(nodes))
    assert full[0]==coarse[0]==166
    assert nodes[166]==('ENode 171','ENode 167')
    assert nodes[130]==('ENode 123','ENode 166')
    for name in ('TMBuilder.py','tm.py','tmdb.py','LICENSE.wade'):
        (out/name).write_bytes(recover.git_bytes(None,'ZF/generator/'+name))
    sys.path.insert(0,str(out));backend=importlib.import_module('TMBuilder')
    original_leaves=framework_leaves(nodes)
    results=dict(scope=__doc__,source_commit=recover.COMMIT,original_contract=contract,
                 seeds=args.seeds,exponents=[1,2,4,8],lanes={})
    begun=time.monotonic()
    for ax_drop,mp_drop in ((False,False),(True,False),(False,True),(True,True)):
        tag=('ax_omit_push' if ax_drop else 'original_ax')+'_'+('mp_omit_zero' if mp_drop else 'original_mp')
        nn0=copy.deepcopy(nodes)
        if mp_drop:nn0[130]=('ENode 123','ENode 167')
        word=coarse[:]
        if ax_drop:word[0]=167
        assert helper.bounder(nn0)('ENode 167')==(0,0)
        best=None;hist=Counter();trials=0
        # Exact original control plus both grammar samplers; costs charge the
        # real dispatch depth. Compile each winner and independently reextract.
        for exponent in (1,2,4,8):
            for seed in range(args.seeds):
                for algo in ('safe','legacy'):
                    if algo=='safe':seq,rules,_=safe_repair(word,seed,exponent)
                    else:seq,rules=helper.repair(word,seed,exponent)
                    assert expand(seq,rules)==word
                    nn,nm,root=helper.transform(nn0,names,seq,rules)
                    assert framework_leaves(nn)==original_leaves
                    cost=len(nn)+55+dispatch_depth(nn)
                    hist[cost]+=1;trials+=1
                    key=(cost,len(nn),len(rules),len(seq),algo,exponent,seed)
                    if best is None or key<best['key']:
                        best=dict(key=key,nodes=nn,names=nm,root=root,seq=seq,rules=rules)
        machine=helper.compile_dag(backend,best['nodes'],best['names'])
        helper.reextract(machine,best['nodes'],best['names'])
        states={q for q,_ in machine.states}
        assert len(states)==best['key'][0]
        table,labels,missing=normalize(machine)
        lane=out/tag;lane.mkdir(exist_ok=True)
        (lane/'candidate.tm').write_bytes(table)
        machine.save(str(lane/'candidate.named.tm'))
        (lane/'dag.json').write_text(json.dumps(dict(nodes=best['nodes'],names=best['names'],root=0),indent=2)+'\n')
        (lane/'grammar.json').write_text(json.dumps(dict(word=word,residual=best['seq'],productions=best['rules']),indent=2)+'\n')
        result=dict(working_states=len(states),decision_nodes=len(best['nodes']),
                    framework_states=len(states)-len(best['nodes']),winner=best['key'],
                    histogram=dict(sorted(hist.items())),trials=trials,
                    table_sha256=hashlib.sha256(table).hexdigest(),
                    every_decoder_edge_reextracted=True,missing_rows=missing,
                    elapsed_seconds=time.monotonic()-begun)
        results['lanes'][tag]=result
        (out/'results.json').write_text(json.dumps(results,indent=2)+'\n')
        print(tag,result['working_states'],best['key'],flush=True)
    print('SECONDS',time.monotonic()-begun,flush=True)


if __name__=='__main__':main()
