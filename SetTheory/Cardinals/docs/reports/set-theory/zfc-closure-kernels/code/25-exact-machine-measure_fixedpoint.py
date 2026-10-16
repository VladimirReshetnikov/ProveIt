#!/usr/bin/env python3
"""Measure EFPC normal forms through the complete-equality, base-four frontend.

Reads pinned ProveIt code, changes only the theory formula and bracketing of
closed AX emission words, and emits complete literal tables for the winners.
No theorem-to-code calibration or new ZFC state bound is claimed.
"""
from __future__ import annotations
import argparse
from collections import Counter
import hashlib
import importlib
import importlib.util
import itertools
import json
from pathlib import Path
import sys
import time


def load(name,path,digest=None):
    if digest and hashlib.sha256(path.read_bytes()).hexdigest()!=digest:
        raise ValueError(f'Unexpected source: {path}')
    spec=importlib.util.spec_from_file_location(name,path)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    return module


def jwrite(path,obj):
    path.write_text(json.dumps(obj,sort_keys=True,indent=2)+'\n')


def formula(t,mode):
    I,A,E,N,O,R=t.Imp,t.All,t.Ex,t.And,t.Or,t.Rel
    c='c'
    bound=A(0,E(c,A(1,I(c,A(0,I(R(0,1),R(0,c)))))))
    empty=A(c,t.Not(R(c,0)))
    if mode.startswith('EPSC'):
        closure=A(0,I(O(empty,R(0,c)),A(1,I(c,R(1,c)))))
        support=A(1,I(R(1,c),E(0,c)))
        return I(bound,E(c,N(support,closure) if mode=='EPSC_s' else N(closure,support)))
    a,b,d=map(int,mode.split('_')[1])
    active=O(R(0,c),empty) if a else O(empty,R(0,c))
    predecessor=E(0,N(c,active) if b else N(active,c))
    membership=R(1,c)
    condition=t.Iff(predecessor,membership) if d else t.Iff(membership,predecessor)
    return I(bound,E(c,A(1,condition)))


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo',type=Path,required=True)
    ap.add_argument('--out',type=Path,required=True)
    ap.add_argument('--seeds',type=int,default=128)
    ap.add_argument('--modes',nargs='+')
    args=ap.parse_args()
    if not __debug__:raise RuntimeError('Run with assertions enabled')
    repo=args.repo.resolve();out=args.out.resolve();out.mkdir(parents=True,exist_ok=True)
    code=repo/'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code'
    sys.path.insert(0,str(repo/'Computability/BusyBeaver/Research/ZFC'))
    import theory_backend_experiment as t
    import recover_wade_dag as recover
    g=load('grammar',code/'14-empty-third_party-one_schema-machine-rebracket_axioms.py',
           'bdbf5a84ab1a2914e351e917d7ff3994fec5729bddbe33971678cd51c2839119')
    eps=load('epsc',code/'14-empty-code-full_equality_epsc.py')
    macro=load('macro',code/'14-empty-code-macro_contract.py')
    nodes,names=recover.parse_dag(recover.git_bytes(None,'ZF/m254/coq/prog/Dag254.v').decode())
    effects=macro.possible_returns(nodes)
    assert all(effects[q]=={macro.NORMAL} for q in macro.MACROS)
    backend_path=repo/'lib/jeff-busy-beaver-zfc254/ZF/generator'
    sys.path.insert(0,str(backend_path));backend=importlib.import_module('TMBuilder')
    spec,_=t.published_spec();original=spec['ax_rows']('a','h','b','c','u')
    V=t.Imp(t.Rel('a','b'),t.All('c',t.Rel('a','b')))
    Q=t.Imp(t.Eq('a','b'),t.All('c',t.Eq('a','b')))
    modes=args.modes or ['EPSC_s','EPSC_c']+['EFPC_'+''.join(map(str,k)) for k in itertools.product((0,1),repeat=3)]
    results=[];begin=time.monotonic()
    for mode in modes:
        E=formula(t,mode);best=None;hist=Counter();actual_hist=Counter();framework_hist=Counter();count=0
        for oi,order in enumerate(eps.ORDERS):
            for association in (0,1):
                bundle=t.And(t.And(E,Q),V) if association==0 else t.And(E,t.And(Q,V))
                word=[166,121,180,176]
                for i in order:word+=t.emit(original[i])
                word+=t.emit(bundle)+t.TAIL
                assert t.symbolic(word)[0]==['old_top',original[0]]+[original[i] for i in order]+[bundle]
                for alpha in (4,8):
                    for seed in range(args.seeds):
                        seq,grammar=g.repair(word,seed,alpha)
                        nn,nam,root=g.transform(nodes,names,seq,grammar)
                        machine=g.compile_dag(backend,nn,nam)
                        states={q for q,_ in machine.states}
                        cost=len(states);hist[len(nn)]+=1;actual_hist[cost]+=1;count+=1
                        framework_hist[sum(q[0].isdigit() for q in states)]+=1
                        key=(cost,len(nn),len(grammar),len(seq),oi,association,alpha,seed)
                        if best is None or key<best[0]:
                            best=key,nn,nam,root,word,seq,grammar
        key,nn,nam,root,word,seq,grammar=best
        machine=g.compile_dag(backend,nn,nam);g.reextract(machine,nn,nam)
        naive,naivenames,naiveroot=g.transform(nodes,names,word,[])
        cert,stats=g.bisimulation(naive,nn)
        dest=out/mode;dest.mkdir(exist_ok=True)
        machine.save(str(dest/'winner_named.tm'))
        states={q for q,_ in machine.states}; ordered=[machine.start]+sorted(states-{machine.start})
        missing=[(q,b) for q in states for b in ('0','1') if (q,b) not in machine.states]
        assert missing==[('1.inc','1')]
        labels={q:i for i,q in enumerate(ordered)};labels['halt']=len(ordered)
        lines=['#! start 0']
        for q in ordered:
            for b in ('0','1'):
                row=machine.states.get((q,b))
                w,d,n=(b,'R',labels['halt']) if row is None else (row.write,row.direction,labels[row.nextstate])
                lines.append(f'{labels[q]} {b} {w} {d} {n}')
        table=('\n'.join(lines)+'\n').encode();(dest/'winner_total.tm').write_bytes(table)
        jwrite(dest/'source_dag.json',{'root':0,'axioms_root':naiveroot,'nodes':naive,'names':naivenames})
        jwrite(dest/'candidate_dag.json',{'root':0,'axioms_root':root,'nodes':nn,'names':nam})
        jwrite(dest/'rm_bisimulation.json',cert)
        jwrite(dest/'grammar.json',{'word':word,'seq':seq,'grammar':grammar})
        jwrite(dest/'state_names.json',{'states':ordered,'halt':len(ordered)})
        row={'mode':mode,'formula_macro_length':len(t.emit(E)),'word_macro_length':len(word),
             'selected_family_cases':count,'histogram_of_decision_nodes':dict(hist),
             'decision_nodes':len(nn),'working_states':len(states),'framework_states':sum(q[0].isdigit() for q in states),
             'total_rows':len(lines)-1,'literal_sha256':hashlib.sha256(table).hexdigest(),
             'histogram_of_actual_working_states':dict(actual_hist),'histogram_of_framework_states':dict(framework_hist),
             'recipe':{'logical_order':eps.ORDERS[key[4]],'association':key[5],'alpha':key[6],'seed':key[7]},
             'grammar_productions':len(grammar),'residual_length':len(seq),
             'source_decision_nodes':len(naive),'rm_bisimulation':stats}
        results.append(row);jwrite(dest/'results.json',row)
        print(json.dumps({k:v for k,v in row.items() if k not in ('histogram_of_decision_nodes','rm_bisimulation')}) ,flush=True)
        jwrite(out/'results.json',{'results':results,'elapsed_seconds':time.monotonic()-begin,
            'status':'Complete-equality/base-four frontend measurement; no new verified Con(ZFC) machine.',
            'proof_scope':'Finite operation bisimulation compares each compressed program with its own naive identical formula word, not the published SIR theory.',
            'protected_frontend':'GEN, all eight logical rows, both atomic vacuities, original cleanup/freshness tail, and all equality code retained.',
            'search_objective':'Actual generated working-state count; every selected candidate is compiled, no fixed-overhead inference.',
            'source_commit':'de047657e193ec605e930eaf149a44a38031820b','seeds':args.seeds,
            'generator_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()})

if __name__=='__main__':main()
