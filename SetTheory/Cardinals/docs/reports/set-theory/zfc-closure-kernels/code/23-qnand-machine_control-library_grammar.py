"""Closed-helper library-aware grammar comparison, with offline fixed replay.

This changes only a straight-line expansion of the original full AX word.
The pinned original logic, theory, register instructions and Wade framework
are retained. A finite RM certificate is still not a binary compiler theorem.
"""
from __future__ import annotations
from collections import Counter
from functools import cache
from pathlib import Path
import argparse, hashlib, json, random, sys

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'vendor'))
import rebracket_axioms as g
import recover_wade_dag as r
r.SNAPSHOT=HERE/'upstream'
import theory_backend_experiment as t
sys.path.insert(0,str(r.SNAPSHOT/'ZF/generator'))
import TMBuilder as backend

def edge(v): return v if isinstance(v,str) else f'ENode {v}'
def atom(e): return int(e[6:]) if e.startswith('ENode ') else e

def expand_word(nodes,word,chosen):
    bc=g.bounder(nodes)
    @cache
    def exp(v):
        if v not in chosen:return (v,)
        assert all(bc(e)==(0,0) for e in nodes[v]),v
        return tuple(z for e in nodes[v] for z in exp(atom(e)))
    return [z for q in word for z in exp(q)]

def repair_library(nodes,word,seed,alpha):
    rng=random.Random(seed)
    # Every source node outside AX is independently live in the original core
    # plus the original AX helper set, so its node cost has already been paid.
    dictionary={tuple(atom(e) for e in es):q for q,es in nodes.items()
                if not 1<=q<=114}
    seq=list(word); grammar=[]
    while True:
        raw=Counter(zip(seq,seq[1:])); choices=[]
        for pair,frequency in raw.items():
            if pair[0]==pair[1]:
                frequency=0;i=0
                while i+1<len(seq):
                    if tuple(seq[i:i+2])==pair:frequency+=1;i+=2
                    else:i+=1
            gain=frequency-(pair not in dictionary)
            if gain>0:choices.append((pair,gain))
        if not choices:break
        pair=rng.choices([p for p,f in choices],[f**alpha for p,f in choices])[0]
        if pair in dictionary:symbol=dictionary[pair]
        else:
            symbol=300+len(grammar);grammar.append(pair);dictionary[pair]=symbol
        new=[];i=0
        while i<len(seq):
            if i+1<len(seq) and tuple(seq[i:i+2])==pair:new.append(symbol);i+=2
            else:new.append(seq[i]);i+=1
        seq=new
    return seq,grammar

def transform(nodes,names,seq,grammar):
    out={q:es for q,es in nodes.items() if not 1<=q<=114}
    outnames={q:s for q,s in names.items() if q in out}
    interner={es:q for q,es in out.items()};next_id=max(nodes)+1;remap={}
    def resolve(v):return edge(remap.get(v,v))
    def pair(a,b):
        nonlocal next_id
        es=(a,b)
        if es not in interner:
            interner[es]=next_id;out[next_id]=es
            outnames[next_id]=f'library_grammar_{next_id}';next_id+=1
        return interner[es]
    for j,(a,b) in enumerate(grammar):remap[300+j]=pair(resolve(a),resolve(b))
    root=remap.get(seq[-1],seq[-1])
    for v in reversed(seq[:-1]):root=pair(resolve(v),edge(root))
    for q,es in tuple(out.items()):out[q]=tuple(edge(root) if e=='ENode 1' else e for e in es)
    seen=set();pending=[0]
    while pending:
        q=pending.pop()
        if q in seen:continue
        seen.add(q);pending.extend(int(e[6:]) for e in out[q] if e.startswith('ENode '))
    ordered=[0]+sorted(seen-{0});ids={q:i for i,q in enumerate(ordered)}
    nn={ids[q]:tuple(edge(ids[int(e[6:])]) if e.startswith('ENode ') else e for e in out[q]) for q in ordered}
    nam={ids[q]:outnames[q] for q in ordered}
    return nn,nam,ids[root]

def main():
    if not __debug__:raise RuntimeError('Run without -O; explicit checks use assertions.')
    ap=argparse.ArgumentParser();ap.add_argument('--seeds',type=int,default=80)
    ap.add_argument('--output',type=Path,default=HERE/'reproduced')
    ap.add_argument('--search',action='store_true',help='Run the bounded search instead of the fixed winning recipe.')
    ap.add_argument('--families',default='all',help='Comma-separated expansion families, or all.')
    args=ap.parse_args();args.output.mkdir(parents=True,exist_ok=True)
    nodes,names=r.parse_dag(r.git_bytes(None,'ZF/m254/coq/prog/Dag254.v').decode())
    word,_,contract=t.old_contract(nodes);bc=g.bounder(nodes)
    expandible={q for q,es in nodes.items() if q>114 and all(bc(e)==(0,0) for e in es)}
    families={
        'none':set(),
        'negation':{178,179,183,184,218},
        'quantifier':{180,181,182},
        'variables':{121,166,168},
        'copy_variables':{121,122,166,167,168,169},
        'constructors':{178,179,180,181,182,183,184,218},
        'outer':{121,166,168,178,179,180,181,182,183,184,218},
        'all':expandible,
    }
    if args.families!='all':
        chosen_names=args.families.split(',')
        families={k:v for k,v in families.items() if k in chosen_names}
    if not args.search:families={'quantifier':{180,181,182}}
    counts={};best=None
    for fn,chosen in families.items():
        ex=expand_word(nodes,word,chosen);cnt=Counter()
        for alpha in ((2,4,8) if args.search else (4,)):
            for seed in (range(args.seeds) if args.search else (0,)):
                residual,grammar=repair_library(nodes,ex,seed,alpha)
                nn,nam,root=transform(nodes,names,residual,grammar)
                cost=len(nn);cnt[cost]+=1
                if best is None or cost<best[0]:
                    best=cost,nn,nam,root,residual,grammar,fn,alpha,seed,ex
                    print(json.dumps({'new_best_nodes':cost,'family':fn,'alpha':alpha,'seed':seed,'expanded_word':len(ex)}),flush=True)
        counts[fn]=dict(sorted(cnt.items()))
    cost,nn,nam,root,residual,grammar,fn,alpha,seed,ex=best
    cert,stats=g.bisimulation(nodes,nn)
    machine=g.compile_dag(backend,nn,nam);g.reextract(machine,nn,nam)
    machine.save(str(args.output/'candidate_named.tm'))
    states={q for q,_ in machine.states}
    missing=[(q,b) for q in sorted(states) for b in ('0','1') if (q,b) not in machine.states]
    assert missing==[('1.inc','1')]
    ordered=[machine.start]+sorted(states-{machine.start});number={q:i for i,q in enumerate(ordered)}
    number['halt']=len(ordered);lines=['#! start 0']
    for q in ordered:
        for bit in ('0','1'):
            action=machine.states.get((q,bit))
            w,d,target=(bit,'R','halt') if action is None else (action.write,action.direction,action.nextstate)
            lines.append(f'{number[q]} {bit} {w} {d} {number[target]}')
    (args.output/'candidate_total.tm').write_text('\n'.join(lines)+'\n')
    results={'upstream_commit':r.COMMIT,'provenance':'Original AX word expanded only through universally closed existing helper pairs.',
             'working_states':len(states),'decision_nodes':cost,'framework_states':sum(q[0].isdigit() for q in states),
             'winner':{'family':fn,'alpha':alpha,'seed':seed,'expanded_word_length':len(ex)},
             'fixed_recipe_replay':not args.search,'sampled_choices':sum(sum(d.values()) for d in counts.values()),
             'partial_rows':len(machine.states),'total_rows':len(lines)-1,'missing_rows':missing,
             'named_table_sha256':hashlib.sha256((args.output/'candidate_named.tm').read_bytes()).hexdigest(),
             'total_table_sha256':hashlib.sha256((args.output/'candidate_total.tm').read_bytes()).hexdigest(),
             'distributions':counts,'original_symbolic_contract':contract,'rm_bisimulation':stats,
             'compiler_proof':False,'new_ZFC_state_bound':False}
    for name,data in [('results.json',results),('candidate_dag.json',{'root':0,'axioms_root':root,'nodes':nn,'names':nam}),
                      ('rm_bisimulation.json',cert),('grammar.json',{'original_word':word,'expanded_word':ex,'residual':residual,'productions':grammar})]:
        (args.output/name).write_text(json.dumps(data,indent=2,sort_keys=True)+'\n')
    print(json.dumps({k:v for k,v in results.items() if k not in ('distributions','original_symbolic_contract')},indent=2))

if __name__=='__main__':main()
