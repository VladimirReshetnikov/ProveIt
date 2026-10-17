"""Measure full logical-row permutations; retain every original formula row."""
from pathlib import Path
from functools import cache
from collections import Counter
import argparse, json, random, sys, time
BASE=Path(__file__).resolve().parents[1]
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output',type=Path,default=BASE/'experiments/permutations')
args=parser.parse_args()
sys.path.insert(0,str(BASE/'sources/proveit/Computability/BusyBeaver/Research/ZFC'))
import recover_wade_dag as recover, theory_backend_experiment as theory
import full_grammar_experiment as common, layout_grammar_experiment as layout
nodes,names=recover.parse_dag(recover.git_bytes(None,'ZF/m254/coq/prog/Dag254.v').decode())
word,contract=layout.selected_word(nodes)
spec,_=theory.published_spec();rows=spec['ax_rows']('a','h','b','c','u')
prefix=[166,121,180,176];tail=word[88:]
assert prefix+sum([theory.emit(row) for row in rows[1:]],[])+tail==word
best=268;hist=Counter();start=time.monotonic();rng=random.Random(20261016)
out=args.output;out.mkdir(parents=True,exist_ok=True)
perms=[tuple(range(1,9))]
for i in range(6000):
    p=list(range(1,9));rng.shuffle(p);perms.append(tuple(p))
for trial,order in enumerate(perms):
    w=prefix+sum([theory.emit(rows[k]) for k in order],[])+tail
    stack,events=theory.symbolic(w)
    assert stack==['old_top',rows[0]]+[rows[k] for k in order]+[theory.symbolic(word)[0][-1]]
    coarse=[];i=0
    while i<len(w):
        if w[i:i+2]==[166,119]:coarse.append(161);i+=2
        else:coarse.append(w[i]);i+=1
    for seed in (130,341):
        seq,rules,_=common.safe_repair(coarse,seed,4)
        nn,nm,root=layout.transform(nodes,names,coarse,seq,rules)
        d=layout.dispatch_depth(nn);cost=len(nn)+55+d;hist[cost]+=1
        if cost<best:
            best=cost
            info={'permutation':order,'seed':seed,'cost':cost,'depth':d,'decision_nodes':len(nn),'primitive_word':w,
                  'token_word':coarse,'residual':seq,'productions':rules,'nodes':nn,'names':nm,'root':root,'events':events,'trial':trial}
            (out/'best.json').write_text(json.dumps(info,indent=2)+'\n')
            print(json.dumps({'best':best,'order':order,'trial':trial,'seconds':time.monotonic()-start}),flush=True)
    if trial%1000==0:print(json.dumps({'trial':trial,'best':best}),flush=True)
(out/'census.json').write_text(json.dumps({
    'trials':len(perms), 'grammars':sum(hist.values()),
    'histogram':dict(hist), 'seconds':time.monotonic()-start,
    'observed_minimum':min(hist), 'incumbent':best,
    'incumbent_source':'pinned 268-state complete-word control, outside new trial family'
},indent=2)+'\n')
