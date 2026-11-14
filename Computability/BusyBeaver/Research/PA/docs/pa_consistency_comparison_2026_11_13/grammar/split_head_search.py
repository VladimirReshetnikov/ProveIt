#!/usr/bin/env python3
"""Search sound B+explosion splitting of PA196's first quantifier head.

Discovery scores are not machine-correctness certificates. This imports the
pinned incoming compiler and preserves its source/license attribution.
"""
import sys, json, random, time, itertools
from pathlib import Path
HERE = Path(__file__).resolve().parent
PRIOR = HERE/'support'
sys.path.insert(0,str(PRIOR/'history209'))
sys.path.insert(0,str(PRIOR/'incoming208'))
from variant_search import parts, enc as original_enc, I, U, N, subst
from repair_search import repair, count, nodes, word
from equivalent_search import get_dictionary, parse_with_dictionary, balanced
import compile_ax as ca

MODE=sys.argv[2] if len(sys.argv)>2 else 'split'
OUT=Path(sys.argv[3]).resolve() if len(sys.argv)>3 else HERE/'runs'/({'padding':'head_padding','split_positive':'split_positive'}.get(MODE,'split_head')); OUT.mkdir(parents=True,exist_ok=True)
def enc(t):
    if t=='0':return 'P'
    if isinstance(t,str):return 'Pi' if t=='1' else t
    op,a,b=t
    if op=='U':return enc(b)+enc(a)+'Cii'
    return enc(a)+enc(b)+'C'+'i'*{'I':0,'M':1,'E':3}[op]
prefix, heads, gate=parts()
newB=I(N('H'),U('D',N(U('D','H'))))
if MODE=='split_positive':newB=I('H',U('D',N(U('D',N('H')))))
rng=random.Random(2026111342)
dictionary=get_dictionary()
best_nodes=1000; best_physical=1000; tested=0; priced=0
hist={}; checked_words=set(); start=time.monotonic(); metric_rejections=0
budget=int(sys.argv[1]) if len(sys.argv)>1 else 50000
baseline_tree=ca.macro_info()[2]
baseline_states=ca.price(baseline_tree)[0]
if baseline_states!=196:raise RuntimeError(('baseline compilation mismatch',baseline_states))

def inspect(t, info):
    global best_nodes,best_physical,priced,metric_rejections
    n=count(t); hist[n]=hist.get(n,0)+1
    if n<best_nodes:
        best_nodes=n; print('best nodes',n,'trial',tested,'seconds',round(time.monotonic()-start,1),flush=True)
    if n>72:return
    metrics=ca.source_metrics(t)
    if metrics['max_consecutive_zeros']>6 or metrics['max_path_bits']>46:
        metric_rejections+=1
        return
    cost,selection=ca.price(t); priced+=1
    if cost<best_physical:
        best_physical=cost
        print('best physical',cost,'nodes',n,'folds',len(selection),'trial',tested,flush=True)
        T,internal,root=ca.compile_tree(t)
        folded,proj=ca.make_fold(T,selection)
        data=dict(info,tree=t,raw_nodes=n,working_states=cost,folds=selection,metrics=metrics,
                  root=proj[root],table=[[q,b,*act] for(q,b),act in sorted(folded.items())])
        (OUT/f'best_{cost}.json').write_text(json.dumps(data,indent=2))

for tested in range(budget):
    expvar='DHA'[tested%3]
    hs=[newB]+heads[1:]+[I('1',expvar)]
    if MODE=='padding':
        h='H'; pads=[h,I('0',h),I(I(h,h),h),I(I(h,'0'),h),I(I('A','A'),h),I(I('D','D'),h),I('0',I('0',h))]
        p1=rng.choice(pads);p2=rng.choice(pads)
        hs=[I(N(U('D',N(U('D',p1)))),p2)]+heads[1:]
    if tested%5==0:
        # All independent renamings preserve the axiom schema being supplied.
        p=rng.choice(list(itertools.permutations('DHA')))
        hs[0]=subst(hs[0],dict(zip('DHA',p)))
    if MODE=='padding':
        order=list(range(6))
        if tested%3:rng.shuffle(order)
    elif tested<42:
        order=list(range(6)); order.insert((tested//3)%7,6)
    else:
        order=list(range(7)); rng.shuffle(order)
    w=prefix+''.join(enc(hs[j]) for j in order)+enc(gate)+'LGX'
    info={'explosion_variable':expvar,'head_order':order,'word':w,'tokens':len(w),
          'B_formula':hs[0]}
    if w not in checked_words:
        checked_words.add(w)
        score,pieces=parse_with_dictionary(w,dictionary)
        if score<=73:inspect(balanced(pieces),info)
    t=repair(w,rng,0 if tested%3 else rng.randrange(1,6))
    inspect(t,info)
    if tested%2000==0:
        print('progress',tested,'best',best_physical,'seconds',round(time.monotonic()-start,1),flush=True)
    if best_physical<196:break

receipt={'seed':2026111342,'trials':tested+1,'distinct_words':len(checked_words),
         'priced_layouts':priced,'best_raw_nodes':best_nodes,
         'best_physical':best_physical if priced else None,
         'baseline_states':baseline_states,'metric_rejections':metric_rejections,
         'histogram':hist,'elapsed_seconds':time.monotonic()-start,
         'status':'construction search only; source and literal contracts not verified'}
(OUT/'receipt.json').write_text(json.dumps(receipt,indent=2))
print(json.dumps(receipt),flush=True)
