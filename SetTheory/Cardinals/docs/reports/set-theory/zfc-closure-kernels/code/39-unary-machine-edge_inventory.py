#!/usr/bin/env python3
"""New diagnostic family: nonuniform incoming-edge deletion of all eligible states.
Uses pinned prior source04 affine checker; supplies no kernel proof.
"""
from pathlib import Path
from collections import defaultdict,Counter
import importlib.util,sys,json,time,hashlib
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'support'))
from context_search import executor,program_sites,cases,check
spec=importlib.util.spec_from_file_location('gen',HERE/'upstream253/ZF/m253/tools/generate_candidate.py')
gen=importlib.util.module_from_spec(spec);spec.loader.exec_module(gen)
tabn=gen.patched_rows(HERE/'upstream/ZF/m254/machine/zfc_254.tm')
table={(str(q),b):(w,d,str(t))for(q,b),(w,d,t)in tabn.items()}
ns=executor(table,HERE/'support/sources/symexec.py')
allcases=cases(ns,program_sites(HERE/'support/sources/Prog254.v'))
# All register-box sources and successors protected; final output rechecks all.
CORE={0,1,2,3,4,6,28,31,38,40,43,44,48,56,59,60,63,64,69,73,75,83,85,95,97,109,112,131}
protect=CORE|{96}|{t for(q,b),(w,d,t)in tabn.items()if q in CORE}
edge_bits=defaultdict(set); affected=defaultdict(set); cur=[0]
def first(segs,exterior=0):
    out=set()
    for s in segs:
        if s[0]=='b':return out|{s[1]}
        if s[0]=='box':return out|{0}
        _,b,a,c=s
        if c>0:return out|{b}
        if a>0:out.add(b)
    return out|{exterior}
def tail(segs):
    if not segs:return {0}
    s=segs[0]
    if s[0]=='b':return first(segs[1:])
    if s[0]=='box':return {0,1}
    _,b,a,c=s
    if c>=2:return {b}
    out={b}if a>0 else set()
    return out|first(segs[1:])
def observe(q,form,L,R,br,exp):
    if q=='254':return
    if form=='l':return
    if not R:return
    s=R[0]
    if s[0]=='box':return
    bits=first(R)
    for bit in bits:
        w,d,p=table[q,bit]
        # Exact finite-symbol overapproximation of the next read.
        nxt=tail(R)if d=='R' else first(L)
        edge_bits[(q,bit)].update(nxt)
        affected[p].add(cur[0])
ns['OBSERVE']=observe
t0=time.monotonic()
for i,c in enumerate(allcases):
    cur[0]=i
    assert check(ns,c),i
ns['OBSERVE']=None
# Include exact full boot reads at the incoming target.
tape=set();head=0;q=5
for i in range(312975):
    b=int(head in tape);w,d,p=tabn[q,b]
    if w:tape.add(head)
    else:tape.discard(head)
    head+=1 if d=='R' else -1
    edge_bits[str(q),b].add(int(head in tape));q=p
assert(q,head,len(tape))==(96,-17,178)
incoming=defaultdict(list)
for e,(w,d,p)in table.items():incoming[p].append(e)
opts={};summ=[]
for pn in sorted({q for q,b in tabn}-protect):
    p=str(pn);ins=incoming[p];edges=[];possible=True
    for e in ins:
        bs=edge_bits[e]
        same=[q for q in sorted({q for q,b in table},key=int) if q!=p and all(table[q,b]==table[p,b]for b in bs)]if bs else []
        edges.append({'edge':e,'bits':sorted(bs),'same_rows':same})
        if not same:possible=False
    summ.append({'removed':pn,'incoming':edges,'possible':possible})
    if possible:opts[p]=edges
print('runtime baseline',len(allcases),'elapsed',round(time.monotonic()-t0,3),'eligible',len(summ),'possible',len(opts))
print('possible',opts)
(HERE/'incoming_edge_inventory.json').write_text(json.dumps({'cases':len(allcases),'protect':sorted(protect),'eligible':summ,'possible':opts},indent=2)+'\n')
