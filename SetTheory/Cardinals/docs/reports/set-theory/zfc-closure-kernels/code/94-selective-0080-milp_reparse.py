"""Finite-substrate exact grammar minimization using scipy.optimize.milp.

This search fixes route words and bootstrap productions. Its universe contains
the incumbent words and a bounded closure of rotation-generated subwords.
Only solver-proved results establish bounds within that finite substrate;
all candidates still require the independent scanner/semantic verification.
"""
from pathlib import Path
from collections import defaultdict
import argparse,json,time,sys
import numpy as np
from scipy.optimize import milp,Bounds,LinearConstraint
from scipy.sparse import coo_array
from grammar_model import load
from prepare_fine_search import norm,expansions

HERE=Path(__file__).resolve().parent

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--rounds',type=int,default=2);ap.add_argument('--seconds',type=int,default=180);ap.add_argument('--new-limit',type=int);ap.add_argument('--bound',type=int,default=128);ap.add_argument('--output',type=Path,default=HERE/'milp-result.json');args=ap.parse_args()
    data,initial,old,roots,allowed,groups,exprs,orig,atoms,locks=load()
    g={norm(w):(norm(a),norm(b)) for w,(a,b) in initial.items()}
    routes=[norm(r['word'])for r in data['routes']]
    locked={norm(w):tuple(norm(t)for t in ts)for w,ts in locks.items()}
    forced=set(map(norm,roots))|set(routes)
    # Freeze the at-most-two consumed route projections at their incumbent
    # spelling. Optional universe expansion does not weaken any interface.
    for (_,_,_,cs),r in zip(groups,routes):
        for p,t in cs:
            w=r
            for b in p:
                locked[w]=g[w];w=g[w][int(b)]
    terminals={expansions[c]for c in allowed}
    masks={expansions[c]:mask for c,mask in allowed.items()}
    def permitted(a,b):return (a not in terminals or masks[a]&1) and (b not in terminals or masks[b]&2)
    universe=set(g)|terminals
    def splits(w,u):
        return [(w[:k],w[k:])for k in range(1,len(w))if w[:k]in u and w[k:]in u and permitted(w[:k],w[k:])]
    steps=[]
    for roundn in range(args.rounds):
        options={w:splits(w,universe)for w in universe-terminals}
        extra=set()
        for w,ss in options.items():
            if w in locked:continue
            for a,b in ss:
                if a not in terminals:
                    for aa,ab in options[a]:
                        if permitted(ab,b):extra.add(ab+b)
                if b not in terminals:
                    for ba,bb in options[b]:
                        if permitted(a,ba):extra.add(a+ba)
        universe|=extra
        steps.append(len(universe))
    words=sorted(universe-terminals,key=lambda w:(len(w),w));ix={w:i for i,w in enumerate(words)}
    opts={w:([locked[w]]if w in locked else splits(w,universe))for w in words}
    # Subword lengths strictly decrease. Hence these activation constraints
    # enforce a genuine acyclic binary grammar without a separate rank axiom.
    ys=[]
    for w in words:
        for a,b in opts[w]:ys.append((w,a,b))
    start=len(words);nv=start+len(ys)
    c=np.zeros(nv);c[:start]=1
    lower=np.zeros(nv);upper=np.ones(nv)
    for w in forced:lower[ix[w]]=1
    ri=[];ci=[];vv=[];lo=[];hi=[]
    def row(items,l=-np.inf,h=np.inf):
        i=len(lo);lo.append(l);hi.append(h)
        for j,x in items:ri.append(i);ci.append(j);vv.append(x)
    byword=defaultdict(list)
    for j,(w,a,b) in enumerate(ys,start):
        byword[w].append(j)
        for child in set((a,b))-terminals:row([(j,1),(ix[child],-1)],h=0)
    for w in words:row([(ix[w],-1)]+[(j,1)for j in byword[w]],l=0,h=0)
    # Do not spend time exploring solutions worse than the supplied witness.
    count_row=len(lo)
    row([(i,1)for i in range(start)],h=args.bound)
    if args.new_limit is not None:row([(ix[w],1)for w in words if w not in g],h=args.new_limit)
    matrix=coo_array((np.array(vv), (np.array(ri,dtype=np.int32),np.array(ci,dtype=np.int32))),shape=(len(lo),nv)).tocsc()
    # Positive control: the supplied 128-rule incumbent exactly satisfies
    # every structural/model constraint. If a smaller bound is requested, its
    # sole violation is the intentionally strengthened count constraint.
    witness=np.zeros(nv)
    for w in g:witness[ix[w]]=1
    for j,(w,a,b)in enumerate(ys,start):
        if w in g and g[w]==(a,b):witness[j]=1
    assert np.all(witness>=lower) and np.all(witness<=upper)
    values=matrix@witness
    violations=[i for i,(v,l,h)in enumerate(zip(values,lo,hi))if v<l or v>h]
    assert violations==([count_row]if args.bound<len(g)else [])
    print(json.dumps(dict(nodes=start,productions=len(ys),constraints=len(lo),universe_steps=steps)),flush=True)
    begin=time.monotonic()
    result=milp(c,integrality=np.ones(nv,dtype=np.int32),bounds=Bounds(lower,upper),constraints=LinearConstraint(matrix,np.array(lo),np.array(hi)),options=dict(time_limit=args.seconds,mip_rel_gap=0,disp=True))
    report=dict(status=int(result.status),message=result.message,seconds=time.monotonic()-begin,universe_rounds=args.rounds,new_word_limit=args.new_limit,grammar_bound=args.bound,incumbent_128_positive_control=True,frozen_productions=len(locked),nodes=start,productions=len(ys),constraints=len(lo),objective=None if result.fun is None else float(result.fun),dual_bound=getattr(result,'mip_dual_bound',None),mip_gap=getattr(result,'mip_gap',None))
    if result.x is not None:
        ng={w:(a,b)for j,(w,a,b)in enumerate(ys,start)if result.x[j]>.5}
        report['candidate_rules_count']=len(ng)
        candidate=dict(data,status='FINE_ATOM_ROUTING_GRAMMAR_ONLY',properties=None,rules_count=len(ng),roots=list(map(norm,roots)),rules=[[w,*ng[w]]for w in sorted(ng)],routes=[dict(r,word=norm(r['word']))for r in data['routes']],finite_substrate=report)
        args.output.with_name(args.output.stem+'-grammar.json').write_text(json.dumps(candidate,indent=2)+'\n')
    args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2),flush=True)

if __name__=='__main__':main()
