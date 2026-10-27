"""Authored exact references and sparse-delta acceleration; not a SAT solver.

The cubic reference evaluates the conditional-score formula in the incoming
asymmetric-packing report. No incoming program is imported or executed.
"""
from fractions import Fraction as F
from heapq import heapify, heappop, heappush

def prepare(adjacency,Q,h):
    if type(Q) is not int or Q<1 or type(h) is not int or h<2:
        raise ValueError('positive integer labels, integer h>=2 required')
    adj=[list(row) for row in adjacency]
    n=len(adj[0]) if adj else 0
    if any(len(row)!=n for row in adj):raise ValueError('ragged matrix')
    if any(type(x) is not int or x<0 for row in adj for x in row):
        raise ValueError('nonnegative integer edge multiplicities required')
    degrees=[sum(row) for row in adj];M=sum(degrees)
    C=max((sum(adj[i][j] for i in range(len(adj))) for j in range(n)),default=0)
    q=F(h*max(1,C)+1,h*max(1,C))
    powers=[F(1)]
    for _ in range(M):powers.append(powers[-1]*q)
    heap=[(0,a) for a in range(Q)];heapify(heap); row_labels=[]
    weights=[{} for _ in range(n)]
    for row,degree in zip(adj,degrees):
        load,a=heappop(heap);row_labels.append(a);heappush(heap,(load+degree,a))
        for j,w in enumerate(row):
            if w:weights[j][a]=weights[j].get(a,0)+w
    factors=[{a:(Q-1+powers[w])/Q for a,w in col.items()} for col in weights]
    future=[F(1)]*Q
    for col in factors:
        for a,f in col.items():future[a]*=f
    return dict(Q=Q,h=h,M=M,q=q,powers=powers,row_labels=row_labels,
                weights=weights,factors=factors,future=future)

def balance(adjacency,Q,h=8,method='sparse',certificate=False,checks=True,count=True):
    """Same labels and potentials for cubic, dense-delta and sparse methods.

    All share improved heap row grouping, sparse input aggregation and the
    same exact power/future caches. Timings therefore do not credit those
    common optimizations to sparse delta. Dense output materialization is paid
    by all methods. checks=False skips invariant checks, not exact arithmetic.
    """
    if method not in ('cubic','dense','sparse'):raise ValueError('unknown method')
    z=prepare(adjacency,Q,h);powers=z['powers'];future=z['future'][:]
    current=Q*sum(future,F(0)); initial=current
    loads=[{} for _ in range(Q)]; labels=[]; steps=[]
    stats=dict(score_terms=0,score_multiplications=0,active_row_updates=0,
               candidate_scans=0,columns=len(z['weights']),edges=z['M'])
    for col,factors in zip(z['weights'],z['factors']):
        nxt=future[:]
        for a,f in factors.items():nxt[a]/=f
        if method=='cubic':
            scores=[]
            for b in range(Q):
                score=F(0)
                for a in range(Q):
                    inner=F(0);w=col.get(a,0)
                    for c in range(Q):
                        inner+=powers[loads[a].get(c,0)+(w if c==b else 0)]
                        if count:stats['score_terms']+=1
                    score+=nxt[a]*inner
                    if count:stats['score_multiplications']+=1
                scores.append(score)
            chosen=min(range(Q),key=lambda b:(scores[b],b))
            after=scores[chosen]
            if count:stats['candidate_scans']+=Q
            if checks and sum(scores,F(0))/Q!=current:raise ArithmeticError('averaging')
        else:
            delta={}
            for a,w in col.items():
                U=nxt[a]*(powers[w]-1)
                cells=loads[a].items() if method=='sparse' else ((b,loads[a].get(b,0)) for b in range(Q))
                for b,load in cells:
                    term=U*(powers[load]-1)
                    if term:delta[b]=delta.get(b,F(0))+term
                    if count:
                        stats['score_terms']+=1;stats['score_multiplications']+=1
            if len(delta)<Q:
                chosen=0
                while chosen in delta:
                    chosen+=1
                    if count:stats['candidate_scans']+=1
                if count:stats['candidate_scans']+=1
            else:
                chosen=min(delta,key=lambda b:(delta[b],b))
                if count:stats['candidate_scans']+=Q
            mean=sum(delta.values(),F(0))/Q
            after=current+delta.get(chosen,F(0))-mean
            scores=[current+delta.get(b,F(0))-mean for b in range(Q)] if certificate else None
        if checks and after>current:raise ArithmeticError('potential increased')
        if certificate:steps.append(dict(before=current,scores=scores,selected=chosen,after=after))
        labels.append(chosen)
        for a,w in col.items():loads[a][chosen]=loads[a].get(chosen,0)+w
        if count:stats['active_row_updates']+=len(col)
        current=after;future=nxt
    final=sum((powers[loads[a].get(b,0)] for a in range(Q) for b in range(Q)),F(0))
    if checks and (current!=final or final>initial):raise ArithmeticError('final potential')
    dense=[[loads[a].get(b,0) for b in range(Q)] for a in range(Q)]
    return dict(row_labels=z['row_labels'],column_labels=labels,loads=dense,
                initial=initial,final=final,steps=steps,stats=stats)
