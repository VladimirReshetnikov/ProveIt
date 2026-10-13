"""Exact forced private-leaf preprocessing before the width-dependent optimizer."""
from collections import deque
from .core import Instance,Edge,Decomposition,optimize


def peel_then_optimize(inst, decomposition=None, *, state_limit=None):
    if decomposition is not None:decomposition.validate(inst)
    m,n=inst.rows,inst.columns
    # Optional pivot restrictions need their own forcing proof. Keep this wrapper unrestricted.
    if any(e.count==1 and not e.allowed for e in inst.edges):
        raise ValueError('forced preprocessing currently requires unrestricted unit pivots')
    row_edges=[[] for _ in range(m)];total=[0]*n;owner=[0]*n
    for e in inst.edges:
        j=e.column-m;x=min(2,e.count)
        row_edges[e.row].append((j,x));total[j]+=x;owner[j]^=e.row
    queue=deque(j for j in range(n) if total[j]==1);live=set(range(m));prefix=[]
    while queue:
        j=queue.popleft()
        if total[j]!=1:continue
        r=owner[j]
        if r not in live:raise AssertionError('corrupt private-leaf state')
        prefix.append((r,j));live.remove(r)
        for k,x in row_edges[r]:
            total[k]-=x;owner[k]^=r
            if total[k]==1:queue.append(k)
    rr=sorted(live);cc=[j for j in range(n) if total[j]]
    rm={r:i for i,r in enumerate(rr)};cm={c:i for i,c in enumerate(cc)}
    if not rr:
        sub={'matching':[], 'retained_weight':0,'stats':{'width':-1,'peak_states':0,'state_visits':0,'bags':0}}
    else:
        reduced=Instance(len(rr),len(cc),tuple(inst.weights[r] for r in rr),
                         tuple(Edge(rm[e.row],len(rr)+cm[e.column-m],e.count,e.allowed)
                               for e in inst.edges if e.row in live))
        restricted=None
        if decomposition is not None:
            vm={**rm,**{m+c:len(rr)+j for c,j in cm.items()}}
            restricted=Decomposition(tuple(frozenset(vm[v] for v in bag if v in vm)
                                           for bag in decomposition.bags),
                                     decomposition.parent,decomposition.root)
        sub=optimize(reduced,restricted,state_limit=state_limit)
    pairs=prefix+[(rr[r],cc[c]) for r,c in sub['matching']]
    selected={r for r,c in pairs};score=sum(inst.weights[r] for r in selected)
    return {'schema':'ordered-pivot-plan-v1','matching':[list(p) for p in sorted(pairs)],
            'deferred_rows':sorted(set(range(m))-selected),'retained_weight':score,
            'deferred_weight':sum(inst.weights)-score,
            'stats':{**sub['stats'],'prepeeled_rows':len(prefix),'residual_rows_before_dp':len(rr)}}
