"""Necessary chain-parity diagnostics. These are NOT source-realization tests.

Exact mode uses the actual parity of supplied counts. Saturated mode asks only
whether some lift of the categories 0,1,>=2 satisfies the necessary cycle condition.
It must not be used to change an authenticated count or to certify a 3-manifold.
"""
from activation_forest.model import DSU


def exact_parity_defects(inst):
    defects=[]
    for h in range(inst.columns):
        odd=set()
        for e,row in enumerate(inst.matrix):
            if row[h] & 1:
                for v in inst.edges[e]:
                    if v in odd: odd.remove(v)
                    else: odd.add(v)
        if odd: defects.append(dict(column=h,odd_vertices=sorted(odd)))
    return defects


def saturated_parity_completion(inst):
    result=[]
    for h in range(inst.columns):
        odd=set();forest=[[] for _ in range(inst.vertices)];ds=DSU(inst.vertices)
        for e,row in enumerate(inst.matrix):
            if row[h]==1:
                for v in inst.edges[e]:
                    if v in odd: odd.remove(v)
                    else: odd.add(v)
            elif row[h]>=2:
                u,v=inst.edges[e]
                if ds.union(u,v):
                    forest[u].append((v,e));forest[v].append((u,e))
        components={}
        for v in range(inst.vertices): components.setdefault(ds.find(v),[]).append(v)
        for part in components.values():
            demand=sorted(set(part)&odd)
            if len(demand)%2:
                return dict(possible=False,column=h,heavy_component=part,odd_unit_vertices=demand)
        chosen=[];seen=set()
        for root in range(inst.vertices):
            if root in seen: continue
            parent={root:(None,None)};order=[root];seen.add(root)
            for v in order:
                for w,e in forest[v]:
                    if w not in seen:
                        seen.add(w);parent[w]=(v,e);order.append(w)
            for v in reversed(order[1:]):
                u,e=parent[v]
                if v in odd:
                    chosen.append(e);odd.remove(v)
                    if u in odd: odd.remove(u)
                    else: odd.add(u)
        if odd: raise AssertionError('even-demand forest lift failed')
        result.append(sorted(chosen))
    return dict(possible=True,odd_heavy_rows_by_column=result)
