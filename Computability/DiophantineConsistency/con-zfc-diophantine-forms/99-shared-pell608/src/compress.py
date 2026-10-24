"""Exact elimination of natural gate outputs used only linearly.

Each trace step is a full algebraic certificate, independent of the greedy
choice order. The checker reconstructs the selected monic row itself.
"""
from collections import defaultdict
import heapq


def normalize(terms):
    p = defaultdict(int)
    for coefficient, monomial in terms:
        p[tuple(monomial)] += coefficient
    return {m:c for m,c in p.items() if c}


def terms(p):
    return [[c,list(m)] for m,c in sorted(p.items()) if c]


def compress(equation):
    rows = [normalize(r['terms']) for r in equation['residuals']]
    labels = [r['label'] for r in equation['residuals']]
    count = len(equation['variables'])
    uses = [set() for _ in range(count)]
    nonlinear = [set() for _ in range(count)]

    def attach(rid, p, remove=False):
        vs = {v for m in p for v in m}
        ns = {v for m in p if len(m)>1 for v in m}
        for v in vs:
            if remove: uses[v].discard(rid)
            else: uses[v].add(rid)
        for v in ns:
            if remove: nonlinear[v].discard(rid)
            else: nonlinear[v].add(rid)

    definitions = {}
    for rid,p in enumerate(rows):
        attach(rid,p)
        if labels[rid] not in ('multiplication','addition'):
            continue
        vs = {v for m in p for v in m}
        if not vs: continue
        v=max(vs)
        if equation['variables'][v]['kind']!='gate' or p.get((v,))!=1:
            continue
        if any(c>0 for m,c in p.items() if m!=(v,)):
            continue
        if any(v in m for m in p if m!=(v,)):
            continue
        if v in definitions: raise ValueError('ambiguous gate definition')
        definitions[v]=rid
    queue=[-v for v in definitions if not nonlinear[v]]
    heapq.heapify(queue)
    eliminated=set()
    trace=[]
    while queue:
        v=-heapq.heappop(queue)
        if v in eliminated or nonlinear[v]: continue
        rid=definitions[v]
        if rows[rid] is None: continue
        definition=rows[rid]
        if definition.get((v,))!=1: raise ValueError('lost monicity')
        q={m:-c for m,c in definition.items() if m!=(v,)}
        if any(c<0 or len(m)>2 or v in m for m,c in q.items()):
            raise ValueError('invalid natural restoration')
        targets=sorted(uses[v]-{rid})
        trace.append({'variable':v,'definition_row':rid,'restoration':terms(q),'consumer_rows':targets})
        touched=set()
        attach(rid,definition,remove=True)
        touched.update(w for m in definition for w in m)
        rows[rid]=None
        for other in targets:
            p=rows[other]
            if any(v in m and m!=(v,) for m in p): raise ValueError('nonlinear consumer')
            factor=p[(v,)]
            attach(other,p,remove=True)
            touched.update(w for m in p for w in m)
            pp=dict(p)
            del pp[(v,)]
            for m,c in q.items(): pp[m]=pp.get(m,0)+factor*c
            pp={m:c for m,c in pp.items() if c}
            if any(len(m)>2 for m in pp): raise ValueError('degree increased')
            rows[other]=pp
            attach(other,pp)
            touched.update(w for m in pp for w in m)
        eliminated.add(v)
        for w in touched:
            if w in definitions and w not in eliminated and not nonlinear[w]:
                heapq.heappush(queue,-w)
    live=sorted({v for p in rows if p for m in p for v in m})
    remap={old:new for new,old in enumerate(live)}
    residuals=[{'label':labels[i],'terms':[[c,[remap[v] for v in m]] for m,c in sorted(p.items())]}
               for i,p in enumerate(rows) if p]
    out=dict(equation)
    out.pop('metrics',None)
    out['variables']=[equation['variables'][v] for v in live]
    out['residuals']=residuals
    out['variant']='cofinal11_power16_terminal'
    proof={'schema':'natural_monic_elimination_v1','steps':trace,'retained_indices':live,
           'retained_row_indices':[i for i,p in enumerate(rows) if p],
           'dropped_unused_indices':sorted(set(range(count))-set(live)-eliminated)}
    return out,proof


def expand(equation):
    out=defaultdict(int)
    for row in equation['residuals']:
        for ca,ma in row['terms']:
            for cb,mb in row['terms']:
                out[tuple(sorted(ma+mb))]+=ca*cb
    return {m:c for m,c in out.items() if c}
