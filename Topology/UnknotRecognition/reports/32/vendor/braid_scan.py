"""Small braid-scanning research harness, not the upstream optimized recognizer.

The crossing/delooping topology is adapted from ProveIt geometry.py and
algebra.py, reviewed 7 October 2026; see PROVENANCE.json. Reductions use this
package's independently implemented scalar-pivot or radical-transfer backend.
Closure is the representable functor Hom(identity_matching, -).
SPDX-License-Identifier: MIT-0
"""
from __future__ import annotations
from collections import defaultdict
from dataclasses import dataclass
from itertools import product
from time import perf_counter
from radical import ArcAlgebra, Obj, Mat, bits, transfer, pivot_reduce, survivor_profile, rank_binary, check_contraction

SMOOTHINGS = (((0,1),(2,3)), ((0,3),(1,2)))


def find(parent, x):
    root=x
    while parent[root] != root: root=parent[root]
    while parent[x] != x:
        nxt=parent[x]; parent[x]=root; x=nxt
    return root


@dataclass
class Glued:
    matching: int
    closed: int
    arc_of: dict


class BraidArc(ArcAlgebra):
    def __init__(self):
        super().__init__()
        self.gluing_cache={}
        self.transfer_cache={}

    def glue(self, m, s, slots):
        key=(m,s,slots)
        if key in self.gluing_cache: return self.gluing_cache[key]
        pairs=self.pairs[m]
        points={p for pair in pairs for p in pair}
        adj=defaultdict(list)
        def edge(a,b,arc):
            adj[a].append((b,arc)); adj[b].append((a,arc))
        for pair in pairs:
            p,q=pair; edge(('P',p),('P',q),('m',pair))
        for j,(a,b) in enumerate(SMOOTHINGS[s]):
            edge(('S',a),('S',b),('s',j))
        seen={}
        for j,p in enumerate(slots):
            if p in points: edge(('S',j),('P',p),None)
            elif p in seen: edge(('S',j),('S',seen[p]),None)
            else: seen[p]=j
        visited=set(); newpairs=[]; arc_of={}; closed=0
        for start in adj:
            if start in visited: continue
            stack=[start]; visited.add(start); ends=[]; arcs=set()
            while stack:
                v=stack.pop()
                if len(adj[v])==1:
                    ends.append(v[1] if v[0]=='P' else slots[v[1]])
                for w,arc in adj[v]:
                    if arc is not None: arcs.add(arc)
                    if w not in visited: visited.add(w); stack.append(w)
            if ends:
                if len(ends)!=2 or ends[0]==ends[1]: raise ArithmeticError('bad gluing')
                pair=tuple(sorted(ends)); newpairs.append(pair); ref=('new',pair)
            else:
                ref=('closed',closed); closed+=1
            for arc in arcs: arc_of[arc]=ref
        ans=Glued(self.intern(tuple(sorted(newpairs))),closed,arc_of)
        self.gluing_cache[key]=ans
        return ans

    def crossing_entries(self,a,b,f,s,t,slots):
        key=(a,b,s,t,slots)
        if key not in self.transfer_cache:
            self.transfer_cache[key]=self._transfer_plan(a,b,s,t,slots)
        gs,gt,plans=self.transfer_cache[key]
        entries=[]
        for ls,lt,components in plans:
            value=0
            for mask in bits(f):
                out=1
                for source,boundary,extra in components:
                    dots=(mask&source).bit_count()+extra
                    if dots>=2 or (not boundary and dots!=1): out=0; break
                    if not boundary: continue
                    choices=(boundary,) if dots else tuple(boundary^(1<<j) for j in bits(boundary))
                    nxt=0
                    for u in bits(out):
                        for v in choices: nxt^=1<<(u|v)
                    out=nxt
                value^=out
            if value: entries.append((ls,lt,value))
        return gs,gt,entries

    def _transfer_plan(self,a,b,s,t,slots):
        gs,gt=self.glue(a,s,slots),self.glue(b,t,slots)
        owner,c=self.basis(a,b); new_owner,_=self.basis(gs.matching,gt.matching)
        saddle=s!=t
        discs=[('F',j) for j in range(c)]+([('I',0)] if saddle else [('I',0),('I',1)])
        def idisc(j): return ('I',0 if saddle else j)
        parent={d:d for d in discs}
        points={p for pair in self.pairs[a] for p in pair}
        arc_of_slot={v:j for j,pair in enumerate(SMOOTHINGS[s]) for v in pair}
        joins=[]; seen={}
        for j,label in enumerate(slots):
            if label in points: joins.append((('F',owner[label]),idisc(arc_of_slot[j])))
            elif label in seen: joins.append((idisc(arc_of_slot[seen[label]]),idisc(arc_of_slot[j])))
            else: seen[label]=j
        for x,y in joins:
            x,y=find(parent,x),find(parent,y)
            if x!=y: parent[x]=y
        members=defaultdict(list)
        for d in discs: members[find(parent,d)].append(d)
        roots=list(members); idx={r:j for j,r in enumerate(roots)}
        comp={d:idx[find(parent,d)] for d in discs}
        gluings=[0]*len(roots)
        for x,y in joins: gluings[comp[x]]+=1
        boundary=[0]*len(roots); closed_s=[None]*gs.closed; closed_t=[None]*gt.closed
        def record(disc,ref,closed):
            kind,value=ref
            if kind=='new': boundary[comp[disc]] |= 1<<new_owner[value[0]]
            else: closed[value]=comp[disc]
        for m,g,closed in ((a,gs,closed_s),(b,gt,closed_t)):
            for pair in self.pairs[m]: record(('F',owner[pair[0]]),g.arc_of['m',pair],closed)
            for j in range(2): record(idisc(j),g.arc_of['s',j],closed)
        if None in closed_s or None in closed_t: raise ArithmeticError('missing circle')
        base_chi=[len(members[r])-gluings[j] for j,r in enumerate(roots)]
        inputs=[0]*len(roots)
        for j in range(c): inputs[comp['F',j]] |= 1<<j
        plans=[]
        for ls in product((0,1),repeat=gs.closed):
            for lt in product((0,1),repeat=gt.closed):
                chi=base_chi[:]; extra=[0]*len(roots)
                for q,lab in zip(closed_s,ls): chi[q]+=1; extra[q]+=lab
                for q,lab in zip(closed_t,lt): chi[q]+=1; extra[q]+=1-lab
                components=[]
                for q in range(len(roots)):
                    genus2=2-chi[q]-boundary[q].bit_count()
                    if genus2<0 or genus2%2: raise ArithmeticError('impossible genus')
                    if genus2 or extra[q]>=2: break
                    components.append((inputs[q],boundary[q],extra[q]))
                else: plans.append((ls,lt,components))
        return gs,gt,plans


def attach(d:Mat,alg:BraidArc,slots,positive:bool) -> Mat:
    obs=[]; index={}; glued={}
    def smoothing(i): return 1-i if positive else i
    for j,o in enumerate(d.src):
        for i in (0,1):
            g=alg.glue(o.matching,smoothing(i),slots); glued[j,i]=g
            for labels in product((0,1),repeat=g.closed):
                index[j,i,labels]=len(obs); obs.append(Obj(g.matching,o.degree+i))
    cols=[{} for _ in obs]
    def put(a,b,v):
        v^=cols[a].get(b,0)
        if v: cols[a][b]=v
        else: cols[a].pop(b,None)
    for j,o in enumerate(d.src):
        for ls,lt,v in alg.crossing_entries(o.matching,o.matching,1,smoothing(0),smoothing(1),slots)[2]:
            put(index[j,0,ls],index[j,1,lt],v)
        for q,f in d.cols[j].items():
            for i in (0,1):
                for ls,lt,v in alg.crossing_entries(o.matching,d.src[q].matching,f,smoothing(i),smoothing(i),slots)[2]:
                    put(index[j,i,ls],index[q,i,lt],v)
    obs=tuple(obs)
    return Mat(obs,obs,cols)


def close(d:Mat,alg:ArcAlgebra,closure_matching:int,negative_crossings:int=0):
    basis=[]; index={}; bydegree=defaultdict(list)
    for j,o in enumerate(d.src):
        c=alg.basis(closure_matching,o.matching)[1]
        for mask in range(1<<c):
            index[j,mask]=len(basis); bydegree[o.degree-negative_crossings].append(len(basis))
            basis.append((j,mask))
    out=[]
    for j,mask in basis:
        col=0
        for q,f in d.cols[j].items():
            g=alg.compose(closure_matching,d.src[j].matching,d.src[q].matching,1<<mask,f)
            for term in bits(g): col ^= 1<<index[q,term]
        out.append(col)
    ranks={h:rank_binary([out[j] for j in ids]) for h,ids in bydegree.items()}
    for col in out:
        square=0
        for j in bits(col): square ^= out[j]
        if square: raise ArithmeticError('closed differential squared nonzero')
    profile={h:len(ids)-ranks.get(h,0)-ranks.get(h-1,0) for h,ids in sorted(bydegree.items())}
    return {h:n for h,n in profile.items() if n}


def scan_braid(strands:int,word:list[int],*,backend='transfer',certificate=False,validate=True):
    if type(strands) is not int or strands<1: raise ValueError('invalid strands')
    if any(type(x) is not int or not 0<abs(x)<strands for x in word): raise ValueError('invalid braid')
    if backend not in ('transfer','pivot'): raise ValueError('invalid backend')
    alg=BraidArc(); tops=list(range(strands)); bottoms=list(range(strands,2*strands)); nxt=2*strands
    ident=alg.intern(tuple(sorted(zip(tops,bottoms)))); obs=(Obj(ident,0),); d=Mat(obs,obs,[{}]); trace=[]
    for step,letter in enumerate(word):
        j=abs(letter)-1; new0,new1=nxt,nxt+1; nxt+=2
        slots=(bottoms[j],bottoms[j+1],new1,new0)
        d=attach(d,alg,slots,letter>0); before=len(d.src); predicted=sum(survivor_profile(d).values())
        started=perf_counter()
        if backend=='transfer':
            t=transfer(d,alg,certificate=certificate,validate=validate)
            elapsed=perf_counter()-started
            if certificate: check_contraction(t,alg)
            d=t.d; depth=t.series_depth
        else:
            d=pivot_reduce(d,alg); elapsed=perf_counter()-started; depth=None
        if len(d.src)!=predicted: raise ArithmeticError('wrong minimal count')
        trace.append({'step':step+1,'pre_objects':before,'survivors':predicted,'depth':depth,'reduce_seconds':elapsed})
        bottoms[j:j+2]=[new0,new1]
    closure=alg.intern(tuple(sorted(zip(tops,bottoms))))
    rank=close(d,alg,closure,sum(x<0 for x in word))
    return {'unreduced_by_degree':rank,'unreduced_rank':sum(rank.values()),'trace':trace}
