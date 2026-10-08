"""Small, independently packaged dart reference for the research experiments.

RIII reconnection and RI/II tests are adapted from ProveIt's simplify.py at
34f2689e96e04a13a32d133173b5e41a34320086 (MIT-0). This is NOT a byte-identical
checkout. It deliberately uses immutable states, full validation and no cache.
Crossing slots are counterclockwise; even slots under, odd slots over.
"""
from __future__ import annotations
from collections import defaultdict
from dataclasses import dataclass
from layered_search import Action

@dataclass(frozen=True)
class Darts:
    alpha: tuple[int, ...]
    @property
    def n(self): return len(self.alpha) // 4
    def nxt(self, d):
        a = self.alpha[d]
        return (a & -4) | ((a+1) & 3)
    def faces(self):
        seen = set()
        for start in range(len(self.alpha)):
            if start in seen: continue
            face, d = [], start
            while d not in seen:
                seen.add(d); face.append(d); d = self.nxt(d)
            yield tuple(face)
    def validate(self, knot=True):
        a = self.alpha
        if len(a) % 4 or any(type(x) is not int or not 0 <= x < len(a) for x in a):
            raise ValueError("invalid dart array")
        if any(a[x] == x or a[a[x]] != x for x in range(len(a))):
            raise ValueError("edge pairing is not a fixed-point-free involution")
        if not a: return
        visited, todo = set(), [0]
        while todo:
            d = todo.pop()
            if d in visited: continue
            visited.add(d); todo.extend((a[d], d ^ 2))
        if knot and len(visited) != len(a): raise ValueError("not one knot component")
        if len(list(self.faces())) != self.n+2: raise ValueError("not a connected spherical map")
    def pd(self):
        names = {}
        labels = [names.setdefault(min(d, p), len(names)) for d,p in enumerate(self.alpha)]
        return tuple(tuple(labels[i:i+4]) for i in range(0,len(labels),4))

def from_pd(rows, *, validate=True):
    rows = [tuple(r) for r in rows]
    if any(len(r)!=4 or any(type(v) is not int for v in r) for r in rows):
        raise ValueError("PD rows must be four integers")
    where = defaultdict(list)
    for i,r in enumerate(rows):
        for j,x in enumerate(r): where[x].append(4*i+j)
    if any(len(v)!=2 for v in where.values()): raise ValueError("each label must occur twice")
    alpha = [0]*(4*len(rows))
    for x,y in where.values(): alpha[x],alpha[y] = y,x
    result = Darts(tuple(alpha))
    if validate: result.validate()
    return result

def from_braid(strands, word):
    word = list(word)
    if type(strands) is not int or strands<1: raise ValueError("invalid strand count")
    if any(type(g) is not int or not 1<=abs(g)<strands for g in word):
        raise ValueError("invalid braid generator")
    p = list(range(strands))
    for g in word:
        i=abs(g)-1; p[i],p[i+1]=p[i+1],p[i]
    seen=set(); x=0
    while x not in seen: seen.add(x); x=p[x]
    if len(seen)!=strands: raise ValueError("braid closes to a link")
    if not word: return Darts(())
    current=list(range(strands)); next_label=strands; rows=[]
    for g in word:
        i=abs(g)-1; left,right=current[i:i+2]; ol,orr=next_label,next_label+1; next_label+=2
        rows.append((right,left,ol,orr) if g>0 else (left,ol,orr,right))
        current[i],current[i+1]=ol,orr
    parent=list(range(next_label))
    def find(x):
        while parent[x]!=x:
            parent[x]=parent[parent[x]]; x=parent[x]
        return x
    for top,bottom in enumerate(current): parent[find(top)]=find(bottom)
    return from_pd([[find(x) for x in row] for row in rows])

def footprint(state, core_darts):
    local={4*(d//4)+j for d in core_darts for j in range(4)}
    return frozenset(local | {state.alpha[d] for d in local})

def triangles(state):
    for f in state.faces():
        if len(f)==3 and len({d//4 for d in f})==3 and any(d%2 and state.alpha[d]%2 for d in f):
            yield tuple(f)

def triangle_patch(state, triangle):
    """Return the constant-size pairing patch, reading only the footprint."""
    alpha=state.alpha
    inner=[alpha[d] for d in triangle]
    entry=[d^2 for d in triangle]; exit_=[i^2 for i in inner]
    moved={}
    for k in range(3): moved[entry[k]]=inner[k]; moved[exit_[k]]=triangle[k]
    if len(moved)!=6: raise ValueError("degenerate triangle")
    links=[]
    for x,new_x in moved.items():
        new_y=moved.get(alpha[x],alpha[x])
        if new_y==new_x: raise ValueError("degenerate reconnection")
        links.append((new_x,new_y))
    links.extend((exit_[k],entry[k]) for k in range(3))
    return tuple(links)

def apply_triangle(state, triangle):
    alpha=list(state.alpha)
    for x,y in triangle_patch(state,triangle): alpha[x],alpha[y]=y,x
    return Darts(tuple(alpha))

def reductions(state):
    for f in state.faces():
        if len(f)==1:
            yield ("R1", f)
        elif len(f)==2 and f[0]//4!=f[1]//4 and all(d%2==state.alpha[d]%2 for d in f):
            yield ("R2", f)

def remove_reduction(state, terminal):
    # Splice opposite ports through every deleted crossing; rebuild live labels.
    kind,face=terminal
    if terminal not in list(reductions(state)): raise ValueError("illegal reduction")
    removed={d//4 for d in face}; a=list(state.alpha)
    live=[d for d in range(len(a)) if d//4 not in removed]
    updated={}
    for d in live:
        p=a[d]
        for _ in range(len(a)+1):
            if p//4 not in removed: break
            p=a[p^2]
        else: raise ArithmeticError("splice did not exit removed crossings")
        updated[d]=p
    ids={d:i for i,d in enumerate(live)}
    result=Darts(tuple(ids[updated[d]] for d in live)); result.validate()
    return result

def reduce_12(state):
    count=0
    while True:
        terminal=next(reductions(state),None)
        if terminal is None: return state,count
        state=remove_reduction(state,terminal); count+=1

def projection_graph(state):
    adj=[set() for _ in range(state.n)]
    for d,p in enumerate(state.alpha):
        if d//4!=p//4: adj[d//4].add(p//4)
    return tuple(frozenset(s) for s in adj)

class R3System:
    def actions(self,state):
        for f in triangles(state):
            # The production implementation excludes degenerate trials.
            try: apply_triangle(state,f)
            except ValueError: continue
            yield Action(tuple(sorted(f)),footprint(state,f),f)
    def _checked_face(self,state,action):
        d=action.key[0]
        if not 0<=d<len(state.alpha): raise ValueError("invalid dart")
        e=state.nxt(d); f=state.nxt(e); face=(d,e,f)
        if state.nxt(f)!=d or len({x//4 for x in face})!=3 or tuple(sorted(face))!=action.key:
            raise ValueError("not a triangular face")
        if not any(x%2 and state.alpha[x]%2 for x in face):
            raise ValueError("RIII over/under condition failed")
        if footprint(state,face)!=action.footprint: raise ValueError("stale footprint")
        return face
    def apply(self,state,action):
        return apply_triangle(state,self._checked_face(state,action))
    def apply_layer(self,state,layer):
        # All patches are computed in the same pre-layer state. There is only
        # one global array copy, and a failure leaves the input untouched.
        patches=[]; used=set()
        for action in layer:
            if not used.isdisjoint(action.footprint): raise ValueError("overlapping layer")
            used.update(action.footprint)
            patches.append(triangle_patch(state,self._checked_face(state,action)))
        alpha=list(state.alpha)
        for patch in patches:
            for x,y in patch: alpha[x],alpha[y]=y,x
        return Darts(tuple(alpha))
    def goal(self,state): return next(reductions(state),None)
