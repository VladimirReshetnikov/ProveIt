"""Common-disk certificates from the rotation system of a processed PD prefix.

A certificate is combinatorial, independent of the number of smoothing states.
No claim that a low-width certified order exists for every knot is made.
"""
from __future__ import annotations
from dataclasses import dataclass, asdict
from collections import defaultdict, deque
from hashlib import sha256
import json

class GeometryError(ValueError):
    """No certified common disk; this is not a knot verdict."""


def canonical_cycle(values):
    values=tuple(values)
    if not values: return ()
    if len(set(values))!=len(values): raise GeometryError('repeated frontier label')
    k=values.index(min(values)); a=values[k:]+values[:k]
    rev=values[::-1]; k=rev.index(min(rev)); b=rev[k:]+rev[:k]
    return min(a,b)


def connected(vertices,adj):
    vertices=set(vertices)
    if not vertices: return True
    seen={next(iter(vertices))}; stack=list(seen)
    while stack:
        for y in adj[stack.pop()]:
            if y in vertices and y not in seen: seen.add(y);stack.append(y)
    return len(seen)==len(vertices)


def ribbon_data(pd):
    pd=[tuple(c) for c in pd]
    if any(len(c)!=4 or any(type(x) is not int for x in c) for c in pd):
        raise GeometryError('crossings require four integer edge labels')
    occurrence=defaultdict(list)
    for v,crossing in enumerate(pd):
        for j,label in enumerate(crossing): occurrence[label].append(4*v+j)
    if any(len(ds)>2 for ds in occurrence.values()):
        raise GeometryError('edge label occurs more than twice')
    alpha=list(range(4*len(pd)))
    adj=[set() for _ in pd]; internal=0
    for ds in occurrence.values():
        if len(ds)==2:
            a,b=ds;alpha[a]=b;alpha[b]=a;internal+=1
            adj[a//4].add(b//4);adj[b//4].add(a//4)
    phi=[4*(alpha[d]//4)+(alpha[d]%4+1)%4 for d in range(len(alpha))]
    cycles=[];seen=set()
    for d in range(len(alpha)):
        if d in seen: continue
        cycle=[];x=d
        while x not in seen:
            seen.add(x);cycle.append(x);x=phi[x]
        if x!=d: raise GeometryError('boundary walk is not a permutation cycle')
        cycles.append(tuple(cycle))
    return pd,occurrence,adj,internal,cycles


@dataclass(frozen=True)
class DiskCertificate:
    prefix_sha256: str
    vertices: int
    internal_edges: int
    boundary_components: int
    boundary_walks: tuple[tuple[int,...],...]
    cyclic_order: tuple[int,...]

    def as_dict(self): return asdict(self)


def certify_disk(pd) -> DiskCertificate:
    """Certify a connected planar ribbon prefix with one marked boundary.

    Each internal dart is paired by alpha; a frontier dart is fixed by alpha.
    Boundary cycles are sigma alpha. Unmarked holes may be filled. At a closed
    boundary the empty order is allowed. Disconnected prefixes are declined.
    """
    pd,occ,adj,e,walks=ribbon_data(pd)
    n=len(pd)
    digest=sha256(json.dumps(pd,separators=(',',':')).encode()).hexdigest()
    if not n: return DiskCertificate(digest,0,0,0,(),())
    if not connected(range(n),adj): raise GeometryError('processed ribbon graph is disconnected')
    if n-e+len(walks)!=2: raise GeometryError('processed ribbon surface has positive genus')
    marked=[]
    for cycle in walks:
        labels=tuple(pd[d//4][d%4] for d in cycle if len(occ[pd[d//4][d%4]])==1)
        if labels: marked.append(labels)
    if len(marked)>1: raise GeometryError('frontier lies on more than one boundary component')
    order=canonical_cycle(marked[0]) if marked else ()
    return DiskCertificate(digest,n,e,len(walks),tuple(walks),order)


def verify_disk_certificate(pd,certificate):
    """Recompute the rotation-system proof and compare all certificate fields."""
    expected=certify_disk(pd).as_dict()
    supplied=certificate.as_dict() if isinstance(certificate,DiskCertificate) else certificate
    normalize=lambda x:json.dumps(x,sort_keys=True,separators=(',',':'))
    if normalize(expected)!=normalize(supplied): raise GeometryError('disk certificate mismatch')
    return True


def verify_common_order(matchings,cyclic_order):
    order=tuple(cyclic_order)
    if len(set(order))!=len(order): raise GeometryError('cyclic order repeats labels')
    position={x:i for i,x in enumerate(order)}
    for matching in set(tuple(m) for m in matchings):
        partner={}
        for a,b in matching:
            if a==b or a in partner or b in partner: raise GeometryError('not a perfect matching')
            partner[a]=b;partner[b]=a
        if set(partner)!=set(position): raise GeometryError('matching and frontier disagree')
        stack=[]
        for i,a in enumerate(order):
            j=position[partner[a]]
            if i<j: stack.append(j)
            elif not stack or stack.pop()!=i: raise GeometryError('matching crosses the supplied cyclic order')
        if stack: raise GeometryError('unbalanced matching stack')
    return True


def diagram_graph(pd):
    pd,occ,adj,e,walks=ribbon_data(pd)
    if any(len(ds)!=2 for ds in occ.values()): raise GeometryError('diagram is not closed')
    if pd and (not connected(range(len(pd)),adj) or len(pd)-e+len(walks)!=2):
        raise GeometryError('diagram is not connected and genus zero')
    return adj


def bipolar_order(pd):
    """Polynomial ear-insertion construction of an st-order for a biconnected PD.

    We use a deliberately simple O(n^3) upper bound, not a linear-time claim.
    A chosen component outside the ordered set has two distinct attachments;
    insert a path between them immediately after the earlier attachment.
    """
    adj=diagram_graph(pd);n=len(adj)
    if n<=1: return list(range(n))
    vertices=set(range(n))
    if any(not connected(vertices-{v},adj) for v in vertices):
        raise GeometryError('crossing graph has an articulation; decompose or supply another order')
    s=0;t=min(adj[s]-{s});order=[s,t];inside={s,t}
    while len(inside)<n:
        start=min(vertices-inside);component={start};stack=[start]
        while stack:
            for y in adj[stack.pop()]-inside-component: component.add(y);stack.append(y)
        attachment={a:[] for a in inside if adj[a]&component}
        if len(attachment)<2: raise GeometryError('missing second attachment in biconnected graph')
        ordered_attachments=sorted(attachment,key=order.index)
        a,z=ordered_attachments[0],ordered_attachments[-1]
        starts=sorted(adj[a]&component);targets=adj[z]&component
        parent={v:None for v in starts};queue=deque(starts);end=None
        while queue:
            x=queue.popleft()
            if x in targets: end=x;break
            for y in sorted(adj[x]&component):
                if y not in parent: parent[y]=x;queue.append(y)
        if end is None: raise GeometryError('ear path is missing')
        path=[]
        while end is not None: path.append(end);end=parent[end]
        path.reverse();at=order.index(a)+1;order[at:at]=path;inside.update(path)
    # Cheap graph assertions plus the independently computed geometric certificate.
    validate_connected_cut_order(pd,order)
    return order


def validate_connected_cut_order(pd,order):
    adj=diagram_graph(pd);n=len(adj)
    if sorted(order)!=list(range(n)): raise GeometryError('order is not a permutation')
    for k in range(1,n):
        if not connected(order[:k],adj) or not connected(order[k:],adj):
            raise GeometryError('prefix or suffix crossing graph is disconnected')
        certify_disk([pd[j] for j in order[:k]])
    return True
