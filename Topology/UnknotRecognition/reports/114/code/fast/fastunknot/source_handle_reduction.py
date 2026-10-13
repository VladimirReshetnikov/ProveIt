"""Certified empty-pattern dual-handle cancellations and cocore disc discovery.

This is the initial, empty-pattern stage. It does not silently discard a
pattern on a later hierarchy state and does not assert full admissibility.
"""
from collections import Counter, deque

from .normal_parallelity_geometry import _edge_links
from .source_handle_cohomology import _boundary_witness
from .normal_surface_geometry import _prepare, _coordinates, _fingerprint


def _source_handles(prepared, check):
    faces = []; owner = {}
    for i, (t, f, u, g, p) in enumerate(prepared['pairs']):
        check(); owner[t, f] = owner[u, g] = i
        faces.append(dict(id=i, tetrahedron=t, face=f, target_tetrahedron=u,
                          target_face=g, permutation=list(p), ends=[t, u]))
    edges = []
    for root, sectors in _edge_links(prepared, check).items():
        word = []
        for sector in sectors:
            check(); t, f = sector['tetrahedron'], sector['exit_face']; i = owner[t, f]
            word.append(dict(one_handle=i, forward=(t, f) == (faces[i]['tetrahedron'], faces[i]['face'])))
        edges.append(dict(id=root, ends=list(prepared['endpoints'][root]), attaching_cycle=word, sectors=sectors))
    boundary = {prepared['vertex_roots'][4*t+v] for t, f in prepared['boundary_faces'] for v in range(4) if v != f}
    vertices = sorted(set(prepared['vertex_roots'])-boundary)
    return dict(zero_handles=len(prepared['tetrahedra']), one_handles=faces, two_handles=edges, three_handles=vertices)


def _cocore_paths(handles, alive_faces, degree, check):
    """Put non-free edges first in a forest; a rejected free edge supplies a disc."""
    n=handles['zero_handles'];parent=list(range(n));sizes=[1]*n;forest=[[]for _ in range(n)];candidates=[]
    def root(v):
        while parent[v]!=v:parent[v]=parent[parent[v]];v=parent[v]
        return v
    for free in (False,True):
        for i in sorted(alive_faces):
            check()
            if (degree[i]==0)!=free:continue
            a,b=handles['one_handles'][i]['ends'];x,y=root(a),root(b)
            if x==y:
                if free:candidates.append(i)
                continue
            if sizes[x]<sizes[y]:x,y=y,x
            parent[y]=x;sizes[x]+=sizes[y];forest[a].append((b,i,True));forest[b].append((a,i,False))
    for candidate in candidates:
        start,target=handles['one_handles'][candidate]['ends'];previous={start:None};queue=deque([start])
        while target not in previous:
            check();v=queue.popleft()
            for w,i,forward in forest[v]:
                if w not in previous:previous[w]=(v,i,forward);queue.append(w)
        path=[];v=target
        while v!=start:
            u,i,forward=previous[v];path.append(dict(one_handle=i,forward=forward));v=u
        yield dict(one_handle=candidate,connecting_path=list(reversed(path)))


def reduce_source_handles(triangulation, *, max_moves=None, record_certificate=False, check=lambda:None):
    """Reduce the source dual handles for the empty boundary pattern.

    COMPLETE authenticates a partial geometric reduction, not admissibility.
    A non-null compressing_disc is a proper cocore transported through the
    cancellation trace, with a certified nonzero boundary cohomology period. Source manifolds may be reducible: this
    alone is not a solid-torus or knot verdict. A cap returns INCONCLUSIVE.
    """
    check()
    if type(record_certificate)is not bool:raise ValueError('record_certificate must be bool')
    if max_moves is not None and(type(max_moves)is not int or max_moves<0):raise ValueError('max_moves must be nonnegative or None')
    prepared=_prepare(triangulation,check);h=_source_handles(prepared,check)
    faces=set(range(len(h['one_handles'])));edges={e['id']:e for e in h['two_handles']};alive=set(edges);vertices=set(h['three_handles'])
    vertex_edges={v:[]for v in vertices}
    for e in h['two_handles']:
        for v in set(e['ends']):
            if v in vertices:vertex_edges[v].append(e['id'])
    queue=deque(e['id']for e in h['two_handles']if sum(v in vertices for v in e['ends'])==1)
    moves=[];stats=dict(cancelled_23=0,cancelled_12=0,incidence_updates=0)
    def capped():return max_moves is not None and len(moves)>=max_moves
    def incomplete():return dict(status='INCONCLUSIVE',reason='source handle move cap',stats=stats)
    while vertices:
        check()
        if not queue:raise ArithmeticError('interior vertex handles cannot reach the boundary')
        e=queue.popleft()
        if e not in alive:continue
        ends=[v for v in edges[e]['ends']if v in vertices]
        if len(ends)!=1:continue
        if capped():return incomplete()
        v=ends[0];moves.append(dict(kind='cancel_23',two_handle=e,three_handle=v));alive.remove(e);vertices.remove(v);stats['cancelled_23']+=1
        for other in vertex_edges[v]:
            check();stats['incidence_updates']+=1
            if other in alive and sum(w in vertices for w in edges[other]['ends'])==1:queue.append(other)
    occurrences={e:Counter(r['one_handle']for r in edges[e]['attaching_cycle'])for e in alive}
    incidence={i:{}for i in faces};degree=[0]*len(faces)
    for e,counts in occurrences.items():
        for i,n in counts.items():incidence[i][e]=n;degree[i]+=n
    queue=deque(i for i in sorted(faces)if degree[i]==1)
    while queue:
        check();i=queue.popleft()
        if i not in faces or degree[i]!=1:continue
        if capped():return incomplete()
        e=next(iter(incidence[i]));moves.append(dict(kind='cancel_12',one_handle=i,two_handle=e));faces.remove(i);alive.remove(e);stats['cancelled_12']+=1
        for j,n in occurrences[e].items():
            check();stats['incidence_updates']+=1;del incidence[j][e];degree[j]-=n
            if j in faces and degree[j]==1:queue.append(j)
    disc=None;stats['cocore_candidates_tested']=0
    for candidate in _cocore_paths(h,faces,degree,check):
        stats['cocore_candidates_tested']+=1
        witness=_boundary_witness(prepared,h,moves,faces,candidate['one_handle'],check)
        if witness is not None:
            disc=dict(candidate,boundary_witness=witness);break
    remaining=dict(one_handles=sorted(faces),two_handles=sorted(alive),three_handles=[])
    summary=dict(initial_handle_counts=[h['zero_handles'],len(h['one_handles']),len(h['two_handles']),len(h['three_handles'])],
        remaining_handle_counts=[h['zero_handles'],len(faces),len(alive),0],
        characteristic_zero_handle_indices=[dict(one_handle=i,index=-4+2*degree[i],multiplicity=2)for i in sorted(faces)])
    answer=dict(status='COMPLETE',boundary_pattern='empty',source_handles=h,moves=moves,remaining=remaining,
        summary=summary,compressing_disc=disc,stats=stats,trust='source handle reduction and optional cocore disc; no admissibility or knot verdict')
    if record_certificate:
        analysed=_coordinates(prepared,[[0]*7 for _ in prepared['tetrahedra']],check)
        answer['certificate']=dict(schema='source-handle-reduction-v1',input_sha256=_fingerprint(triangulation,analysed,check),
            boundary_pattern='empty',moves=moves,remaining=remaining,summary=summary,compressing_disc=disc)
    check();return answer
