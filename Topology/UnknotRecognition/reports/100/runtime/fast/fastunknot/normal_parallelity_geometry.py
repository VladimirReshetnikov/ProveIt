"""Source product handles, complete base polygons and bounded complementary handles."""
from itertools import combinations

from .normal_surface_geometry import _edge, _quad
from .normal_cut_boundary import _cycle_recipes


def _edge_links(prepared, check):
    representatives = {}
    for t in range(len(prepared['tetrahedra'])):
        for a, b in combinations(range(4), 2):
            representatives.setdefault(prepared['edge_roots'][_edge(t, a, b)], (t, a, b))
    links = {}
    for root, (t, a, b) in sorted(representatives.items()):
        if root in prepared['boundary_incidence']: continue
        faces = [f for f in range(4) if f not in (a, b)]; entry, exit = faces
        initial = (t, a, b, entry); state = initial; wedges = []; seen = set()
        while state not in seen:
            check(); seen.add(state); t, a, b, entry = state
            exit = next(f for f in range(4) if f not in (a, b, entry))
            e = prepared['tetrahedra'][t][exit]
            if e is None: raise ArithmeticError('interior edge link reached the boundary')
            u, p = e['tetrahedron'], e['permutation']; c, d = sorted((p[a], p[b])); g = p[exit]
            wedges.append(dict(tetrahedron=t, edge=[a, b], entry_face=entry, exit_face=exit,
                               target_tetrahedron=u, target_edge=[c, d], target_face=g))
            state = (u, c, d, g)
        if state != initial: raise ArithmeticError('interior edge link did not close')
        links[root] = wedges
    return links


def _parallelity_geometry(prepared, analysed, check):
    rows = analysed['rows']; links = _edge_links(prepared, check)
    layout = []; total = 0
    core0 = []; by_chamber = {}
    for t, row in enumerate(rows):
        q = sum(row[4:]); kind = next((j for j in range(3) if row[4+j]), None)
        chain = total; tips = []; total += q+1
        marks = [(chain, 'central' if q == 0 else 'quad_a', None)]
        if q: marks.append((chain+q, 'quad_b', None))
        for v, count in enumerate(row[:4]):
            tips.append(total)
            if count: marks.append((total, 'triangle_tip', v))
            total += count
        for point, name, v in marks:
            index = len(core0); by_chamber[point] = index
            core0.append(dict(id=index, tetrahedron=t, kind=name, vertex=v, source_chamber=point))
        layout.append((chain, tips, q, kind))

    def chamber_face(t, f, v, rank):
        chain, tips, q, kind = layout[t]
        if v == -1: return chain+(q if kind is not None and f in (0, kind+1) else 0)
        m = rows[t][v]
        if rank < m: return tips[v]+rank
        if kind is None or _quad(f, v) != kind: raise ArithmeticError('invalid face chamber rank')
        return chain+(rank-m if v in (0, kind+1) else q-rank+m)

    def edge_chamber(t, a, b, rank):
        local = _edge(t, a, b); root = prepared['edge_roots'][local]; w = analysed['weights'][root]
        k = w-rank if prepared['edge_orientations'][local] else rank
        chain, tips, q, kind = layout[t]; ta, tb = rows[t][a], rows[t][b]
        crossing = q if kind is not None and kind != _quad(a, b) else 0
        if k < ta: return tips[a]+k
        if k > ta+crossing: return tips[b]+w-k
        if crossing: return chain+(k-ta if a in (0, kind+1) else q-k+ta)
        return chain+(q if kind is not None and a not in (0, kind+1) else 0)

    core1 = []; core_face = {}
    for t, f, u, g, p in prepared['pairs']:
        for v in [-1]+[v for v in range(4) if v != f and rows[t][v]+rows[t][4+_quad(f, v)]]:
            index = len(core1); core_face[t, f, v] = index
            a = chamber_face(t, f, v, 0); b = chamber_face(u, g, p[v] if v >= 0 else -1, 0)
            if a not in by_chamber or b not in by_chamber: raise ArithmeticError('nonparallel face has a prism end')
            core1.append(dict(id=index, tetrahedron=t, face=f, corner=v, ends=[by_chamber[a], by_chamber[b]],
                              target_tetrahedron=u, target_face=g, permutation=list(p)))
    def face_region(t, f, a, b, rank):
        root = prepared['edge_roots'][_edge(t, a, b)]; w = analysed['weights'][root]
        k = w-rank if prepared['edge_orientations'][_edge(t, a, b)] else rank
        n = rows[t][a]+rows[t][4+_quad(f, a)]
        return (-1, 0) if k == n else ((a, k) if k < n else (b, w-k))
    def canonical_face(t, f, v):
        e = prepared['tetrahedra'][t][f]
        if e is None: return t, f, v, None
        u, p = e['tetrahedron'], e['permutation']; g = p[f]
        return (t, f, v, None) if (t, f) < (u, g) else (u, g, p[v] if v >= 0 else -1, p)

    core2 = []
    for root, wedges in links.items():
        w = analysed['weights'][root]
        for rank in ([0] if w == 0 else [0, w]):
            cycle = []
            for s in wedges:
                t, (a, b), f = s['tetrahedron'], s['edge'], s['exit_face']
                point = edge_chamber(t, a, b, rank)
                v, r = face_region(t, f, a, b, rank); tt, ff, vv, _ = canonical_face(t, f, v)
                if point not in by_chamber or r != 0: raise ArithmeticError('core edge gap touches parallel handles')
                cycle.extend([dict(dimension=0, handle=by_chamber[point], tetrahedron=t, local_edge=[a, b]),
                              dict(dimension=1, handle=core_face[tt, ff, vv], tetrahedron=t, face=f, corner=v)])
            core2.append(dict(id=len(core2), edge=root, rank=rank, cycle=cycle))
    boundary_vertices = {prepared['vertex_roots'][4*t+v] for t, f in prepared['boundary_faces'] for v in range(4) if v != f}
    groups = {}
    for t in range(len(rows)):
        for v in range(4): groups.setdefault(prepared['vertex_roots'][4*t+v], []).append([t, v])
    core3 = [dict(id=i, vertex=root, link_triangles=group) for i, (root, group) in enumerate(
        (item for item in sorted(groups.items()) if item[0] not in boundary_vertices))]

    polygons = []; p0 = {}; p1 = {}; p2 = {}; point_size = 0
    for t, row in enumerate(rows):
        for col, count in enumerate(row):
            if count > 1:
                index = len(polygons); p0[t, col] = index
                polygons.append(dict(id=index, kind='prism', tetrahedron=t, column=col, start=point_size,
                                     stop=point_size+count-1, rank_start=1, rank_stop=count))
                point_size += count-1
    temp = [dict(kind='horizontal', tetrahedron=p['tetrahedron'], column=p['column'], side=0) for p in polygons]
    _cycle_recipes(prepared, rows, temp, check)
    for polygon, original in zip(polygons, temp):
        t, col = polygon['tetrahedron'], polygon['column']; arcs = original['cycle']; vertices = []; edges = []
        for i, arc in enumerate(arcs):
            f, v = arc['face'], arc['corner']; others = [x for x in range(4) if x not in (f, v)]
            if not arc['forward']: others.reverse()
            first, last = [sorted((v, u)) for u in others]
            s, offset = arc['rank']
            if col >= 4 and v not in (0, col-3): offset += 1
            vertices.extend([dict(edge=first, face=f), dict(edge=last, face=f)])
            edges.append(dict(kind='face', face=f, corner=v, rank=[s, offset]))
            root = prepared['edge_roots'][_edge(t, *last)]
            a, b = (col, next(x for x in last if x != col)) if col < 4 else (
                next(x for x in last if x in (0, col-3)), next(x for x in last if x not in (0, col-3)))
            reverse = prepared['edge_orientations'][_edge(t, a, b)] ^ int(a > b)
            offset = 0 if col < 4 else rows[t][a]
            edges.append(dict(kind='corner', edge=last, root=root, rank=[-1, analysed['weights'][root]-offset] if reverse else [1, offset]))
        polygon.update(vertices=vertices, edges=edges)
    for t, f, u, g, perm in prepared['pairs']:
        for v in (x for x in range(4) if x != f):
            count = rows[t][v]+rows[t][4+_quad(f, v)]
            if count < 2: continue
            others = [x for x in range(4) if x not in (f, v)]; index = len(polygons); p1[t, f, v] = index
            polygons.append(dict(id=index, kind='face_strip', tetrahedron=t, face=f, corner=v,
                target_tetrahedron=u, target_face=g, permutation=list(perm), start=point_size, stop=point_size+count-1,
                rank_start=1, rank_stop=count, vertices=[dict(end=end, branch=branch) for end, branch in ((0,0),(1,0),(1,1),(0,1))],
                edges=[dict(kind='side', branch=0, edge=sorted((v,others[0]))), dict(kind='end', end=1),
                       dict(kind='side', branch=1, edge=sorted((v,others[1]))), dict(kind='end', end=0)]))
            point_size += count-1
    for root, wedges in links.items():
        w = analysed['weights'][root]
        if w < 2: continue
        index = len(polygons); p2[root] = index; vertices = []; edges = []
        for s in wedges:
            t, e, entry, exit = s['tetrahedron'], s['edge'], s['entry_face'], s['exit_face']
            vertices.extend([dict(tetrahedron=t, edge=e, face=entry), dict(tetrahedron=t, edge=e, face=exit)])
            edges.append(dict(kind='tetrahedron_sector', tetrahedron=t, edge=e))
            tt, ff, _, transform = canonical_face(t, exit, -1)
            ce = e if transform is None else sorted(transform[a] for a in e)
            edges.append(dict(kind='face_sector', tetrahedron=tt, face=ff, edge=ce))
        polygons.append(dict(id=index, kind='edge_cap', edge=root, start=point_size, stop=point_size+w-1,
                             rank_start=1, rank_stop=w, vertices=vertices, edges=edges)); point_size += w-1

    gluings = []
    def glue(left, slot, right, target_slot, lo, hi, a, b, ends_reverse, fibre_flip):
        check()
        gluings.append(dict(left=left, left_edge=slot, right=right, right_edge=target_slot,
                             rank_start=lo, rank_stop=hi, left_map=list(a), right_map=list(b),
                             ends_reverse=bool(ends_reverse), fibre_flip=bool(fibre_flip)))
    for polygon in polygons:
        check(); kind = polygon['kind']; index = polygon['id']; start = polygon['start']; lo, hi = polygon['rank_start'], polygon['rank_stop']
        if kind == 'prism':
            t, col = polygon['tetrahedron'], polygon['column']
            for slot, e in enumerate(polygon['edges']):
                first = polygon['vertices'][slot]
                if e['kind'] == 'face':
                    f, v = e['face'], e['corner']; entry = prepared['tetrahedra'][t][f]
                    if entry is None: continue
                    tt, ff, vv, transform = canonical_face(t, f, v); target = p1[tt, ff, vv]; q = polygons[target]
                    end = 0 if transform is None else 1; target_slot = 3 if end == 0 else 1
                    other = next(x for x in first['edge'] if x != v)
                    if transform is not None: other = transform[other]
                    branch = [x for x in range(4) if x not in (ff, vv)].index(other)
                    target_first = q['vertices'][target_slot]
                    s, o = e['rank']
                    glue(index, slot, target, target_slot, lo, hi, (1,start-1), (s,q['start']+o-1),
                         target_first != dict(end=end,branch=branch), col >= 4 and v not in (0,col-3))
                else:
                    root = e['root']
                    if root in prepared['boundary_incidence']: continue
                    target = p2[root]; q = polygons[target]
                    target_slot = next(i for i,r in enumerate(q['edges']) if r['kind']=='tetrahedron_sector' and r['tetrahedron']==t and r['edge']==e['edge'])
                    s, o = e['rank']
                    glue(index,slot,target,target_slot,lo,hi,(1,start-1),(s,q['start']+o-1),
                         q['vertices'][target_slot]['face'] != first['face'], s == -1)
        elif kind == 'face_strip':
            t, f, v = polygon['tetrahedron'], polygon['face'], polygon['corner']
            for slot in (0,2):
                e = polygon['edges'][slot]; a,b=e['edge']; root=prepared['edge_roots'][_edge(t,a,b)]
                if root in prepared['boundary_incidence']: continue
                target=p2[root];q=polygons[target]
                target_slot=next(i for i,r in enumerate(q['edges']) if r['kind']=='face_sector' and r['tetrahedron']==t and r['face']==f and r['edge']==e['edge'])
                u=next(x for x in e['edge'] if x!=v);reverse=prepared['edge_orientations'][_edge(t,v,u)] ^ int(v>u)
                s,o=(-1,analysed['weights'][root]) if reverse else (1,0)
                first=polygon['vertices'][slot]; wanted=t if first['end']==0 else polygon['target_tetrahedron']
                wanted_face=f if first['end']==0 else polygon['target_face']
                # Same-tetrahedron self-gluings still have distinct face flags.
                cap_first=q['vertices'][target_slot]
                flip=not(cap_first['tetrahedron']==wanted and cap_first['face']==wanted_face)
                glue(index,slot,target,target_slot,lo,hi,(1,start-1),(s,q['start']+o-1),flip,reverse)

    covered = {(p['id'],i):[] for p in polygons for i in range(len(p['edges']))}
    for g in gluings:
        for side in ('left','right'):
            p=polygons[g[side]];s,o=g[side+'_map'];a=s*g['rank_start']+o;b=s*(g['rank_stop']-1)+o
            covered[g[side],g[side+'_edge']].append((min(a,b)-p['start']+1,max(a,b)-p['start']+2))
    free=[];ports=[]
    for p in polygons:
        t=p.get('tetrahedron');lo,hi=p['rank_start'],p['rank_stop']
        for slot,e in enumerate(p['edges']):
            cursor=lo; gaps=[]
            for a,b in sorted(covered[p['id'],slot]):
                if a<cursor:raise ArithmeticError('parallelity edge glued more than once')
                if cursor<a:gaps.append((cursor,a))
                cursor=b
            if cursor<hi:gaps.append((cursor,hi))
            if p['kind']=='edge_cap' and e['kind']=='tetrahedron_sector':
                u,(a,b)=e['tetrahedron'],e['edge'];w=analysed['weights'][p['edge']]
                crossing=sum(rows[u][4:])-rows[u][4+_quad(a,b)]
                ranks={rows[u][a],rows[u][a]+crossing}
                if prepared['edge_orientations'][_edge(u,a,b)]:ranks={w-r for r in ranks}
                split=[]
                for first,last in gaps:
                    points=sorted(r for r in ranks if first<=r<last)
                    if len(points)!=last-first:raise ArithmeticError('unowned edge-cap core span')
                    split.extend((r,r+1)for r in points)
                gaps=split
            for first,last in gaps:
                check();boundary=False;core_dimension=None;core_handle=None
                if p['kind']=='prism':
                    boundary=(prepared['tetrahedra'][t][e['face']] is None if e['kind']=='face' else e['root'] in prepared['boundary_incidence'])
                elif p['kind']=='face_strip':
                    if e['kind']=='side':boundary=prepared['edge_roots'][_edge(t,*e['edge'])] in prepared['boundary_incidence']
                    else:
                        u,f,v=(t,p['face'],p['corner']) if e['end']==0 else (p['target_tetrahedron'],p['target_face'],p['permutation'][p['corner']])
                        core_dimension=0;core_handle=by_chamber[chamber_face(u,f,v,first)]
                else:
                    root=p['edge']
                    if e['kind']=='tetrahedron_sector':
                        core_dimension=0;core_handle=by_chamber[edge_chamber(e['tetrahedron'],*e['edge'],first)]
                    else:
                        u,f=e['tetrahedron'],e['face'];v,r=face_region(u,f,*e['edge'],first)
                        if v!=-1:raise ArithmeticError('free edge-cap face sector is not central')
                        core_dimension=1;core_handle=core_face[u,f,-1]
                if not boundary and(core_dimension is None or last-first!=1):raise ArithmeticError('unbounded or unowned core interface')
                record=dict(polygon=p['id'],edge=slot,rank_start=first,rank_stop=last,original_boundary=boundary)
                if not boundary:
                    port=len(ports);ports.append(dict(id=port,polygon=p['id'],edge=slot,rank=first,
                        core_dimension=core_dimension,core_handle=core_handle));record['port']=port
                free.append(record)
    if len(core0)>6*len(rows) or len(core1)>8*len(rows) or len(core2)>12*len(rows) or len(core3)>4*len(rows) or len(ports)>66*len(rows):
        raise ArithmeticError('parallelity/core family bound failed')
    corner_size=0
    for p in polygons:
        count=p['stop']-p['start'];p['corner_starts']=[]
        for v in p['vertices']:p['corner_starts'].append(corner_size);corner_size+=count
    return dict(polygon_points=point_size,corner_points=corner_size,polygons=polygons,gluings=gluings,
                free_edges=free,ports=ports,core=dict(handles0=core0,handles1=core1,handles2=core2,handles3=core3),
                source={'tetrahedra':[[None if r is None else dict(tetrahedron=r['tetrahedron'],permutation=r['permutation'].copy())
                                       for r in tet]for tet in prepared['tetrahedra']]},coordinates=[r.copy()for r in rows])
