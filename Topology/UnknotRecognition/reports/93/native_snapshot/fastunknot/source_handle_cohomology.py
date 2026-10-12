"""Transport a residual cocore class and certify a nonzero boundary period."""
from collections import deque
from .normal_surface_geometry import _EDGES


def _boundary_witness(prepared, handles, moves, active_faces, target, check):
    values=[0]*len(handles['one_handles']);values[target]=1;edges={e['id']:e for e in handles['two_handles']}
    for move in reversed(moves):
        check()
        if move['kind']!='cancel_12':continue
        face=move['one_handle'];total=0;coefficient=0
        for row in edges[move['two_handle']]['attaching_cycle']:
            sign=1 if row['forward']else -1
            if row['one_handle']==face:coefficient+=sign
            else:total+=sign*values[row['one_handle']]
        if abs(coefficient)!=1:raise ArithmeticError('nonunit geometric pivot')
        values[face]=-coefficient*total
    for edge in handles['two_handles']:
        check()
        if sum((1 if row['forward']else -1)*values[row['one_handle']]for row in edge['attaching_cycle']):
            raise ArithmeticError('transported cocore fails a source edge equation')
    n=len(prepared['tetrahedra']);adj=[[]for _ in range(4*n)]
    for face in handles['one_handles']:
        t,u,f,p=face['tetrahedron'],face['target_tetrahedron'],face['face'],face['permutation'];value=values[face['id']]
        for v in range(4):
            if v==f:continue
            a,b=4*t+v,4*u+p[v];adj[a].append((b,value));adj[b].append((a,-value))
    potential=[None]*(4*n)
    for start in range(4*n):
        if potential[start]is not None:continue
        potential[start]=0;queue=deque([start])
        while queue:
            check();a=queue.popleft()
            for b,delta in adj[a]:
                value=potential[a]+delta
                if potential[b]is None:potential[b]=value;queue.append(b)
                elif potential[b]!=value:raise ArithmeticError('source vertex potential has monodromy')
    graph={};edge_values={}
    for edge in sorted(prepared['boundary_incidence']):
        check();t,j=divmod(edge,6);a,b=_EDGES[j];left,right=prepared['vertex_roots'][4*t+a],prepared['vertex_roots'][4*t+b]
        value=potential[4*t+b]-potential[4*t+a];edge_values[edge]=value
        graph.setdefault(left,[]).append((right,edge,True,value));graph.setdefault(right,[]).append((left,edge,False,-value))
    first=min(graph);heights={first:0};tree={v:[]for v in graph};queue=deque([first]);closing=None
    while queue and closing is None:
        check();a=queue.popleft()
        for b,edge,forward,value in graph[a]:
            if b not in heights:
                heights[b]=heights[a]+value;queue.append(b);tree[a].append((b,edge,forward));tree[b].append((a,edge,not forward))
            elif heights[a]+value!=heights[b]:closing=(a,b,edge,forward);break
    if closing is None:return None
    a,b,edge,forward=closing;cycle=[dict(edge=edge,forward=forward)];previous={b:None};queue=deque([b])
    while a not in previous:
        check();v=queue.popleft()
        for w,e,f in tree[v]:
            if w not in previous:previous[w]=(v,e,f);queue.append(w)
    reverse=[];v=a
    while v!=b:
        u,e,f=previous[v];reverse.append(dict(edge=e,forward=f));v=u
    cycle+=list(reversed(reverse));period=sum((1 if row['forward']else -1)*edge_values[row['edge']]for row in cycle)
    if not period:raise ArithmeticError('boundary period vanished')
    return dict(dual_values=values,corner_potentials=[potential[4*t:4*t+4]for t in range(n)],boundary_cycle=cycle,period=period)
