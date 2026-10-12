"""Descending unknot shadows containing a spanning m-by-m grid.

Every crossing order has a balanced-prefix frontier of at least m/3 edges.
This is a width obstruction, NOT a running-time lower bound for recognition.
"""
from fastunknot.disk_frontier import diagram_graph


def descending_grid(m):
    if type(m) is not int or m<1:raise ValueError('m must be a positive integer')
    n=m*m;alpha=[None]*(4*n)
    dart=lambda i,j,d:4*(i*m+j)+d  # clockwise N,E,S,W
    def join(a,b):
        if alpha[a] is not None or alpha[b] is not None:raise ArithmeticError('dart used twice')
        alpha[a]=b;alpha[b]=a
    for i in range(m):
        for j in range(m):
            if i+1<m:join(dart(i,j,2),dart(i+1,j,0))
            if j+1<m:join(dart(i,j,1),dart(i,j+1,3))
    boundary=([dart(0,j,0) for j in range(m)] + [dart(i,m-1,1) for i in range(m)] +
              [dart(m-1,j,2) for j in range(m-1,-1,-1)] + [dart(i,0,3) for i in range(m-1,-1,-1)])
    # Initial straight-through paths are vertical columns and horizontal rows.
    strand={d:(d//4)%m if d%2==0 else m+(d//4)//m for d in boundary}
    parent=list(range(2*m))
    def root(x):
        while parent[x]!=x:x=parent[x]
        return x
    outside=[]
    while len(boundary)>2:
        for k,a in enumerate(boundary):
            z=(k+1)%len(boundary);b=boundary[z]
            ra,rb=root(strand[a]),root(strand[b])
            if ra!=rb:
                join(a,b);outside.append((a,b));parent[ra]=rb
                boundary=[d for pos,d in enumerate(boundary) if pos not in (k,z)]
                break
        else:raise ArithmeticError('no adjacent distinct open paths')
    join(*boundary);outside.append(tuple(boundary))
    over={};d=0;visited=[]
    while not visited or d!=0:
        visited.append(d);v,j=divmod(d,4)
        over.setdefault(v,j%2)
        d=alpha[4*v+(j+2)%4]
        if len(visited)>2*n:raise ArithmeticError('shadow has more than one component')
    if len(visited)!=2*n:raise ArithmeticError('shadow did not merge to one component')
    label=[None]*(4*n);next_label=0
    for d in range(4*n):
        if label[d] is None:
            label[d]=label[alpha[d]]=next_label;next_label+=1
    pd=[]
    for v in range(n):
        row=tuple(label[4*v+j] for j in range(4))
        k=over[v];pd.append(row[k:]+row[:k])
    diagram_graph(pd);verify_descending(pd)
    return pd


def verify_descending(pd):
    diagram_graph(pd)
    occurrences={}
    for v,c in enumerate(pd):
        for j,label in enumerate(c):occurrences.setdefault(label,[]).append(4*v+j)
    alpha={a:b for ds in occurrences.values() for a,b in (ds,ds[::-1])}
    if not pd:raise ValueError('empty diagram has no descending certificate')
    n=len(pd);visits=[];seen={};d=0
    while not visits or d!=0:
        v,j=divmod(d,4)
        count=seen.get(v,0)
        if count>1 or j%2!=count:raise ValueError('not descending from the designated basepoint')
        seen[v]=count+1;visits.append(dict(vertex=v,incoming_slot=j,first=count==0))
        d=alpha[4*v+(j+2)%4]
        if len(visits)>2*n:raise ValueError('bad traversal')
    if len(visits)!=2*n or any(c!=2 for c in seen.values()):raise ValueError('diagram is not one component')
    return visits
