#!/usr/bin/env python3
"""Recognize total linear transfer loops and their closed compositions."""
from collections import defaultdict
from functools import lru_cache
import grammar_layout as g

def identity():
    return tuple(tuple(int(i==j) for j in range(10)) for i in range(10))

def product(a,b):
    return tuple(tuple(sum(a[i][k]*b[k][j] for k in range(10)) for j in range(10)) for i in range(10))

def recognizer(nodes):
    bound=g.rot.edge_bounds(nodes)
    witnesses={}
    @lru_cache(None)
    def matrix(e):
        if e[0]=='I':
            a=list(map(list,identity()));a[e[1]][9]=1
            return tuple(map(tuple,a))
        if e[0]!='N' or bound(e)[1:]!=(0,0):return None
        left,right=nodes[e[1]]
        if bound(left)[1:]==bound(right)[1:]==(0,0):
            a,b=matrix(left),matrix(right)
            if a is None or b is None:return None
            witnesses[e[1]]=dict(kind='closed_composition',left=left,right=right)
            return product(b,a)
        if left[0]=='D':
            leaves=list(g.dt.leaves(g.dt.unfold(nodes,e[1])))
            if (leaves[0]==((0,),left)
                and all(z[0]=='I' and z[1]!=left[1] for p,z in leaves[1:-1])
                and leaves[-1][1][0]=='C'
                and leaves[-1][0]==(1,)*leaves[-1][1][1]):
                a=list(map(list,identity()));a[left[1]]=[0]*10
                increments=[0]*9
                for p,z in leaves[1:-1]:
                    a[z[1]][left[1]]+=1;increments[z[1]]+=1
                witnesses[e[1]]=dict(kind='primitive_transfer',source=left[1],
                    increment_vector=increments,leaves=leaves)
                return tuple(map(tuple,a))
        return None
    return matrix,witnesses

if __name__=='__main__':
    mat,witness=recognizer(g.original)
    known={i:mat(('N',i)) for i in g.original if mat(('N',i)) is not None}
    groups=defaultdict(list)
    for i,a in known.items():groups[a].append(i)
    print('known',len(known),'duplicate groups',[v for v in groups.values() if len(v)>1])
    print('known nodes',sorted(known))
