#!/usr/bin/env python3
"""Finite local/annular certificate used by validate.py.

No assert statements and no external sources. The universal extension to an
arbitrary old dissection and injectivity on rooted maps are proved in the
report; this module checks their explicit finite building block.
"""
from itertools import combinations, permutations


def schema(s,keys,array,integer,require):
    keys(s,'old_boundary_colors old_boundary_edge_colors radial_colors new_boundary_labels new_root_index new_boundary_order recovered_old_root_position annulus_edges new_faces size_delta comparison_shift comparison_start','sleeve')
    for k in ['old_boundary_colors','old_boundary_edge_colors','radial_colors','new_boundary_labels']:
        array(s[k],6,'sleeve.'+k)
        require(all(type(x) is str and x in ('R','G','B') for x in s[k]),'schema.sleeve_color',k)
    for k in ['new_root_index','recovered_old_root_position']:integer(s[k],'sleeve.'+k,0,5)
    for k in ['comparison_shift','comparison_start']:integer(s[k],'sleeve.'+k,0,100)
    for k,n in [('new_boundary_order',6),('size_delta',3)]:
        array(s[k],n,'sleeve.'+k)
        for x in s[k]:integer(x,'sleeve.'+k,0,100)
    for k,n,width in [('annulus_edges',18,2),('new_faces',6,4)]:
        array(s[k],n,'sleeve.'+k)
        for entry in s[k]:
            array(entry,width,'sleeve.'+k)
            for x in entry:integer(x,'sleeve.'+k,0,11)


def cyclic_reduce(colors):
    reduced=[]
    for x in colors:
        if not reduced or x!=reduced[-1]:reduced.append(x)
    if len(reduced)>1 and reduced[0]==reduced[-1]:reduced.pop()
    return tuple(reduced)


def verify(s,require):
    canonical=['R','G','B']*2
    require(s['old_boundary_colors']==canonical,'sleeve.old_boundary_labels')
    valid={('R','G','B'),('G','B','R'),('B','R','G')}
    for i in range(6):
        # All old inner edges have the same color by old SL1. A contiguous
        # nonempty block reduces to one symbol, so k=0 and k=1 exhaust all k.
        for k in [0,1]:
            colors=[s['old_boundary_edge_colors'][(i-1)%6]]+[canonical[i]]*k+[s['old_boundary_edge_colors'][i],s['radial_colors'][i]]
            require(cyclic_reduce(colors) in valid,'sleeve.local_SL2',f'vertex {i}, zero/positive case {k}')
    require(s['radial_colors']==s['new_boundary_labels'],'sleeve.outer_SL1')
    root=s['new_root_index'];order=s['new_boundary_order']
    require(order==[(root+i)%6 for i in range(6)],'sleeve.boundary_order')
    require(root%2==1 and [i%2 for i in order]==[1,0,1,0,1,0],'sleeve.root_bipartition')
    require([s['new_boundary_labels'][i] for i in order]==canonical,'sleeve.canonical_new_labels')
    edges={tuple(sorted(e)) for e in s['annulus_edges']}
    require(len(edges)==18 and all(a!=b for a,b in edges),'sleeve.simple_annulus')
    expected={tuple(sorted((i,(i+1)%6))) for i in range(6)}|{tuple(sorted((6+i,6+(i+1)%6))) for i in range(6)}|{(i,6+i) for i in range(6)}
    require(edges==expected,'sleeve.annulus_edges')
    white=lambda i:(i%2==0 if i<6 else (i-6)%2==1)
    require(all(white(a)!=white(b) for a,b in edges),'sleeve.bipartition')
    for face in s['new_faces']:
        require(len(set(face))==4 and all(tuple(sorted((face[j],face[(j+1)%4]))) in edges for j in range(4)),'sleeve.face_edges')
    cycles=set()
    for verts in combinations(range(12),4):
        for rest in permutations(verts[1:]):
            cyc=(verts[0],)+rest
            if cyc[1]>cyc[-1]:continue
            if all(tuple(sorted((cyc[j],cyc[(j+1)%4]))) in edges for j in range(4)):cycles.add(frozenset(cyc))
    faces={frozenset(face) for face in s['new_faces']}
    require(len(cycles)==6 and cycles==faces,'sleeve.four_cycles')
    recovered=[]
    for i in order:
        old_neighbors=[j for j in range(6) if (j,6+i) in edges]
        require(len(old_neighbors)==1,'sleeve.unique_inner_neighbor')
        recovered.append(old_neighbors[0])
    pos=s['recovered_old_root_position']
    require(recovered[pos]==0,'sleeve.root_recovery')
    require(recovered[pos:]+recovered[:pos]==list(range(6)),'sleeve.boundary_recovery')
    deleted={edge for edge in edges if all(v<6 for v in edge)}
    require(deleted=={tuple(sorted((i,(i+1)%6))) for i in range(6)},'sleeve.inverse_deletion')
    delta=[6,len(edges)-6,len(faces)]
    require(s['size_delta']==delta and delta[0]-delta[1]+delta[2]==0,'sleeve.euler_size')
    require(s['comparison_shift']==delta[2],'sleeve.comparison_shift')
    require(s['comparison_start']==8,'sleeve.comparison_start')
    return {'local_degree_cases':'k=0 and arbitrary k>=1 via contiguous-block reduction','annular_vertices':12,'annular_edges':18,'four_cycles':6,'all_four_cycles_are_faces':True,'size_delta_vertices_edges_inner_faces':delta,'old_root_recovered_at_output_boundary_position':pos,'comparison_shift':s['comparison_shift'],'scope':'finite sleeve data and symbolic local rule; general surgery/injectivity proof is in report'}
