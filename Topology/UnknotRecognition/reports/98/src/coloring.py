"""Equivariant coloring recipes: one symbolic DAG, not one per root assignment.

An expression [i,b] means input component-root bit i XOR b. [-1,b] is
constant b. A recipe describes an actual graph coloring for EVERY choice
of its visible root bits. All hidden choices are fixed by a four-state DP.
"""
from __future__ import annotations
from gauge_cuts import ParityDSU,groups,flip,decode_row,encode_row

def select_hidden(start:int, tags:list[int], target:int) -> list[int]:
    paths={start:[]}
    for tag in tags:
        nxt={}
        for old,path in sorted(paths.items()):
            for bit in (0,1): nxt.setdefault(old|flip(tag,bit),path+[bit])
        paths=nxt
    if target not in paths: raise ValueError('infeasible hidden gauge assignment')
    return paths[target]

def build_recipe(packet:dict, root_row:int) -> dict:
    nodes=packet['grammar']['nodes'];tabs=packet['atlases'];wanted={(len(nodes)-1,root_row)}
    todo=list(wanted)
    for i,ri in todo:
        z=nodes[i];origin=tabs[i]['origins'][ri]
        if z['op']!='leaf':
            for j,rj in zip(z['children'],origin['child_rows']):
                if (j,rj) not in wanted:wanted.add((j,rj));todo.append((j,rj))
    records=[];ids={}
    for i,ri in sorted(wanted):
        z=nodes[i];row=decode_row(tabs[i]['rows'][ri]);origin=tabs[i]['origins'][ri]
        rec={'node':i,'row':encode_row(row)}
        if z['op']=='leaf':
            n=len(z['vertices']);uf=ParityDSU(n);cut=set(origin['cut_edges'])
            for j,(u,v,_) in enumerate(z['edges']):
                if not uf.union(u,v,int(j in cut)):raise ValueError('invalid leaf cut')
            coords=[uf.find(v) for v in range(n)];tags={r:0 for r,b in coords}
            for j,(u,v,_) in enumerate(z['edges']):
                if j not in cut:tags[coords[u][0]]|=1<<coords[u][1]
            active={}
            for t in z['terminals']:
                r,b=coords[t]
                if r not in active:active[r]=(len(active),b)
            hidden=[r for r in tags if r not in active]
            orientations=dict(zip(hidden,select_hidden(0,[tags[r] for r in hidden],row[3])))
            rec['colors']=[[active[r][0],b^active[r][1]] if r in active else [-1,b^orientations[r]] for r,b in coords]
        else:
            child_rows=[decode_row(tabs[j]['rows'][rj]) for j,rj in zip(z['children'],origin['child_rows'])]
            ms=[tabs[j]['metadata'] for j in z['children']];q=len(set(v for mp in z['maps'] for v in mp));uf=ParityDSU(q)
            for cr,m,mp in zip(child_rows,ms,z['maps']):
                for grp in groups(m['part']):
                    for j in grp:
                        if not uf.union(mp[grp[0]],mp[j],(cr[1]>>j)&1):raise ValueError('inconsistent quotient')
            coords=[uf.find(v) for v in range(q)];marks={r:0 for r,b in coords};fixed=0
            for cr,m,mp in zip(child_rows,ms,z['maps']):
                fixed|=cr[3]
                for c,grp in enumerate(groups(m['part'])):
                    r,b=coords[mp[grp[0]]];marks[r]|=flip(cr[2][c],b)
            active={}
            for t in z['keep']:
                r,b=coords[t]
                if r not in active:active[r]=(len(active),b)
            hidden=[r for r in marks if r not in active]
            orientations=dict(zip(hidden,select_hidden(fixed,[marks[r] for r in hidden],row[3])))
            transports=[]
            for cr,m,mp in zip(child_rows,ms,z['maps']):
                trs=[]
                for grp in groups(m['part']):
                    r,b=coords[mp[grp[0]]]
                    trs.append([active[r][0],b^active[r][1]] if r in active else [-1,b^orientations[r]])
                transports.append(trs)
            rec['children']=[ids[(j,rj)] for j,rj in zip(z['children'],origin['child_rows'])]
            rec['transports']=transports
        ids[(i,ri)]=len(records);records.append(rec)
    return {'schema':'component-gauge-coloring-v1','grammar':packet['grammar'],'records':records,
            'root':ids[(len(nodes)-1,root_row)]}

def color_at(recipe:dict,path:list[int],leaf_vertex:int,root_bits:list[int] | None=None) -> int:
    """Random access by a grammar occurrence address; never expands siblings."""
    records=recipe['records']; rec=records[recipe['root']]
    count=len(rec['row'][2])
    if root_bits is None:root_bits=[0]*count
    if len(root_bits)!=count or any(type(b) is not int or b not in (0,1) for b in root_bits):raise ValueError('bad root bits')
    bits=root_bits
    for branch in path:
        if 'children' not in rec or type(branch) is not int or not 0<=branch<len(rec['children']):raise ValueError('bad occurrence path')
        bits=[offset if var<0 else bits[var]^offset for var,offset in rec['transports'][branch]]
        rec=records[rec['children'][branch]]
    if 'colors' not in rec or type(leaf_vertex) is not int or not 0<=leaf_vertex<len(rec['colors']):raise ValueError('not a leaf vertex')
    var,offset=rec['colors'][leaf_vertex]
    return offset if var<0 else bits[var]^offset

def mark_address(recipe:dict,color:int,root_bits:list[int] | None=None) -> dict:
    """One original grammar-edge occurrence witnessing a present color flag."""
    if type(color) is not int or color not in (0,1):raise ValueError('invalid mark color')
    records=recipe['records'];rec=records[recipe['root']]
    if root_bits is None:root_bits=[0]*len(rec['row'][2])
    if len(root_bits)!=len(rec['row'][2]) or any(type(b) is not int or b not in (0,1) for b in root_bits):raise ValueError('bad root bits')
    def flags(row,bits):
        ans=row[3]
        for tag,b in zip(row[2],bits):ans|=flip(tag,b)
        return ans
    if not flags(rec['row'],root_bits)&(1<<color):raise ValueError('requested mark is absent')
    bits=root_bits;path=[]
    while 'children' in rec:
        found=False
        for branch,child in enumerate(rec['children']):
            cb=[offset if var<0 else bits[var]^offset for var,offset in rec['transports'][branch]]
            cr=records[child]
            if flags(cr['row'],cb)&(1<<color):
                path.append(branch);rec=cr;bits=cb;found=True;break
        if not found:raise ValueError('invalid coloring recipe')
    z=recipe['grammar']['nodes'][rec['node']]
    def value(v):
        var,b=rec['colors'][v];return b if var<0 else bits[var]^b
    for j,(u,v,c) in enumerate(z['edges']):
        if value(u)==value(v)==color:return {'path':path,'leaf_edge':j,'color':color}
    raise ValueError('invalid leaf mark')
