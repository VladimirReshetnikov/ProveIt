#!/usr/bin/env python3
"""Match opposite monomial occurrences before building a graph energy."""
from collections import Counter, defaultdict
from copy import deepcopy
import importlib.util
from pathlib import Path
_spec=importlib.util.spec_from_file_location('inherited_graph127',Path(__file__).parent/'source127'/'graph'/'build.py')
_upstream=importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_upstream)
normalize,orient=_upstream.normalize,_upstream.orient


def compile_paired(source,hubs=32,match=True):
    norm=normalize(source)
    bymon=defaultdict(lambda:[[],[]])
    for r,row in enumerate(norm['rows']):
        for j,(c,m) in enumerate(row['terms']):
            bymon[tuple(sorted(m))][c>0].append((r,j))
    paired=[];covered=set();used_row_pairs=set()
    if match:
        # Largest repeated monomial classes first; all tie breaks are explicit.
        for mon,sides in sorted(bymon.items(),key=lambda kv:(-min(map(len,kv[1])),len(kv[0]),kv[0])):
            negatives,positives=sides
            for plus in positives:
                for minus in negatives:
                    key=tuple(sorted((plus[0],minus[0])))
                    if minus in covered or plus[0]==minus[0] or key in used_row_pairs:continue
                    paired.append((plus,minus,mon));covered.update((plus,minus));used_row_pairs.add(key);break
    unpaired=[];perrow=defaultdict(list)
    for r,row in enumerate(norm['rows']):
        for j,(c,m) in enumerate(row['terms']):
            if (r,j) not in covered:
                perrow[r].append(len(unpaired));unpaired.append((r,j,c,tuple(sorted(m))))
    logical=[]
    for p,n,m in paired:logical.append({'occurrences':[[p[0],p[1]],[n[0],n[1]]],'sign':1,'mon':list(m),'paired':True})
    for r,j,c,m in unpaired:logical.append({'occurrences':[[r,j]],'sign':c,'mon':list(m),'paired':False})
    fake={'variables':norm['variables'],'rows':[{'terms':[[e['sign'],e['mon']]]} for e in logical]}
    _,orientations=orient(fake,True)
    variables=[];groups=defaultdict(list);units=[];products=[]
    def fresh(kind,**kw):
        v=len(variables);variables.append({'kind':kind,**kw});return v
    common={}
    for v in sorted({b for a,b in orientations if b is not None and a!=b}):
        w=fresh('shared',normalized_variable=v);common[v]=w;groups[v].append(w)
    unit=fresh('unit_shared');units.append(unit)
    for e,(a,b) in zip(logical,orientations):
        private=fresh('private',normalized_variable=a,occurrences=e['occurrences'])
        (units if a is None else groups[a]).append(private)
        other=private if a is not None and a==b else (unit if b is None else common[b])
        products.append({'occurrences':e['occurrences'],'sign':e['sign'],'factors':[private,other],
                         'logical_factors':[a,b]})
    vertices=[{'kind':'hub','index':i} for i in range(hubs)];blocks=[];edges=[]
    for r in range(len(norm['rows'])):
        count=max(1,(len(perrow[r])+hubs-1)//hubs)
        block=list(range(len(vertices),len(vertices)+count));blocks.append(block)
        vertices.extend({'kind':'row','row':r,'part':i} for i in range(count))
    for i,(plus,minus,mon) in enumerate(paired):
        edges.append({'kind':'prescribed','tail':blocks[plus[0]][0],'head':blocks[minus[0]][0],
                      'coefficient':1,'monomial':products[i]['factors'],'product':i,
                      'occurrences':products[i]['occurrences']})
    local=Counter()
    for j,(r,occ,c,m) in enumerate(unpaired):
        i=len(paired)+j;k=local[r];local[r]+=1
        edges.append({'kind':'prescribed','tail':blocks[r][k//hubs],'head':j%hubs,
                      'coefficient':c,'monomial':products[i]['factors'],'product':i,
                      'occurrences':[[r,occ]]})
    for r,block in enumerate(blocks):
        for a,b in zip(block,block[1:]):
            w=fresh('flow',component='row',row=r,edge=len(edges))
            edges.append({'kind':'free','tail':a,'head':b,'coefficient':1,'monomial':[w]})
    for a in range(hubs-1):
        w=fresh('flow',component='hub',edge=len(edges))
        edges.append({'kind':'free','tail':a,'head':a+1,'coefficient':1,'monomial':[w]})
    pairs=set();incident=[[] for _ in vertices];pol=Counter()
    for e in edges:
        pair=tuple(sorted((e['tail'],e['head'])))
        if pair[0]==pair[1] or pair in pairs:raise ValueError('Graph must initially be simple')
        pairs.add(pair);c=e['coefficient'];m=tuple(sorted(e['monomial']))
        pol[tuple(sorted(m+m))]+=c*c
        incident[e['tail']].append((c,m));incident[e['head']].append((-c,m))
    for row in incident:
        for i,(c,m) in enumerate(row):
            for d,n in row[i+1:]:pol[tuple(sorted(m+n))]+=c*d
    cycles=[]
    for v,aliases in sorted(groups.items()):
        if len(aliases)==2:aliases.append(fresh('equality_dummy',normalized_variable=v))
        if len(aliases)>1:
            for a in aliases:pol[(a,a)]+=1
            for a,b in zip(aliases,aliases[1:]+aliases[:1]):pol[tuple(sorted((a,b)))]-=1
        cycles.append({'normalized_variable':v,'aliases':aliases})
    while len(units)<2:units.append(fresh('unit_dummy'))
    pol[()]+=1
    for a in units:pol[(a,a)]+=1
    for a,b in zip(units,units[1:]):pol[tuple(sorted((a,b)))]-=1
    pol[(units[0],)]-=1;pol[(units[-1],)]-=1
    pol={m:c for m,c in pol.items() if c}
    if any(abs(c)!=1 for c in pol.values()):raise ValueError('Initial height-one failure')
    met={'variables':len(variables),'degree':max(map(len,pol)),'monomials':len(pol),'coefficient_height':1,
         'paired_occurrences':len(paired),'source_occurrences':sum(len(r['terms']) for r in norm['rows']),
         'source_variables':len(source['variables']),'hubs':hubs}
    artifact={'schema':'paired-graph-height-one-v1','domain':'unrestricted integers','variables':variables,
              'terms':[[pol[m],list(m)] for m in sorted(pol,key=lambda m:(len(m),m))],'metrics':met}
    cert={'schema':'paired-graph-certificate-v1','normalization':norm,'vertices':vertices,'edges':edges,
          'products':products,'row_blocks':blocks,'hub_vertices':list(range(hubs)),
          'equality_cycles':cycles,'unit_path':units,'pairing':{'matched':len(paired),'covered_occurrences':len(covered),
            'source_occurrences':met['source_occurrences']}}
    return artifact,cert
