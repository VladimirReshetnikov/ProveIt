"""Independent exponential reduced Khovanov F_2 oracle for small braid closures.

This is an audit/reference fallback, not the maintained Bar-Natan scanner.
The reduced subcomplex fixes the label X on the marked resolution circle.
All gradings except cohomological cube height are suppressed; total rank is
unchanged. With one component, rank one detects the unknot. Caps raise a
resource exception, never a knot verdict. No saturation/source modules imported.
"""
from __future__ import annotations
from itertools import product

class CubeLimit(RuntimeError): pass

def _rank(columns):
    pivots={}
    for v in columns:
        while v:
            j=v.bit_length()-1
            if j in pivots: v^=pivots[j]
            else: pivots[j]=v; break
    return len(pivots)

def rank_braid(strands,braid,*,crossing_cap=10,generator_cap=300_000,check_square=True):
    if type(strands) is not int or strands<1 or not isinstance(braid,(tuple,list)): raise ValueError('invalid source')
    if any(type(c) is not int or not 0<abs(c)<strands for c in braid): raise ValueError('invalid crossing')
    n=len(braid)
    if strands>n+1: raise ValueError('too few crossings for a knot closure')
    if n>crossing_cap: raise CubeLimit('crossing cap')
    # Connectivity of the classical closure: independent from source frontend.
    positions=list(range(strands))
    for c in braid:
        i=abs(c)-1; positions[i],positions[i+1]=positions[i+1],positions[i]
    v=0; seen=set()
    while v not in seen: seen.add(v); v=positions[v]
    if len(seen)!=strands: raise ValueError('not a knot closure')
    states=[]; bases=[[] for _ in range(n+1)]; indices=[{} for _ in range(n+1)]
    allocated=0
    for mask in range(1<<n):
        size=(n+1)*strands; parent=list(range(size))
        def root(a):
            while parent[a]!=a: parent[a]=parent[parent[a]]; a=parent[a]
            return a
        def join(a,b):
            a,b=root(a),root(b)
            if a!=b: parent[a]=b
        for level,c in enumerate(braid):
            i=abs(c)-1; cap=((mask>>level)&1)==(1 if c>0 else 0)
            for j in range(strands):
                if j not in (i,i+1) or not cap: join(level*strands+j,(level+1)*strands+j)
            if cap:
                join(level*strands+i,level*strands+i+1)
                join((level+1)*strands+i,(level+1)*strands+i+1)
        for j in range(strands): join(j,n*strands+j)
        groups={}
        for node in range(size): groups.setdefault(root(node),[]).append(node)
        circles=sorted(tuple(g) for g in groups.values())
        lookup={node:i for i,g in enumerate(circles) for node in g}
        marked=lookup[0]; unmarked=[i for i in range(len(circles)) if i!=marked]
        count=1<<len(unmarked)
        allocated+=count
        if allocated>generator_cap: raise CubeLimit('generator cap')
        labels=[]
        for bits in range(count):
            label=1<<marked
            for j,k in enumerate(unmarked):
                if bits>>j&1: label|=1<<k
            labels.append(label)
        h=mask.bit_count()
        for label in labels:
            indices[h][(mask,label)]=len(bases[h]); bases[h].append((mask,label))
        states.append((circles,lookup,labels,marked))
    matrices=[[] for _ in range(n)]
    for h in range(n):
        for mask,label in bases[h]:
            old,oldmap,_,_=states[mask]; out=0
            for bit in range(n):
                if mask>>bit&1: continue
                target=mask|(1<<bit); new,newmap,_,_=states[target]
                # Circle incidence computed geometrically from common vertex sets.
                old_to_new=[{newmap[x] for x in c} for c in old]
                new_to_old=[{oldmap[x] for x in c} for c in new]
                local=[]
                if len(new)==len(old)-1:
                    merge=[j for j,s in enumerate(new_to_old) if len(s)==2]
                    if len(merge)!=1: raise AssertionError('invalid merge geometry')
                    z=merge[0]; a,b=sorted(new_to_old[z]); A=label>>a&1; B=label>>b&1
                    if A and B: continue
                    val=(A|B)<<z
                    for j,s in enumerate(new_to_old):
                        if j!=z: val|=((label>>next(iter(s)))&1)<<j
                    local=[val]
                elif len(new)==len(old)+1:
                    split=[j for j,s in enumerate(old_to_new) if len(s)==2]
                    if len(split)!=1: raise AssertionError('invalid split geometry')
                    z=split[0]; a,b=sorted(old_to_new[z]); val=0
                    for j,s in enumerate(old_to_new):
                        if j!=z: val|=((label>>j)&1)<<next(iter(s))
                    if label>>z&1: local=[val|(1<<a)|(1<<b)]
                    else: local=[val|(1<<a),val|(1<<b)]
                else: raise AssertionError('saddle not merge/split')
                for val in local:
                    key=(target,val)
                    if key not in indices[h+1]: raise AssertionError('reduced subcomplex not preserved')
                    out^=1<<indices[h+1][key]
            matrices[h].append(out)
    if check_square:
        for h in range(n-1):
            for col in matrices[h]:
                result=0
                while col:
                    bit=(col&-col).bit_length()-1; col&=col-1; result^=matrices[h+1][bit]
                if result: raise AssertionError('d squared is nonzero')
    ranks=[_rank(cols) for cols in matrices]
    total=allocated-2*sum(ranks)
    return {'rank':total,'generators':allocated,'chain_dimensions':[len(b) for b in bases],
            'differential_ranks':ranks,'square_checked':check_square}
