"""Independent small crossing cube, graph traversal and set elimination.

Adapted explicitly from vendor/reference_cube.py (prior report, MIT-0).
Unlike the scanner, it closes every resolution before applying m and Delta.
Returns unreduced, absolutely bigraded homology over F_2. Exponential audit only.
"""
from collections import defaultdict
from itertools import product


def cube(strands, word, max_crossings=12):
    if type(strands) is not int or strands<1 or any(type(x) is not int or not 0<abs(x)<strands for x in word):
        raise ValueError('invalid braid')
    n=len(word)
    if n>max_crossings: raise ValueError('independent cube limit exceeded')
    neg=sum(x<0 for x in word); vertices=(n+1)*strands
    circles={}; owner={}; basis={}; dims=defaultdict(int)
    for state in range(1<<n):
        adj=[set() for _ in range(vertices)]
        def edge(a,b): adj[a].add(b); adj[b].add(a)
        for j in range(strands): edge(j,n*strands+j)
        for k,letter in enumerate(word):
            e=bool((state>>k)&1)==(letter>0); i=abs(letter)-1
            for j in range(strands):
                if not e or j not in (i,i+1): edge(k*strands+j,(k+1)*strands+j)
            if e:
                edge(k*strands+i,k*strands+i+1)
                edge((k+1)*strands+i,(k+1)*strands+i+1)
        visited=set(); groups=[]
        for v in range(vertices):
            if v in visited: continue
            stack=[v]; group=set(); visited.add(v)
            while stack:
                w=stack.pop(); group.add(w)
                for z in adj[w]:
                    if z not in visited: visited.add(z); stack.append(z)
            groups.append(group)
        circles[state]=groups
        owner[state]={v:j for j,g in enumerate(groups) for v in g}
        for lab in product((0,1),repeat=len(groups)):
            h=state.bit_count()-neg
            q=state.bit_count()+n-3*neg+len(groups)-2*sum(lab)
            key=(h,q); basis[state,lab]=(key,dims[key]); dims[key]+=1
    cols={key:[set() for _ in range(d)] for key,d in dims.items()}
    for (state,lab),(key,index) in basis.items():
        for k in range(n):
            if state>>k&1: continue
            target=state|(1<<k); src=circles[state]; dst=circles[target]
            images=[{owner[target][v] for v in g} for g in src]
            outputs=[]
            if len(src)==len(dst)+1:
                out=[0]*len(dst)
                for j,image in enumerate(images):
                    assert len(image)==1
                    out[next(iter(image))]+=lab[j]
                if max(out)<2: outputs.append(tuple(out))
            elif len(src)+1==len(dst):
                j=next(j for j,image in enumerate(images) if len(image)==2)
                a,b=sorted(images[j]); part=[0]*len(dst)
                for z,image in enumerate(images):
                    if z!=j: part[next(iter(image))]=lab[z]
                for aa,bb in (((1,1),) if lab[j] else ((1,0),(0,1))):
                    out=part[:]; out[a],out[b]=aa,bb; outputs.append(tuple(out))
            else: raise ArithmeticError('non-saddle cube edge')
            for out in outputs:
                targetkey,ii=basis[target,out]
                assert targetkey==(key[0]+1,key[1])
                if ii in cols[key][index]: cols[key][index].remove(ii)
                else: cols[key][index].add(ii)
    for (h,q),cc in cols.items():
        for col in cc:
            result=set()
            for j in col: result.symmetric_difference_update(cols[h+1,q][j])
            assert not result, 'cube d squared nonzero'
    ranks={}
    for key,cc in cols.items():
        pivots={}
        for col in cc:
            col=set(col)
            while col:
                top=max(col)
                if top not in pivots: pivots[top]=col; break
                col.symmetric_difference_update(pivots[top])
        ranks[key]=len(pivots)
    result=[]
    for (h,q),d in sorted(dims.items()):
        b=d-ranks[h,q]-ranks.get((h-1,q),0)
        assert b>=0
        if b: result.append([h,q,b])
    return {'bigraded_homology':result,'basis':sum(dims.values()),'states':1<<n}
