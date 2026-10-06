"""Independent permutation-level map, geometry, and half-deletion checks.

No tableau formula is used to construct any object or map. F and J are
passed to the final comparison only. Exhaustive scope is explicitly finite.
"""
from collections import Counter, defaultdict
from itertools import combinations, permutations
from math import factorial


def need(condition,message):
    if not condition:
        raise ValueError(message)


def standardize(word):
    rank={v:i+1 for i,v in enumerate(sorted(word))}
    return tuple(rank[v] for v in word)


def inverse(word):
    result=[0]*len(word)
    for i,v in enumerate(word):
        result[v-1]=i+1
    return tuple(result)


def ranks(word):
    result=[]
    for i,v in enumerate(word):
        result.append(1+max((result[j] for j in range(i) if word[j]<v),default=0))
    return result


def skeleton(word):
    return tuple((i,word[i]) for i,r in enumerate(ranks(word)) if r<=2)


def occurrences(word,limit=2):
    result=[]
    for a,b,c,d in combinations(range(len(word)),4):
        if word[a]<word[b]<word[d]<word[c]:
            result.append((a,b,c,d))
            if len(result)>=limit:
                break
    return result


def swap(word,i,j):
    result=list(word)
    result[i],result[j]=result[j],result[i]
    return tuple(result)


def greedy_and_corners(word):
    """Called on a 1243 avoider: verify greedy, corner, and local tests."""
    rr=ranks(word)
    low=[i for i,r in enumerate(rr) if r<=2]
    high=[i for i,r in enumerate(rr) if r>=3]
    values=sorted(word[i] for i in high)
    remaining=set(values)
    marked=[]
    previous=0
    corners=[]
    tau=list(word)
    for i,v in zip(high,reversed(values)):
        tau[i]=v
    tau=tuple(tau)
    for index,i in enumerate(high):
        def supports(y,positions):
            return [(a,b) for a,b in combinations(positions,2)
                    if b<i and word[a]<word[b]<y]
        globally=[v for v in values if supports(v,low)]
        allowed=[v for v in globally if v in remaining]
        need(allowed and allowed[0]==word[i],"avoider is greedy")
        d=len(globally)
        need(len(allowed)==d-index,"deterministic board degree")
        greedy=len(allowed)>=2 and len(supports(allowed[0],range(i)))==1
        local=d>=index+2 and d>previous and len(supports(globally[0],low))==1
        need(greedy==local,"greedy/corner equivalence")
        if greedy:
            y,z=allowed[:2]
            marked.append((i,word.index(z)))
            a,b=supports(globally[0],low)[0]
            corner=(a,b,i,tau.index(globally[0]))
            corners.append(corner)
            # Check the stated finite-neighbor description independently.
            twos=[j for j in range(i) if rr[j]==2]
            ones=[j for j in range(b) if rr[j]==1]
            need(twos[-1]==b and ones[-1]==a,"latest low neighbors")
            need(word[b]<globally[0] and (len(twos)<2 or globally[0]<word[twos[-2]]),"rank-two corner neighbors")
            need(word[a]<word[b] and (len(ones)<2 or word[b]<word[ones[-2]]),"rank-one corner neighbors")
            need(index==0 or b>high[index-1],"new low point before corner")
        remaining.remove(word[i])
        previous=d
    need(max(ranks(tau),default=0)<=3,"West image avoids 1234")
    need(skeleton(tau)==skeleton(word),"West skeleton preservation")
    return marked,tau,corners


def half_delete(word,r):
    m=len(word)
    s=m-r-2
    need(s>=0 and word[-r:] == tuple(sorted(word[-r:],reverse=True)),"half suffix")
    need(word.index(2)==m-r-1,"half value 2 immediately before spine")
    y=word[-1]
    q=y-2
    need(1<=q<=s+1,"half q range")
    beta=standardize([v for i,v in enumerate(word) if v!=2 and i!=m-1])
    need(len(beta)==s+r,"deleted beta size")
    need(max(ranks(beta),default=0)<=3,"deleted beta avoids 1234")
    suffix=beta[-(r-1):]
    small=tuple(v for v in beta if v<=q)
    need(suffix==tuple(sorted(suffix,reverse=True)),"beta suffix decreases")
    need(small==tuple(range(q,0,-1)),"beta small values decrease")
    need(not (set(suffix)&set(small)),"beta disjointness")
    # Explicit inverse operations, with no knowledge of the original labels.
    restored=[v+int(v>=q+1) for v in beta]+[q+1]
    restored=[v+int(v>=2) for v in restored]
    restored.insert(len(restored)-r,2)
    need(tuple(restored)==word,"half deletion inverse")
    return q,beta


def unique_order(sequences,extra):
    vertices=set().union(*(set(s) for s in sequences))
    edges={v:set() for v in vertices}
    for seq in sequences:
        for a,b in zip(seq,seq[1:]):
            edges[a].add(b)
    for a,b in extra:
        edges[a].add(b)
    result=[]
    while vertices:
        incoming={b for a in vertices for b in edges[a] if b in vertices}
        free=vertices-incoming
        need(len(free)==1,"amalgamation must give a unique total order")
        v=free.pop()
        vertices.remove(v)
        result.append(v)
    return result


def glue(north,south_north,r):
    """Reconstruct from two standardized halves by forced order relations."""
    def labeled(word,offset,reverse_spine=False):
        labels=[]
        extra=[]
        start=len(word)-r
        for i,v in enumerate(word):
            if v==1:
                label=0
            elif v==2:
                label=1
            elif i>=start:
                j=i-start
                label=2+(r-1-j if reverse_spine else j)
            else:
                label=offset+i
                extra.append(label)
            labels.append(label)
        return labels,extra
    nl,N=labeled(north,100)
    sl,T=labeled(south_north,200,True)
    north_values=[nl[i] for i in sorted(range(len(north)),key=lambda i:north[i])]
    # Inversion swaps the two southern orderings.
    south_positions=[sl[i] for i in sorted(range(len(south_north)),key=lambda i:south_north[i])]
    position_order=unique_order((nl,south_positions),[(a,b) for a in N for b in T])
    value_order=unique_order((north_values,sl),[(b,a) for a in N for b in T])
    value={v:i+1 for i,v in enumerate(value_order)}
    word=tuple(value[v] for v in position_order)
    core_positions=tuple(position_order.index(v) for v in (0,1,2,r+1))
    return word,core_positions


NORTH={(0,2),(0,3),(0,4),(1,3),(1,4)}
SOUTH={(2,0),(3,0),(3,1),(4,0),(4,1)}


def geometry(word,mark):
    a,b,z,y=mark
    need(a<b<z<y and word[a]<word[b]<word[y]<word[z],"marked core")
    lowvalues=sorted(word[i] for i in mark)
    N,T,W=[],[],[z,y]
    for i,v in enumerate(word):
        if i in mark:
            continue
        cell=(sum(j<i for j in mark),sum(u<v for u in lowvalues))
        if cell in NORTH:
            N.append(i)
        elif cell in SOUTH:
            T.append(i)
        elif cell==(3,3):
            W.append(i)
        else:
            raise ValueError("point outside eleven shared-spine cells")
    W.sort()
    need(all(word[i]>word[j] for i,j in zip(W,W[1:])),"decreasing shared spine")
    r=len(W)
    k,s,t=r-2,len(N),len(T)
    need(s==b-1 and t==word[b]-2,"spine size shortcuts")
    need(k+s+t==len(word)-4,"size decomposition")
    support=[(i,j) for i,j in combinations(range(z),2) if word[i]<word[j]<word[y]]
    need(support==[(a,b)],"unique full southwest support")
    for special in ((0,2),(2,0)):
        members=[i for i in range(len(word)) if i not in mark and
                 (sum(j<i for j in mark),sum(u<word[i] for u in lowvalues))==special]
        need(all(word[i]>word[j] for i,j in zip(members,members[1:])),"decreasing boundary cell")
    north=standardize([word[i] for i in sorted(N+[a,b]+W)])
    south=standardize([word[i] for i in sorted(T+[a,b]+W)])
    south_north=inverse(south)
    nq,nbeta=half_delete(north,r)
    tq,tbeta=half_delete(south_north,r)
    rebuilt,remark=glue(north,south_north,r)
    need(rebuilt==word and remark==mark,"marked inverse amalgamation")
    return (k,s,t),north,south_north,(nq,nbeta),(tq,tbeta)


def run(F,J,max_n=8):
    rows=[]
    all_hist=[]
    for n in range(max_n+1):
        generated=set()
        actual=set()
        west_images=set()
        histogram=Counter()
        halves=defaultdict(set)
        beta_classes=defaultdict(set)
        pairs=defaultdict(set)
        matrix=[[0]*(n+1) for _ in range(n+1)]
        avoid1243=0
        avoid1234=0
        max_marks=0
        for word in permutations(range(1,n+1)):
            rr=ranks(word)
            if max(rr,default=0)<=3:
                avoid1234+=1
                suffix=0 if n==0 else 1
                while suffix<n and word[-suffix-1]>word[-suffix]:
                    suffix+=1
                pos=inverse(word)
                smallest=0 if n==0 else 1
                while smallest<n and pos[smallest-1]>pos[smallest]:
                    smallest+=1
                for p in range(suffix+1):
                    for q in range(smallest+1):
                        matrix[p][q]+=1
            occ=occurrences(word)
            if len(occ)==1:
                actual.add(word)
                a,b,i,j=occ[0]
                sigma=swap(word,i,j)
                need(not occurrences(sigma),"inverse unique-occurrence swap")
                need(skeleton(word)==skeleton(sigma),"inverse swap skeleton")
                marks,_,_=greedy_and_corners(sigma)
                need((i,j) in marks,"inverse mark recovered")
            elif not occ:
                avoid1243+=1
                marks,tau,corners=greedy_and_corners(word)
                need(tau not in west_images,"West map injectivity")
                west_images.add(tau)
                max_marks=max(max_marks,len(marks))
                need(len(marks)<=max((n-2)//2,0),"sharp deterministic mark upper bound")
                for i,j in marks:
                    target=swap(word,i,j)
                    need(len(occurrences(target))==1,"forward marked swap")
                    need(skeleton(target)==skeleton(word),"forward skeleton")
                    need(target not in generated,"marked swap injectivity")
                    generated.add(target)
                for mark in corners:
                    triple,north,south,nb,tb=geometry(tau,mark)
                    k,s,t=triple
                    histogram[triple]+=1
                    need((north,south) not in pairs[triple],"marked half-pair injectivity")
                    pairs[triple].add((north,south))
                    halves[k,s].add(north)
                    halves[k,t].add(south)
                    beta_classes[k,s,nb[0]].add(nb[1])
                    beta_classes[k,t,tb[0]].add(tb[1])
        need(generated==actual,"forward/inverse map is a finite bijection")
        need(avoid1243==avoid1234==F(n)[0][0],"avoidance equality")
        need(tuple(map(tuple,matrix))==F(n),"permutation/tableau F")
        need(sum(histogram.values())==len(actual),"corners count equals unique permutations")
        if n>=4:
            expected={(k,s,n-4-k-s):J(k,s)*J(k,n-4-k-s)
                      for k in range(n-3) for s in range(n-3-k)}
            need(histogram==expected,"all (k,s,t) product counts")
        for (k,s),words in halves.items():
            need(len(words)==J(k,s),"distinct half count J")
        for (k,s,q),betas in beta_classes.items():
            r=k+2
            need(len(betas)==F(s+r)[r-1][q]-F(s+r-1)[r-2][q-1],"q-refined half count")
        for triple,pairset in pairs.items():
            k,s,t=triple
            need(len(pairset)==len(halves[k,s])*len(halves[k,t]),"every independent half pair occurs")
        all_hist.extend([[n,*triple,value] for triple,value in sorted(histogram.items())])
        rows.append({"n":n,"permutations":factorial(n),"avoidance":avoid1243,
                     "exactly_one":len(actual),"eligible_marks":len(generated),
                     "max_marks":max_marks,"triple_classes":len(histogram),
                     "half_classes":len(halves),"q_refined_half_classes":len(beta_classes)})
    return {"max_n":max_n,"rows":rows,"spine_histogram":all_hist,
            "scope":"Exhaustive finite object audit only; not a proof for arbitrary n"}
