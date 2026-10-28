"""Exact checks for adaptive quartet conditioning and its strict schedule.
Python >=3.10, standard library only. No checks rely on assert.
This checks finite instances/certificates; the uniform theorem is in quartet.tex.
"""
from fractions import Fraction as Q
from itertools import combinations, product
from math import isqrt
from random import Random
import json
from pathlib import Path

PAIRS = (((0,1),(2,3)), ((0,2),(1,3)), ((0,3),(1,2)))
G = {1:Q(0),2:Q(2),3:Q(6),4:Q(26,3),6:Q(22),8:Q(110,3),16:Q(442,3)}

def require(ok, message):
    if not ok: raise RuntimeError(message)

def split4(vertices):
    n=len(vertices); sizes=[n//4]*4
    for j in range(n%4): sizes[3-j]+=1
    blocks=[];start=0
    for size in sizes:
        blocks.append(tuple(vertices[start:start+size]));start+=size
    return blocks

def edge_product(a,b,sizes):
    ans=1
    for x in a:
        for y in b:
            ans*=sizes[x,y]*sizes[y,x]
    return ans

def tree(vertices,sizes):
    """Choose a 2+2 supertree by exact integer list-size products."""
    vertices=tuple(vertices)
    if len(vertices)==1:return vertices[0]
    if len(vertices)<4:
        m=len(vertices)//2
        return (tree(vertices[:m],sizes),tree(vertices[m:],sizes))
    blocks=split4(vertices)
    scores=[]
    for p in PAIRS:
        scores.append(min(edge_product(blocks[a],blocks[b],sizes) for a,b in p))
    chosen=max(range(3),key=lambda j:scores[j])
    return tuple(tuple(tree(blocks[j],sizes) for j in pair) for pair in PAIRS[chosen])

def fixed_tree(vertices):
    vertices=tuple(vertices)
    if len(vertices)==1:return vertices[0]
    m=len(vertices)//2
    return (fixed_tree(vertices[:m]),fixed_tree(vertices[m:]))

def leaves(t):
    if isinstance(t,int):return (t,)
    return leaves(t[0])+leaves(t[1])

def path_sets(t,above=frozenset()):
    if isinstance(t,int):return [(t,above)]
    a=set(leaves(t[0]));b=set(leaves(t[1]))
    cross=frozenset((x,y) for x,y in product(a,b))|frozenset((y,x) for x,y in product(a,b))
    return path_sets(t[0],above|cross)+path_sets(t[1],above|cross)

def profile(t,h):
    return max(sum(h[e] for e in es) for _,es in path_sets(t))

def ring_add(a,b):return ((a[0]+b[0])%64,(a[1]+b[1])%64)
def ring_mul(a,b):return ((a[0]*b[0])%64,(a[0]*b[1]+a[1]*b[0])%64)

def contract_stream(t,sizes,factors,assignment,calls):
    if isinstance(t,int):
        calls[t]+=1
        edges,table=factors[t]
        return table[tuple(assignment[e] for e in edges)]
    a=set(leaves(t[0]));b=set(leaves(t[1]))
    cross=sorted([(x,y) for x in a for y in b]+[(y,x) for x in a for y in b])
    ans=(0,0)
    for vals in product(*(range(sizes[e]) for e in cross)):
        assignment.update(zip(cross,vals))
        left=contract_stream(t[0],sizes,factors,assignment,calls)
        right=contract_stream(t[1],sizes,factors,assignment,calls)
        ans=ring_add(ans,ring_mul(left,right))
    for e in cross:del assignment[e]
    return ans

def matched_fixtures():
    results=[]
    for n in (4,8,16):
        edges=[(x,y) for x in range(n) for y in range(n) if x!=y]
        blocks=split4(tuple(range(n)));a,b,c,d=(z[0] for z in blocks)
        active={(a,c),(c,a),(b,d),(d,b)}
        sizes={e:2 if e in active else 1 for e in edges}
        factors={}
        for v in range(n):
            incident=sorted(e for e in edges if v in e)
            table={vals:((1+2*v+2*sum(vals))%64,(2*v+sum((j+1)*x for j,x in enumerate(vals)))%64)
                   for vals in product(*(range(sizes[e]) for e in incident))}
            factors[v]=(incident,table)
        tr_old=fixed_tree(range(n));tr_new=tree(range(n),sizes)
        old=[0]*n;new=[0]*n
        ans_old=contract_stream(tr_old,sizes,factors,{},old)
        ans_new=contract_stream(tr_new,sizes,factors,{},new)
        require(ans_old==ans_new,'matched fixture outputs')
        require(sum(old)==16*n and sum(new)==4*n,'matched fixture calls')
        results.append({'groups':n,'active_directed_pairs':[list(e) for e in sorted(active)],
                        'old_leaf_calls':sum(old),'adaptive_leaf_calls':sum(new),
                        'old_max_path_log2':4,'adaptive_max_path_log2':2,
                        'exact_output':list(ans_new)})
    return results

def check_finite():
    exhaustive=0
    undirected=list(combinations(range(4),2))
    for vals in product(range(5),repeat=6):
        w=dict(zip(undirected,vals))
        scores=[min(w[tuple(sorted(a))],w[tuple(sorted(b))]) for a,b in PAIRS]
        f=sum(vals)-max(scores)
        require(3*f*f<=13*sum(x*x for x in vals),'quartet inequality')
        exhaustive+=1
    # In each complementary pair the smaller edge is 4 and the larger is 6.
    w={(0,1):4,(2,3):6,(0,2):4,(1,3):6,(0,3):4,(1,2):6}
    f=sum(w.values())-4
    require(3*f*f==13*sum(x*x for x in w.values()),'sharp quartet fixture')
    rng=Random(20261026);profiles=0
    for n in (4,6,8,16):
        edges=[(x,y) for x in range(n) for y in range(n) if x!=y]
        for _ in range(500):
            h={e:rng.randrange(13) for e in edges}
            sizes={e:2**h[e] for e in edges}
            p=profile(tree(range(n),sizes),h)
            require(p*p<=G[n]*sum(x*x for x in h.values()),f'profile n={n}')
            profiles+=1
    contractions=0;leaf_calls=0
    for n in (4,6,8,16):
        edges=[(x,y) for x in range(n) for y in range(n) if x!=y]
        for _ in range(20):
            active=set(rng.sample(edges,6));sizes={e:2 if e in active else 1 for e in edges}
            factors={}
            for v in range(n):
                incident=sorted(e for e in edges if v in e)
                table={vals:(rng.randrange(64),rng.randrange(64)) for vals in product(*(range(sizes[e]) for e in incident))}
                factors[v]=(incident,table)
            literal=(0,0)
            for vals in product(*(range(sizes[e]) for e in edges)):
                assignment=dict(zip(edges,vals));term=(1,0)
                for v in range(n):
                    inc,tab=factors[v]
                    term=ring_mul(term,tab[tuple(assignment[e] for e in inc)])
                literal=ring_add(literal,term)
            tr=tree(range(n),sizes);calls=[0]*n
            got=contract_stream(tr,sizes,factors,{},calls)
            require(got==literal,'literal contraction differs')
            for v,es in path_sets(tr):
                expected=1
                for e in es:expected*=sizes[e]
                require(calls[v]==expected,'leaf call ledger')
            leaf_calls+=sum(calls);contractions+=1
    # Unequal-block analytic certificates. Each pair lists directed cardinalities.
    unequal=[((1,1,2,2),(Q(0),Q(1,2),Q(1,2)),Q(22)),
             ((2,2,2,2),(Q(1,3),)*3,Q(110,3)),
             ((4,4,4,4),(Q(1,3),)*3,Q(442,3))]
    for ks,ps,target in unequal:
        require(sum(ps)==1 and all(p>=0 for p in ps),'probability vector')
        root=Q(0)
        for ((a,b),(c,d)),p in zip(PAIRS,ps):
            x=2*ks[a]*ks[b];y=2*ks[c]*ks[d]
            root+=max(x,y)+min(x,y)*(1-p)**2
        require(root+max(G[k] for k in ks)==target,'unequal norm certificate')
    return {'quartet_exhaustive':exhaustive,'random_profiles':profiles,'exact_contractions':contractions,
            'instrumented_leaf_calls':leaf_calls,'ring':'(Z/64Z)[V]/(V^2)','unequal_block_certificates':3,'matched_fixtures':matched_fixtures()}

# Positive interval arithmetic, represented as exact rational endpoints.
def add(a,b):return (a[0]+b[0],a[1]+b[1])
def mul(a,b):return (a[0]*b[0],a[1]*b[1])
def div(a,b):
    require(b[0]>0,'division interval includes zero')
    return (a[0]/b[1],a[1]/b[0])
def scale(a,x):return mul(a,(Q(x),Q(x)))
def sqrtq(q,digits=70):
    q=Q(q);s=10**digits;k=isqrt(q.numerator*s*s//q.denominator)
    return (Q(k,s),Q(k+1,s))
def atan_bounds(q,n=110):
    x=Q(1,q);partial=sum(((-1)**j*x**(2*j+1)/Q(2*j+1) for j in range(n)),Q(0))
    nxt=(-1)**n*x**(2*n+1)/Q(2*n+1)
    return (min(partial,partial+nxt),max(partial,partial+nxt))
def constants():
    a=atan_bounds(5);b=atan_bounds(239)
    pi=(16*a[0]-4*b[1],16*a[1]-4*b[0])
    x=Q(1,3);n=120
    ln=2*sum((x**(2*j+1)/Q(2*j+1) for j in range(n)),Q(0))
    ln2=(ln,ln+2*x**(2*n+1)/(Q(2*n+1)*(1-x*x)))
    return pi,ln2

def coefficient(gs,rs,fs,etas):
    pi,ln2=constants();kap=div(mul(pi,sqrtq(2)),ln2)
    total=(Q(0),Q(0));terms=[]
    ratio=sqrtq(Q(2,5));gap=(1-ratio[1],1-ratio[0])
    for j,(g,r,f,eta) in enumerate(zip(gs,rs,fs,etas)):
        term=scale(div(sqrtq(g),sqrtq(eta)),Q(f,r))
        if j==4:term=div(term,gap)
        terms.append(mul(kap,term));total=add(total,term)
    return mul(kap,total),terms

def check_schedule():
    rs=(16,16,8,6,4);fs=(Q(1),Q(1,8),Q(1,64),Q(1,256),Q(1,768))
    etas=(Q(1249,100000),Q(1249,100000),Q(104,12500),Q(107,20000),Q(27,6400))
    cap=[etas[0],sum(etas[:2]),sum(etas[:3]),sum(etas[:4]),sum(etas[:4])+etas[4]/(1-Q(5,8))]
    require(cap==[Q(1249,100000),Q(1249,50000),Q(333,10000),Q(773,20000),Q(499,10000)],'capacity identities')
    require(6**200<2**517,'log_2(6)<517/200')
    log_upper=(Q(4),Q(4),Q(3),Q(517,200),Q(2))
    margins=[Q(1,10)-(2 if j==0 else 1)*cap[j]*log_upper[j] for j in range(5)]
    require(min(margins)>=Q(1,12500),'uniform old-side packing slack')
    require(Q(2,10)+cap[-1]==Q(2499,10000),'fresh-side/rounding exponent')
    require(Q(8,5)<Q(5,3),'positive depth exponent')
    c,terms=coefficient([G[r] for r in rs],rs,fs,etas)
    require(Q('50.30468921409')<c[0] and c[1]<Q('50.30468921410'),'new coefficient interval')
    old,_=coefficient([170,170,42,24,10],rs,fs,etas)
    require(Q('54.02470271283')<old[0] and old[1]<Q('54.02470271284'),'matched baseline interval')
    prior,_=coefficient([118,132,42,24,10],(13,14,8,6,4),
              (Q(1),Q(2,13),Q(2,91),Q(1,182),Q(1,546)),
              (Q(27,2000),Q(51,4000),Q(141,20000),Q(107,20000),Q(27,6400)))
    require(Q('55.40466590660')<prior[0] and prior[1]<Q('55.40466590662'),'composed incoming baseline')
    pi,ln2=constants()
    simple=scale(mul(div(pi,ln2),sqrtq(Q(221,15))),Q(5,2))
    addterm=div((Q(1),Q(1)),scale(sqrtq(3),3))
    simple=mul(simple,add((Q(1),Q(1)),addterm))
    require(Q('51.86270186389')<simple[0] and simple[1]<Q('51.86270186390'),'simple r16 coefficient')
    return {'strict_coefficient_interval':['50.30468921409','50.30468921410'],
      'matched_fixed_tree_interval':['54.02470271283','54.02470271284'],
      'composed_incoming_interval':['55.40466590660','55.40466590662'],
      'simple_r16_interval':['51.86270186389','51.86270186390'],
      'arities':list(rs),'eta':[str(x) for x in etas],
      'cumulative_capacities':[str(x) for x in cap],
      'packing_margins':[str(x) for x in margins],
      'safe_eventual_coefficient':'50.305',
      'method':'Exact rational intervals (Machin pi, positive atanh series ln2, integer square roots)'}

if __name__=='__main__':
    result={'finite_checks':check_finite(),'schedule':check_schedule()}
    path=(Path(__file__).resolve().parents[1] / "results" / 'quartet_checks.json')
    path.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
