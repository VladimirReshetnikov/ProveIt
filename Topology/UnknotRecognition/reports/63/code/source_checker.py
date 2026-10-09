"""Source-bound independent replay for the literal braid research frontend.

Does not import the presentation producer, donor scanner, saturation routine or
word utilities. It independently reconstructs Artin images by substitution in
reverse crossing order, checks all donor cuts, and retains every relator slot.
It reuses only the separately implemented local graph proof checker and Edge
as a record type. No arbitrary-presentation UNKNOT API is provided.
"""
from collections import deque
from power_graph import Edge
from graph_checker import verify as verify_graph

class ReplayLimit(RuntimeError): pass

def _inv(w): return [-x for x in w[::-1]]
def _free(w):
    d=deque()
    for x in w:
        if d and d[-1]==-x: d.pop()
        else: d.append(x)
    return list(d)
def _cyc(w):
    d=deque(_free(w))
    while len(d)>1 and d[0]==-d[-1]: d.popleft(); d.pop()
    return list(d)

def _source(strands,braid,letter_cap):
    if type(strands) is not int or not 1<=strands<=letter_cap: raise ValueError()
    if not isinstance(braid,(list,tuple)): raise ValueError()
    if any(type(x) is not int or not 0<abs(x)<strands for x in braid): raise ValueError()
    if strands>len(braid)+1: raise ValueError()
    # Independent cycle count using union-find along permutation orbits.
    permutation=list(range(strands))
    for c in braid:
        i=abs(c)-1; permutation[i:i+2]=permutation[i:i+2][::-1]
    visited=set(); components=0
    for s in range(strands):
        if s in visited: continue
        components+=1; v=s
        while v not in visited: visited.add(v); v=permutation[v]
    if components!=1: raise ValueError()
    # Tuple-image updates build phi_1 o ... o phi_n. Direct substitutions
    # are therefore applied in reverse order, independently of that producer.
    images=[[i+1] for i in range(strands)]
    for c in reversed(braid):
        a=abs(c); b=a+1
        table={a:[a,b,-a], b:[a]} if c>0 else {a:[b], b:[-b,a,b]}
        projected=sum(len(table.get(abs(x),[x])) for w in images for x in w)
        if projected>letter_cap: raise ReplayLimit('Artin replay allocation')
        nxt=[]
        for w in images:
            out=[]
            for x in w:
                t=table.get(abs(x),[abs(x)])
                out.extend(t if x>0 else _inv(t))
            nxt.append(_free(out))
        images=nxt
    roots=[_cyc(w+[-i-1]) for i,w in enumerate(images)]
    transformed=[]
    for w in roots:
        out=[]
        for x in w:
            t=[strands] if abs(x)==strands else [abs(x),strands]
            out.extend(t if x>0 else _inv(t))
        transformed.append(_cyc(out))
    return transformed

def decode_donor(relators,proof):
    """Decode only after exact source checks; raises ValueError on a forgery."""
    if not isinstance(proof,dict): raise ValueError()
    kind=proof.get('kind'); slot=proof.get('slot')
    if type(slot) is not int or not 0<=slot<len(relators): raise ValueError()
    R=_cyc(relators[slot])
    if not R: raise ValueError()
    if kind=='power':
        if set(proof)!={'kind','slot'} or any(x!=R[0] for x in R): raise ValueError()
        return Edge(abs(R[0]),abs(R[0]),2,1,True)
    if kind!='conjugacy' or set(proof)!={'kind','slot','period','rotation','head','conj'}: raise ValueError()
    p,h,k,t=(proof[z] for z in ('period','head','conj','rotation'))
    if any(type(x) is not int for x in (p,h,k,t)): raise ValueError()
    if not 1<=p<=len(R) or len(R)%p or not 0<=t<p or not 1<=h<p or not 0<=k<=p: raise ValueError()
    if any(R[i]!=R[i%p] for i in range(len(R))): raise ValueError()
    u=R[:p]; w=u[t:]+u[:t]; B=p-h-2*k
    if B<=0: raise ValueError()
    if any(x!=w[0] for x in w[:h]): raise ValueError()
    middle=w[h+k:h+k+B]
    if any(x!=middle[0] for x in middle): raise ValueError()
    if w[p-k:]!=_inv(w[h:h+k]) and k: raise ValueError()
    return Edge(abs(w[0]),abs(middle[0]),h*(1 if w[0]>0 else -1),
                -B*(1 if middle[0]>0 else -1),k==0)

def verify_braid(strands,braid,certificate,*,letter_cap=200_000):
    try:
        if not isinstance(certificate,dict) or set(certificate)!={'version','basis','rounds','terminal'}: return False
        if type(certificate['version']) is not int or certificate['version']!=1 or certificate['basis']!='right-differences': return False
        relators=_source(strands,braid,letter_cap); alive=set(range(1,strands+1))
        rounds=certificate['rounds']
        if not isinstance(rounds,list) or len(rounds)>strands-1: return False
        for r in rounds:
            if not isinstance(r,dict) or set(r)!={'donors','graph'} or not isinstance(r['donors'],list): return False
            if len(r['donors'])>max(1,sum(len(w)**2 for w in relators)): return False
            edges=[decode_donor(relators,p) for p in r['donors']]
            graph=r['graph']
            if not verify_graph(sorted(alive),edges,graph) or not graph['killed']: return False
            dead=set(graph['killed'])
            # Abelianization h(anchor)=1 is an independent necessary guard.
            if strands in dead: return False
            alive-=dead
            relators=[_cyc([x for x in w if abs(x) not in dead]) for w in relators]
        terminal=certificate['terminal']
        if not isinstance(terminal,dict) or set(terminal)!={'kind','generator'}: return False
        if terminal['kind']!='rank-one' or type(terminal['generator']) is not int or terminal['generator']!=strands: return False
        return alive=={strands} and all(all(abs(x)==strands for x in w) and sum(1 if x>0 else -1 for x in w)==0 for w in relators)
    except (ValueError,TypeError,KeyError,IndexError,ReplayLimit,AttributeError):
        return False
