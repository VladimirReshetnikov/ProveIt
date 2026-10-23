"""Small, explicit division-free integer arithmetic circuits (standard library).

The coding-block identities follow package27, with attribution in NOTICE.md.
Every binary addition, subtraction and multiplication is charged, including
multiplication by a numeral. Constant-only arithmetic is folded; reuse is free.
"""
from functools import lru_cache

class DAG:
    def __init__(self):
        self.nodes=[]; self.cache={}; self.names={}; self.known={}
        self.power_cache={}; self.known_exponents={}
    def node(self, kind, **kw):
        key=(kind,tuple(sorted(kw.items())))
        if key not in self.cache:
            self.cache[key]=len(self.nodes)
            self.nodes.append(dict(kind=kind,**kw))
        return self.cache[key]
    def const(self,x):
        n=self.node('literal',value=int(x));self.known[n]=int(x);return n
    def var(self,name): return self.node('variable',name=name)
    def fixed(self,name): return self.node('fixed',name=name)
    def binary(self,k,a,b):
        if a in self.known and b in self.known:
            x,y=self.known[a],self.known[b]
            return self.const(x+y if k=='add' else x-y if k=='sub' else x*y)
        if k=='add':
            if self.known.get(a)==0:return b
            if self.known.get(b)==0:return a
        if k=='sub':
            if self.known.get(b)==0:return a
            if a==b:return self.const(0)
        if k=='mul':
            if self.known.get(a)==0 or self.known.get(b)==0:return self.const(0)
            if self.known.get(a)==1:return b
            if self.known.get(b)==1:return a
        if k in ('add','mul') and a>b:a,b=b,a
        return self.node(k,left=a,right=b)
    def plus(self,*xs):
        a=self.const(0)
        for b in xs:a=self.binary('add',a,b)
        return a
    def minus(self,a,b):return self.binary('sub',a,b)
    def times(self,*xs):
        a=self.const(1)
        for b in xs:a=self.binary('mul',a,b)
        return a
    def power(self,a,n):
        """Fixed powers with deterministic reuse of already evaluated powers.

        A known split n=i+j costs one multiplication, otherwise recurse by
        squaring. This changes only the arithmetic circuit, never the value.
        """
        assert isinstance(n,int) and n>=0
        if n==0:return self.const(1)
        if n==1:return a
        if (a,n) in self.power_cache:return self.power_cache[a,n]
        known=self.known_exponents.setdefault(a,{1:a})
        pairs=[(i,n-i) for i in known if n-i in known]
        if pairs:
            i,j=min(pairs,key=lambda pair:abs(pair[0]-pair[1]))
            out=self.times(known[i],known[j])
        else:
            h=self.power(a,n//2);out=self.times(h,h)
            if n%2:out=self.times(out,a)
        self.power_cache[a,n]=out;known[n]=out
        return out
    def save(self,name,a):self.names[name]=a;return a
    def prune(self,root):
        live=set(); todo=[root]
        while todo:
            i=todo.pop()
            if i in live:continue
            live.add(i);n=self.nodes[i]
            if n['kind'] in ('add','sub','mul'):todo.extend((n['left'],n['right']))
        order=sorted(live); remap={x:i for i,x in enumerate(order)}
        nodes=[]
        for i in order:
            n=self.nodes[i].copy()
            if n['kind'] in ('add','sub','mul'):
                n['left']=remap[n['left']]; n['right']=remap[n['right']]
            nodes.append(n)
        return nodes,remap[root],{k:remap[v] for k,v in self.names.items() if v in live}

def coding_blocks(d,B,nu,keys,z):
    """Evaluate the complete index digit polynomial without variable powers."""
    A,M,P,c=d.plus,d.times,d.power,d.const
    t=[B]
    for _ in range(nu+1):t.append(M(P(t[-1],4),t[-1]))
    v=[None]*(nu+1); v[nu]=c(1)
    for j in range(nu-1,-1,-1):v[j]=M(P(t[j],4),v[j+1])
    vs=[t[nu]]+v
    hs=[c(1)]+[c(0)]*4
    for term in vs:
        for k in range(1,5):hs[k]=A(hs[k],M(term,hs[k-1]))
    terms=[((4-sum(alpha),)+tuple(alpha),c(name) if isinstance(name,int) else d.fixed(name))
           for alpha,name in keys]
    @lru_cache(None)
    def horner(ts):
        if not ts:return c(0)
        counts=[sum(ex[j]>0 for ex,co in ts) for j in range(len(vs))]
        if not max(counts):return A(*(co for ex,co in ts))
        j=max(range(len(vs)),key=lambda j:(counts[j],sum(ex[j] for ex,co in ts),j))
        yes=[];no=[]
        for ex,co in ts:
            if ex[j]:
                ex=list(ex);ex[j]-=1;yes.append((tuple(ex),co))
            else:no.append((ex,co))
        return A(horner(tuple(no)),M(vs[j],horner(tuple(yes))))
    e=M(t[nu],A(M(z,hs[4]),horner(tuple(terms))))
    factors=[A(c(1),M(x,A(c(1),x),A(c(1),P(x,2)))) for x in t[:nu+1]]
    q=t[nu+1]
    lam=M(*factors,A(c(1),q),A(c(1),P(q,2)))
    return q,A(*t[1:nu+1]),lam,e,t[nu]

def canonical_keys(constants):
    canonical={}; keys=[]; aliases={}
    for row in constants['coefficient_records']:
        recipe=row['coefficient_polynomial_in_fixed_ports']
        sig=tuple((tuple(r['powers']),r['coefficient']) for r in recipe)
        if len(recipe)==1 and not any(recipe[0]['powers']):
            name=recipe[0]['coefficient']; aliases[row['name']]={'literal':name}
        else:
            name=canonical.setdefault(sig,row['name']);aliases[row['name']]={'fixed':name}
        keys.append((tuple(row['alpha']),name))
    return keys,aliases

def evaluate(body,fixed,variables,modulus):
    vals=[]
    for n in body['nodes']:
        k=n['kind']
        if k=='literal':r=n['value']
        elif k=='fixed':r=fixed[n['name']]
        elif k=='variable':r=variables[n['name']]
        else:
            a,b=vals[n['left']],vals[n['right']]
            r=a+b if k=='add' else a-b if k=='sub' else a*b
        vals.append(r%modulus)
    return vals[body['output']],{k:vals[i] for k,i in body['named_nodes'].items()}


