"""Small, explicit division-free integer arithmetic circuits (standard library).

The coding-block identities follow package27, with attribution in NOTICE.md.
Every binary addition, subtraction and multiplication is charged, including
multiplication by a numeral. Constant-only arithmetic is folded; reuse is free.
"""
from functools import lru_cache

class DAG:
    def __init__(self):
        self.nodes=[]; self.cache={}; self.names={}; self.known={}
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
        assert n>=0
        if n==0:return self.const(1)
        if n==1:return a
        h=self.power(a,n//2); r=self.times(h,h)
        return self.times(r,a) if n%2 else r
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
