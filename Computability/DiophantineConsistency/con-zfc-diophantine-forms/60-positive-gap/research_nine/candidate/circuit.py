"""Independent minimal arithmetic-DAG builder; every live binary gate is charged."""
class DAG:
    def __init__(self):
        self.nodes=[];self.lookup={};self.named={};self.powers={}
    def node(self,kind,**kw):
        key=(kind,)+tuple(sorted(kw.items()))
        if key not in self.lookup:
            self.lookup[key]=len(self.nodes);self.nodes.append(dict(kind=kind,**kw))
        return self.lookup[key]
    def const(self,value):return self.node('literal',value=value)
    def fixed(self,name):return self.node('fixed',name=name)
    def var(self,name):return self.node('variable',name=name)
    def val(self,x):
        n=self.nodes[x];return n['value'] if n['kind']=='literal' else None
    def binary(self,kind,a,b):
        x,y=self.val(a),self.val(b)
        if x is not None and y is not None:
            return self.const(x+y if kind=='add' else x-y if kind=='sub' else x*y)
        if kind=='add':
            if x==0:return b
            if y==0:return a
        elif kind=='sub':
            if y==0:return a
            if a==b:return self.const(0)
        elif kind=='mul':
            if x==0 or y==0:return self.const(0)
            if x==1:return b
            if y==1:return a
        if kind in ('add','mul') and a>b:a,b=b,a
        return self.node(kind,left=a,right=b)
    def plus(self,*xs):
        z=self.const(0)
        for x in xs:z=self.binary('add',z,x)
        return z
    def times(self,*xs):
        z=self.const(1)
        for x in xs:z=self.binary('mul',z,x)
        return z
    def minus(self,a,b):return self.binary('sub',a,b)
    def power(self,x,e):
        if type(e) is not int or e<0:raise ValueError('fixed nonnegative exponent required')
        if (x,e) in self.powers:return self.powers[x,e]
        if e==0:z=self.const(1)
        elif e==1:z=x
        else:
            h=self.power(x,e//2);z=self.times(h,h)
            if e%2:z=self.times(z,x)
        self.powers[x,e]=z;return z
    def save(self,name,x):self.named[name]=x;return x
    def prune(self,out):
        keep=set();stack=[out]
        while stack:
            i=stack.pop()
            if i in keep:continue
            keep.add(i);n=self.nodes[i]
            if n['kind'] in ('add','sub','mul'):stack.extend((n['left'],n['right']))
        old=sorted(keep);ix={j:i for i,j in enumerate(old)};nodes=[]
        for j in old:
            n=self.nodes[j].copy()
            if n['kind'] in ('add','sub','mul'):n['left']=ix[n['left']];n['right']=ix[n['right']]
            nodes.append(n)
        return nodes,ix[out],{k:ix[v] for k,v in self.named.items() if v in ix}
