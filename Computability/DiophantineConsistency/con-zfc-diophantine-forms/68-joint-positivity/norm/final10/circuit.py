"""Circuit helper reused from our independently authored round9 work."""
from collections import Counter
class Circuit:
    def __init__(self):
        self.nodes=[];self.intern={};self.names={};self.ints={};self.powers={};self.power_plans={}
    def leaf(self,kind,**fields):
        key=(kind,tuple(sorted(fields.items())))
        if key not in self.intern:
            self.intern[key]=len(self.nodes);self.nodes.append(dict(kind=kind,**fields))
        return self.intern[key]
    def c(self,n):
        q=self.leaf('literal',value=n);self.ints[q]=n;return q
    def op(self,kind,a,b):
        ia,ib=self.ints.get(a),self.ints.get(b)
        if ia is not None and ib is not None:
            return self.c(ia+ib if kind=='add' else ia-ib if kind=='sub' else ia*ib)
        if kind=='add':
            if ia==0:return b
            if ib==0:return a
        if kind=='sub':
            if ib==0:return a
            if a==b:return self.c(0)
        if kind=='mul':
            if ia==0 or ib==0:return self.c(0)
            if ia==1:return b
            if ib==1:return a
        if kind in ('add','mul') and a>b:a,b=b,a
        return self.leaf(kind,left=a,right=b)
    def add(self,*args):
        r=self.c(0)
        for a in args:r=self.op('add',r,a)
        return r
    def mul(self,*args):
        r=self.c(1)
        for a in args:r=self.op('mul',r,a)
        return r
    def sub(self,a,b):return self.op('sub',a,b)
    def pow(self,a,n):
        if not isinstance(n,int) or n<0: raise ValueError("nonnegative fixed exponent required")
        if n==0:return self.c(1)
        ps=self.powers.setdefault(a,{1:a})
        if n not in ps:
            if a in self.power_plans and n in self.power_plans[a]:
                x,y=self.power_plans[a][n];ps[n]=self.mul(self.pow(a,x),self.pow(a,y));return ps[n]
            pairs=[(abs(n-2*k),k) for k in ps if n-k in ps]
            if pairs:
                k=min(pairs)[1];r=self.mul(ps[k],ps[n-k])
            else:
                half=self.pow(a,n//2);r=self.mul(half,half)
                if n%2:r=self.mul(r,a)
            ps[n]=r
        return ps[n]
    def save(self,name,n):self.names[name]=n;return n
    def finish(self,out):
        live=set();todo=[out]
        while todo:
            p=todo.pop()
            if p in live:continue
            live.add(p);n=self.nodes[p]
            if 'left'in n:todo.extend((n['left'],n['right']))
        ids={old:new for new,old in enumerate(sorted(live))};nodes=[]
        for old in sorted(live):
            n=dict(self.nodes[old])
            if 'left'in n:n.update(left=ids[n['left']],right=ids[n['right']])
            nodes.append(n)
        deg=[]
        for n in nodes:
            deg.append(1 if n['kind']=='variable' else 0 if 'left'not in n else
                deg[n['left']]+deg[n['right']] if n['kind']=='mul' else max(deg[n['left']],deg[n['right']]))
        names={k:ids[v] for k,v in self.names.items() if v in ids}
        counts=dict(Counter(n['kind'] for n in nodes if 'left'in n))
        return dict(nodes=nodes,output=ids[out],named_nodes=names,operation_counts=counts,
            total_operations=sum(counts.values()),degree_upper_bound=deg[ids[out]],
            named_degree_bounds={k:deg[v] for k,v in names.items()})

def horner(d,b,items):
    pairs=sorted(items,reverse=True);e,r=pairs[0]
    for f,v in pairs[1:]:r=d.add(d.mul(r,d.pow(b,e-f)),v);e=f
    return d.mul(r,d.pow(b,e))
