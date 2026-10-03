"""Exact quadratic certificates for fixed active-membrane transition-motif schemas.
Stdlib only. Natural variables; fixed supports use multiplicity 1 + variable.
No claim of fixed-arity universal Diophantine encoding.
"""
from collections import Counter
from dataclasses import dataclass, asdict
from itertools import product
import json, random

@dataclass(frozen=True)
class Rule:
    kind: str
    label: str
    a: int
    out: tuple
    other: tuple=()
    elementary: bool=False

@dataclass(frozen=True)
class Cfg:
    label: str
    x: tuple
    children: tuple=()

@dataclass(frozen=True)
class Plan:
    label: str
    x: tuple
    children: tuple=()
    evolution: tuple=()  # pairs (rule index, multiplicity)
    mode: int=-1
    def __post_init__(self):
        counts=Counter()
        for r,n in self.evolution:
            if type(r) is not int or r<0 or type(n) is not int or n<0:
                raise ValueError('natural evolution count/index required')
            counts[r]+=n
        object.__setattr__(self,'evolution',tuple(sorted((r,n) for r,n in counts.items() if n)))

def ckey(c): return (c.label,c.x,tuple(sorted(ckey(x) for x in c.children)))
def pkey(p): return (p.label,p.x,p.evolution,p.mode,tuple(sorted(pkey(x) for x in p.children)))
def source(p): return Cfg(p.label,p.x,tuple(sorted((source(c) for c in p.children),key=ckey)))
def height(p): return 0 if not p.children else 1+max(map(height,p.children))
def add(x,y): return tuple(a+b for a,b in zip(x,y))
def unit(d,a): return tuple(int(i==a) for i in range(d))


def expanded_oracle(root,rules,check=True):
    """Object-instance allocation first; then independent bottom-up structural effects.
    Returns root forest, environmental output, records by canonical plan signature.
    Raises ValueError for resource/slot/maximality errors.
    """
    d=len(root.x); records={}; used={}; residual={}; nodes={}; paths=[]
    def walk(p,path):
        nodes[path]=p; paths.append(path); used[path]=[0]*d
        for k,c in enumerate(p.children): walk(c,path+(k,))
    walk(root,())
    for path in paths:
        p=nodes[path]
        if any(type(z) is not int or z<0 for z in p.x): raise ValueError('not natural')
        for r,n in p.evolution:
            if type(n) is not int or n<0 or rules[r].kind!='evolve' or rules[r].label!=p.label: raise ValueError('evolution')
            used[path][rules[r].a]+=n
        if p.mode>=0:
            r=rules[p.mode]
            if r.kind=='evolve' or r.label!=p.label or (r.kind=='divide' and r.elementary and p.children): raise ValueError('mode')
            if path==() and r.kind in ('in','divide','dissolve'): raise ValueError('skin')
            loc=path[:-1] if r.kind=='in' else path
            used[loc][r.a]+=1
    for path in paths:
        residual[path]=tuple(x-u for x,u in zip(nodes[path].x,used[path]))
        if check and min(residual[path])<0: raise ValueError('overspend old objects')
    # Can any ONE rule be added to the old allocation? Exact set maximality.
    for path in paths:
        p=nodes[path]
        for r in rules:
            if r.label!=p.label: continue
            if r.kind=='divide' and r.elementary and p.children: continue
            if r.kind!='evolve' and p.mode>=0: continue
            if path==() and r.kind in ('in','divide','dissolve'): continue
            loc=path[:-1] if r.kind=='in' else path
            if check and residual[loc][r.a]>0: raise ValueError('nonmaximal')
    def finish(path):
        p=nodes[path]; kids=[]; y=list(residual[path])
        for r,n in p.evolution:
            for a,z in enumerate(rules[r].out): y[a]+=n*z
        for k,c in enumerate(p.children):
            fs,up=finish(path+(k,)); kids.extend(fs)
            y=[a+b for a,b in zip(y,up)]
        r=rules[p.mode] if p.mode>=0 else None
        if r and r.kind=='in': y=[a+b for a,b in zip(y,r.out)]
        kids=tuple(sorted(kids,key=ckey)); y=tuple(y); up=(0,)*d
        if r and r.kind=='dissolve': fs=kids; up=add(y,r.out)
        elif r and r.kind=='divide':
            fs=(Cfg(p.label,add(y,r.out),kids),Cfg(p.label,add(y,r.other),kids))
        else:
            fs=(Cfg(p.label,y,kids),)
            if r and r.kind=='out': up=r.out
        records[pkey(p)]=(residual[path],y,up,fs)
        return fs,up
    forest,up=finish(())
    return forest,up,records

class Poly:
    def __init__(self,terms=None): self.t={m:c for m,c in (terms or {}).items() if c}
    @staticmethod
    def cast(x): return x if isinstance(x,Poly) else Poly({():x})
    @staticmethod
    def var(x): return Poly({(x,):1})
    def __add__(self,o):
        o=Poly.cast(o); z=Counter(self.t); z.update(o.t); return Poly(dict(z))
    __radd__=__add__
    def __neg__(self): return Poly({m:-c for m,c in self.t.items()})
    def __sub__(self,o): return self+-Poly.cast(o)
    def __rsub__(self,o): return Poly.cast(o)+-self
    def __mul__(self,o):
        o=Poly.cast(o); z=Counter()
        for m,c in self.t.items():
            for n,e in o.t.items(): z[tuple(sorted(m+n))]+=c*e
        return Poly(dict(z))
    __rmul__=__mul__
    def evaluate(self,a):
        return sum(c*prod(a[v] for v in m) for m,c in self.t.items())
    @property
    def degree(self): return max(map(len,self.t),default=0)
    def as_json(self): return [[c,list(m)] for m,c in sorted(self.t.items())]
def prod(xs):
    z=1
    for x in xs:z*=x
    return z


def compile_schema(schema,rules,d):
    """Return (named quadratic residuals, variable list). Roots/endpoints are interface.
    Supported model is polarizationless weak division, with elementary division a
    syntactic restriction on selected schemas. Rule choices and DAG maps are data.
    """
    cs=schema['configs']; ts=schema['transitions']; K=len(cs); J=len(ts)
    if not (0<=schema['root']<J) or cs[ts[schema['root']]['source']]['label']!='skin': raise ValueError('root')
    for z in rules:
        if z.kind not in ('evolve','in','out','dissolve','divide') or not 0<=z.a<d: raise ValueError('rule')
        if len(z.out)!=d or any(type(n) is not int or n<0 for n in z.out): raise ValueError('rule output')
        if z.kind!='evolve' and sum(z.out)!=1: raise ValueError('noncooperative structural output')
        if z.kind=='divide' and (len(z.other)!=d or any(type(n) is not int or n<0 for n in z.other) or sum(z.other)!=1): raise ValueError('division output')
    seen=set()
    def visit(j):
        if j in seen:return
        seen.add(j)
        for k in ts[j]['children']:visit(k)
    visit(schema['root'])
    if len(seen)!=J:raise ValueError('orphan transition')
    names=[]
    def v(s): names.append(s); return Poly.var(s)
    X={(i,a):v(f'x:{i}:{a}') for i in range(K) for a in range(d)}
    C={(i,k):1+v(f'c:{i}:{k}') for i,c in enumerate(cs) for k in c['children']}
    M={(j,k):1+v(f'm:{j}:{k}') for j,t in enumerate(ts) for k in t['children']}
    E={(j,r):v(f'e:{j}:{r}') for j,t in enumerate(ts) for r,z in enumerate(rules) if z.kind=='evolve' and z.label==cs[t['source']]['label']}
    U={(j,a):v(f'u:{j}:{a}') for j in range(J) for a in range(d)}
    Y={(j,a):v(f'y:{j}:{a}') for j in range(J) for a in range(d)}
    O={(j,a):v(f'o:{j}:{a}') for j in range(J) for a in range(d)}
    F={(j,i):v(f'f:{j}:{i}') for j in range(J) for i in range(K)}
    eq=[]
    def put(n,p): eq.append((n,Poly.cast(p)))
    for i,c in enumerate(cs):
        if len(c['children'])!=len(set(c['children'])) or any(k>=i or k<0 or cs[k]['label']=='skin' for k in c['children']): raise ValueError('configuration DAG')
    for j,t in enumerate(ts):
        if len(t['children'])!=len(set(t['children'])) or any(k>=j or k<0 for k in t['children']): raise ValueError('transition DAG')
        s=t['source']; label=cs[s]['label']; r=rules[t['mode']] if t['mode']>=0 else None
        if r and (r.kind=='evolve' or r.label!=label or (r.kind=='divide' and r.elementary and cs[s]['children'])): raise ValueError('mode')
        if label=='skin' and r and r.kind in ('in','divide','dissolve'): raise ValueError('skin mode')
        if r and r.kind=='dissolve': branches=[]
        else: branches=t['targets']
        if len(branches)!=(0 if r and r.kind=='dissolve' else 2 if r and r.kind=='divide' else 1): raise ValueError('target arity')
        if any(cs[i]['label']!=label for i in branches): raise ValueError('target label')
        if r and r.kind=='dissolve' and t['targets']: raise ValueError('dissolve targets')
        for i in range(K):
            put(f'source:{j}:{i}',C.get((s,i),0)-sum(M[j,k] for k in t['children'] if ts[k]['source']==i))
            forest = sum(M[j,k]*F[k,i] for k in t['children'])
            put(f'forest:{j}:{i}',F[j,i]-(forest if r and r.kind=='dissolve' else branches.count(i)))
            for b,q in enumerate(branches): put(f'targetchild:{j}:{b}:{i}',C.get((q,i),0)-forest)
        zeros=set()
        for z in rules:
            if z.label!=label:continue
            if z.kind=='divide' and z.elementary and cs[s]['children']:continue
            if z.kind=='evolve' or (r is None and z.kind in ('out','dissolve','divide') and not(label=='skin' and z.kind in ('divide','dissolve'))): zeros.add(z.a)
        for k in t['children']:
            if ts[k]['mode']<0:
                lab=cs[ts[k]['source']]['label']
                zeros.update(z.a for z in rules if z.label==lab and z.kind=='in')
        if zeros:put(f'maximal:{j}',sum(U[j,a] for a in zeros))
        for a in range(d):
            demand=sum(M[j,k] for k in t['children'] if ts[k]['mode']>=0 and rules[ts[k]['mode']].kind=='in' and rules[ts[k]['mode']].a==a)
            local=int(r is not None and r.kind!='in' and r.a==a)
            consume=sum(E[j,z] for z in range(len(rules)) if (j,z) in E and rules[z].a==a)
            put(f'resource:{j}:{a}',U[j,a]+consume+local+demand-X[s,a])
            production=sum(E[j,z]*rules[z].out[a] for z in range(len(rules)) if (j,z) in E)
            inward=r.out[a] if r and r.kind=='in' else 0
            put(f'updated:{j}:{a}',Y[j,a]-U[j,a]-production-inward-sum(M[j,k]*O[k,a] for k in t['children']))
            upward=(Y[j,a]+r.out[a]) if r and r.kind=='dissolve' else r.out[a] if r and r.kind=='out' else 0
            put(f'upward:{j}:{a}',O[j,a]-upward)
            for b,q in enumerate(branches):
                extra=(r.out if b==0 else r.other)[a] if r and r.kind=='divide' else 0
                put(f'targetobject:{j}:{b}:{a}',X[q,a]-Y[j,a]-extra)
    config_seen=set()
    def cvisit(i):
        if i in config_seen:return
        config_seen.add(i)
        for k in cs[i]['children']:cvisit(k)
    root=ts[schema['root']]
    for i in [root['source']]+root['targets']:cvisit(i)
    if len(config_seen)!=K:raise ValueError('orphan configuration')
    assert max(p.degree for _,p in eq)<=2
    return eq,sorted(set(names))


def make_packet(root,rules,validate=True):
    fs,up,rec=expanded_oracle(root,rules,check=validate); plans={}; cfgs={}
    def cg(c):
        cfgs[ckey(c)]=c
        for z in c.children:cg(z)
    def pg(p):
        plans[pkey(p)]=p;cg(source(p))
        for z in rec[pkey(p)][3]:cg(z)
        for z in p.children:pg(z)
    pg(root)
    cl=sorted(cfgs.values(),key=lambda c:(height(c),ckey(c))); ci={ckey(c):i for i,c in enumerate(cl)}
    pl=sorted(plans.values(),key=lambda p:(height(p),pkey(p))); pi={pkey(p):i for i,p in enumerate(pl)}
    cs=[];ts=[];w={};d=len(root.x)
    for i,c in enumerate(cl):
        counts=Counter(ci[ckey(k)] for k in c.children);cs.append({'label':c.label,'children':sorted(counts)})
        for a,n in enumerate(c.x):w[f'x:{i}:{a}']=n
        for k,n in counts.items():w[f'c:{i}:{k}']=n-1
    for j,p in enumerate(pl):
        counts=Counter(pi[pkey(k)] for k in p.children);r=rules[p.mode] if p.mode>=0 else None
        u,y,o,f=rec[pkey(p)];targets=[] if r and r.kind=='dissolve' else [ci[ckey(c)] for c in f]
        ts.append({'source':ci[ckey(source(p))],'children':sorted(counts),'mode':p.mode,'targets':targets})
        for k,n in counts.items():w[f'm:{j}:{k}']=n-1
        for ri,z in enumerate(rules):
            if z.kind=='evolve' and z.label==p.label:w[f'e:{j}:{ri}']=dict(p.evolution).get(ri,0)
        for a in range(d):w[f'u:{j}:{a}']=u[a];w[f'y:{j}:{a}']=y[a];w[f'o:{j}:{a}']=o[a]
        fc=Counter(ci[ckey(c)] for c in f)
        for i in range(len(cl)):w[f'f:{j}:{i}']=fc[i]
    schema={'configs':cs,'transitions':ts,'root':pi[pkey(root)]}
    eq,vs=compile_schema(schema,rules,d)
    assert set(w)==set(vs)
    if validate: assert all(p.evaluate(w)==0 for _,p in eq)
    return {'schema':schema,'rules':[asdict(z) for z in rules],'alphabet_size':d,'witness':w,'ledger':{'variables':len(vs),'residuals':len(eq),'max_degree':max(p.degree for _,p in eq),'monomials':sum(len(p.t) for _,p in eq)},'output':ckey(fs[0]),'environment':up}


def enumerate_plans(c,rules,cap=100000):
    """All locally plausible schedules; expanded_oracle filters global admissibility."""
    children=[list(enumerate_plans(k,rules,cap)) for k in c.children]
    es=[i for i,r in enumerate(rules) if r.kind=='evolve' and r.label==c.label]
    modes=[-1]+[i for i,r in enumerate(rules) if r.kind!='evolve' and r.label==c.label and not(c.label=='skin' and r.kind in ('in','dissolve','divide')) and not(r.kind=='divide' and r.elementary and c.children)]
    ranges=[range(c.x[rules[i].a]+1) for i in es]
    total=0
    for ks in product(*children):
        for e in product(*ranges):
            for m in modes:
                total+=1
                if total>cap:raise ValueError('enumeration cap')
                yield Plan(c.label,c.x,ks,tuple((i,n) for i,n in zip(es,e) if n),m)

if __name__=='__main__':
    import sys
    print('Use replay_tests.py for the verified examples and finite exhaustive tests.')
