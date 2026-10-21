#!/usr/bin/env python3
"""Second, independently written forward audit of the compact proof DAG.

Terms here are nested Python tuples, not the generating/checking program's
interned term algebra. No proof search or unification is performed.
"""
import functools
import json
import sys
from collections import Counter
from pathlib import Path

T = 'T'
def I(x,y):
    return T if x == y == T else (x,y)

def parts(x):
    if x == T:
        return T,T
    assert isinstance(x,tuple) and len(x)==2
    return x

def apply(t,env):
    @functools.lru_cache(None)
    def go(x):
        if isinstance(x,tuple):
            return I(go(x[0]),go(x[1]))
        if isinstance(x,int):
            assert x in env, ('unassigned variable',x)
            return env[x]
        assert x == T
        return T
    return go(t)

def alpha(t):
    names={}
    @functools.lru_cache(None)
    def go(x):
        if isinstance(x,tuple):
            return I(go(x[0]),go(x[1]))
        if isinstance(x,int):
            if x not in names:
                names[x]=len(names)
            return names[x]
        assert x==T
        return T
    return go(t)

@functools.lru_cache(None)
def contains(t,u):
    return t==u or isinstance(t,tuple) and (contains(t[0],u) or contains(t[1],u))

def audit(path):
    data=json.loads(Path(path).read_text())
    assert data['format']=='term_dag_v1'
    terms=[]
    for i,t in enumerate(data['term_table']):
        if t==T:
            terms.append(T)
        elif isinstance(t,dict):
            assert set(t)=={'var'} and type(t['var'])==int and t['var']>=0
            terms.append(t['var'])
        else:
            assert isinstance(t,list) and len(t)==2
            assert all(type(j)==int and 0<=j<i for j in t)
            terms.append(I(terms[t[0]],terms[t[1]]))
    def ref(j):
        assert type(j)==int and 0<=j<len(terms)
        return terms[j]
    def env(e):
        assert all(k.isdigit() and str(int(k))==k for k in e)
        return {int(k):ref(v) for k,v in e.items()}
    proof=[];counts=Counter()
    for k,n in enumerate(data['nodes']):
        assert n['id']==k
        t=ref(n['term']);r=n['rule'];kind=r['kind'];counts[kind]+=1
        if kind=='truth':
            assert t==T
        elif kind=='dominated_rho8':
            left,right=parts(t);cu,a=parts(left);c,u=parts(cu)
            ac,bc=parts(right);a2,c2=parts(ac);b,c3=parts(bc)
            assert a==a2 and c==c2==c3, ('rho8',k)
            assert u==T or contains(a,u), ('domination',k)
        elif kind=='substitution':
            p=r['parent'];assert type(p)==int and 0<=p<k
            assert apply(proof[p],env(r['substitution']))==t, ('instance',k)
        else:
            assert kind in ('mp','mp_substitution')
            p,q=r['major'],r['minor'];assert all(type(j)==int and 0<=j<k for j in (p,q))
            major,minor=proof[p],proof[q]
            if kind=='mp_substitution':
                major=apply(major,env(r['major_substitution']))
                minor=apply(minor,env(r['minor_substitution']))
            premise,result=parts(major)
            assert premise==minor, ('MP premise',k)
            assert (alpha(result)==alpha(t) if kind=='mp_substitution' else result==t), ('MP result',k)
        proof.append(t)
    p,q,r=0,1,2
    goals={'I':I(p,p),'K':I(p,I(q,p)),'P':I(I(I(p,q),p),p),
           'cd59':I(I(p,q),I(I(I(p,r),p),q)),
           'B':I(I(p,q),I(I(q,r),I(p,r))),
           'S':I(I(p,I(q,r)),I(I(p,q),I(p,r)))}
    if 'rho8' in data['roots']:
        goals['rho8']=I(I(I(r,3),p),I(I(p,r),I(q,r)))
    assert set(data['roots'])==set(goals)
    for name,t in goals.items():
        root=data['roots'][name];assert type(root)==int and 0<=root<len(proof)
        assert alpha(proof[root])==alpha(t),('root',name)
    return {'verified':True,'proof_nodes':len(proof),'shared_terms':len(terms),
            'rules':dict(counts),'roots':data['roots'],
            'audit':'independent nested-tuple forward checker; no unification'}

if __name__=='__main__':
    print(json.dumps(audit(sys.argv[1]),indent=2))
