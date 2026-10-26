#!/usr/bin/env python3
"""Exact independent algebra and finite recurrence fixtures for Omega_1.

The unbounded implication is in LINEAR_ORIENTATION.md, not proved by tests.
No builder is imported here.
"""
from pathlib import Path
from collections import defaultdict
import json, hashlib

ROOT=Path(__file__).resolve().parents[1]
OLD=ROOT/'sources/joint209.json'
NEW=ROOT/'sources/joint209_linear_orientation.json'
def need(c,msg):
    if not c:raise ValueError(msg)
def add(*ps):
    z=defaultdict(int)
    for p in ps:
        for m,c in p.items():z[m]+=c
    return {m:c for m,c in z.items() if c}
def neg(p):return {m:-c for m,c in p.items()}
def mul(a,b):
    z=defaultdict(int)
    for m,c in a.items():
        for n,d in b.items():z[tuple(sorted(m+n))]+=c*d
    return {m:c for m,c in z.items() if c}
def sq(a):return mul(a,a)
def C(k):return {():k} if k else {}
def expand(doc):
    vals=[];last=max(doc['residual_nodes'])
    for i,n in enumerate(doc['nodes'][:last+1]):
        op=n[0]
        if op=='const':v=C(n[1])
        elif op=='var':v={(n[1],):1}
        else:
            need(0<=n[1]<i and 0<=n[2]<i,'topological nodes')
            a,b=vals[n[1]],vals[n[2]]
            v=mul(a,b) if op=='mul' else add(a,b if op=='add' else neg(b))
        vals.append(v)
    return vals
def check(old,new):
    for k in ['variables','removed_rows','removed_variables','residual_info','source_sha256']:
        need(old[k]==new[k],('retained interface',k))
    o=expand(old);n=expand(new)
    need([o[i] for i in old['residual_nodes'][:-1]]==
         [n[i] for i in new['residual_nodes'][:-1]],'all retained rows exact')
    unique=[];seen=set()
    for r in old['ports']['requests']:
        key=(r['D'],r['Y'],r['Z'])
        if key not in seen:seen.add(key);unique.append(r)
    omega=C(len(unique));diff={}
    for r in unique:
        X=add(o[r['D']],o[r['Z']]);dk=add(o[r['Y']],neg(o[r['k']]))
        omega=add(omega,neg(X),sq(dk))
        diff=add(diff,X,neg(sq(X)))
    need(omega==n[new['ports']['Omega']],'literal linear sign penalty')
    need(add(omega,neg(o[old['ports']['Omega']]))==diff,'exact numerator difference')
    prod=C(1)
    for i in old['ports']['T']:prod=mul(prod,o[i])
    oldr=o[old['residual_nodes'][-1]];newr=n[new['residual_nodes'][-1]]
    need(add(newr,neg(oldr))==mul(diff,prod),'exact entire joint replacement')
    need(max(map(len,newr))==13,'joint residual degree')
    need({m:c for m,c in oldr.items() if len(m)==13}==
         {m:c for m,c in newr.items() if len(m)==13},'unchanged degree13 part')
    # Verify literal sum-of-squares output by a small abstract expansion.
    roots=new['residual_nodes'];cut={r:{(i,):1} for i,r in enumerate(roots)}
    memo={}
    def abstract(i):
        if i in cut:return cut[i]
        if i in memo:return memo[i]
        q=new['nodes'][i]
        need(q[0] in ['const','add','sub','mul'],'unexpected leaf after residual cuts')
        if q[0]=='const':v=C(q[1])
        else:
            a,b=abstract(q[1]),abstract(q[2])
            v=mul(a,b) if q[0]=='mul' else add(a,b if q[0]=='add' else neg(b))
        memo[i]=v;return v
    need(abstract(new['root'])=={(i,i):1 for i in range(len(roots))},'exact SOS output')
    return {'pairs':len(unique),'variables':len(new['variables']),
            'rows':len(roots),'joint_residual_terms':len(newr),
            'old_joint_residual_terms':len(oldr),'joint_degree':13,'polynomial_degree':26}

def pell(a,n):
    x,y=1,0
    for _ in range(abs(n)):x,y=a*x+(a*a-1)*y,x+a*y
    return x,y if n>=0 else -y

def fixtures():
    count=0
    for a in list(range(-7,-1))+list(range(2,8)):
        for nu in range(-8,9):
            x,y=pell(a,nu)
            need(x*x-(a*a-1)*y*y==1,'Pell norm')
            for eps in [-1,1]:
                for k in range(-8,9):
                    big=1-eps*x+(eps*y-k)**2
                    small=1-eps+(eps*nu-k)**2
                    need((big-small)%(a-1)==0,'orientation congruence fixture')
                    need((small==0)==(eps==1 and nu==k),'nonnegative separation fixture')
                    count+=1
    return count

def main():
    old=json.loads(OLD.read_text());new=json.loads(NEW.read_text())
    need(hashlib.sha256(OLD.read_bytes()).hexdigest()==
         '9bd9f942016c0966b7b73c82fe4ecf394732ebecfd2469484429f7294fde9156','frozen old joint')
    result=check(old,new);result['recurrence_fixtures']=fixtures()
    result['status']='PASS';result['new_sha256']=hashlib.sha256(NEW.read_bytes()).hexdigest()
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
