#!/usr/bin/env python3
"""Exact natural-domain graphs; standard-library symbolic audit."""
from pathlib import Path
from itertools import product
from collections import defaultdict
import json, math
HERE=Path(__file__).resolve().parent
def require(b,m):
    if not b: raise RuntimeError(m)
def A(a,b):return ['+',a,b]
def S(a,b):return ['-',a,b]
def M(a,b):return ['*',a,b]
def sq(a):return M(a,a)
def sum0(xs):
    r=0
    for x in reversed(xs):r=A(x,r)
    return r
def tree(e):return 1+tree(e[1])+tree(e[2]) if isinstance(e,list) else 0
def dag(e):
    seen=set()
    def walk(e):
        if isinstance(e,list):
            walk(e[1]);walk(e[2]);seen.add(json.dumps(e,separators=(',',':')))
    walk(e)
    return len(seen)
def padd(a,b):
    d=dict(a)
    for m,c in b.items():d[m]=d.get(m,0)+c
    return {m:c for m,c in d.items() if c}
def pmul(a,b):
    d=defaultdict(int)
    for ma,ca in a.items():
        for mb,cb in b.items():d[tuple(sorted(ma+mb))]+=ca*cb
    return {m:c for m,c in d.items() if c}
def poly(e):
    if isinstance(e,str):return {(e,):1}
    if isinstance(e,int):return {():e} if e else {}
    a,b=poly(e[1]),poly(e[2])
    if e[0]=='+':return padd(a,b)
    if e[0]=='-':return padd(a,{m:-c for m,c in b.items()})
    return pmul(a,b)
def val(e,v):
    if isinstance(e,str):return v[e]
    if isinstance(e,int):return e
    a,b=val(e[1],v),val(e[2],v)
    return a+b if e[0]=='+' else a-b if e[0]=='-' else a*b
def evpoly(p,v):return sum(c*math.prod(v[x] for x in m) for m,c in p.items())
def save(name,v):(HERE/name).write_text(json.dumps(v,indent=2)+'\n')
def pair_terms(z='z',a='a',b='b',t='t',s='s'):
    B=M(t,S(t,1))
    L=A(S(S(a,b),s),M(t,A(M(2,s),1)))
    E=A(S(M(4,S(S(z,a),b)),sq(A(A(a,b),s))),t)
    return [B,sq(L),sq(E)]
def pred_cubic(n='n',p='p',extra=()):
    factor=A(n,p)
    for x in extra:factor=A(factor,x)
    return M(factor,sq(S(S(n,p),1)))
def joint_terms(n='n',bit='bit',p='p'):
    return [sq(S(S(A(n,bit),p),1)),M(bit,p)]
records=[]
def add(name,inputs,aux,terms,degree,nonnegative=True):
    e=sum0(terms);pp=poly(e)
    deg=max((len(m) for m in pp),default=0)
    require(deg==degree,name+' degree')
    require(set(x for m in pp for x in m)==set(inputs+aux),name+' support')
    out={'name':name,'domain':'all visible and auxiliary coordinates in N, including zero; all subtraction is integer subtraction',
         'inputs':inputs,'auxiliaries':aux,'auxiliary_count':len(aux),'degree':deg,
         'nonnegative_on_natural_domain':nonnegative,'expression':e,
         'tree_binary_operations':tree(e),'shared_dag_binary_operations':dag(e),'monomials':len(pp),
         'expanded_terms':[{'monomial':list(m),'coefficient':str(c)} for m,c in sorted(pp.items())]}
    save(name+'.json',out);records.append(out)
    return e,pp
raw=M(A('n','p'),S(S('n','p'),1))
add('predecessor_quadratic_relation',['n','p'],[],[raw],2,False)
add('predecessor_sos_quartic',['n','p'],[],[sq(raw)],4)
add('predecessor_cubic',['n','p'],[],[pred_cubic()],3)
zero,_=add('zero_test_quadratic',['n','bit'],['p'],joint_terms(),2)
add('joint_zero_predecessor_quadratic',['n','bit','p'],[],joint_terms(),2)
add('predecessor_quadratic_with_bit',['n','p'],['bit'],joint_terms(),2)
for side in ['left','right']:
    add('tree_'+side+'_quartic',['n','a' if side=='left' else 'b'],['p','b' if side=='left' else 'a','t','s'],pair_terms('p')+[pred_cubic()],4)
if4,_=add('conditional_quartic',['n','a','b','c'],['s'],[M('n',sq(S('c','b'))),sq(M(S('c','a'),S(S('n','s'),1)))],4)
if3,_=add('conditional_cubic',['n','a','b','c'],['bit','p'],joint_terms()+[M('bit',sq(S('c','a'))),M('n',sq(S('c','b')))],3)
head,_=add('list_head_quartic',['n','c'],['p','a','b','t','s'],pair_terms('p')+[pred_cubic(extra=('c',)),M('n',sq(S(S('c','a'),1)))],4)

counts={}
for n,p in product(range(150),repeat=2):
    raw_value=(n+p)*(n-p-1)
    require((raw_value==0)==(p==max(n-1,0)),'raw predecessor')
    cp=(n+p)*(n-p-1)**2
    require(cp>=0 and (cp==0)==(p==max(n-1,0)),'cubic predecessor')
counts['predecessor_assignments']=150**2
for n,bit,p in product(range(35),repeat=3):
    z=(n+bit-p-1)**2+bit*p
    require(z>=0,'joint graph sign')
    require((z==0)==(bit==(1 if n==0 else 0) and p==max(n-1,0)),'joint exact graph')
    require(val(zero,locals())==z,'joint AST agreement')
counts['joint_graph_assignments']=35**3
for n,a,b,c,s in product(range(8),repeat=5):
    w=n*(c-b)**2+((c-a)*(n-s-1))**2
    require(w>=0,'if4 sign')
    if w==0:require(c==(a if n==0 else b),'if4 soundness')
    require(val(if4,locals())==w,'if4 AST agreement')
counts['conditional4_soundness']=8**5
for n,a,b in product(range(20),repeat=3):
    c=a if n==0 else b;s=max(n-1,0)
    require(val(if4,locals())==0,'if4 completeness')
    bit=1 if n==0 else 0;p=s
    require(val(if3,locals())==0,'if3 completeness')
counts['conditional_completeness']=20**3
for n,bit,p,a,b,c in product(range(6),repeat=6):
    w=(n+bit-p-1)**2+bit*p+bit*(c-a)**2+n*(c-b)**2
    require(w>=0,'if3 sign')
    if w==0:require(c==(a if n==0 else b),'if3 soundness')
counts['conditional3_soundness']=6**6
def pair(a,b):return b*b+a if a<b else a*a+a+b
def pairpoly(z,a,b,t,s):return t*(t-1)+(a-b-s+t*(2*s+1))**2+(4*(z-a-b)-(a+b+s)**2+t)**2
for a,b,n,c in product(range(14),range(14),range(200),range(16)):
    p=pair(a,b);t=0 if a>=b else 1;s=a-b if a>=b else b-a-1
    w=pairpoly(p,a,b,t,s)+(n+p+c)*(n-p-1)**2+n*(c-a-1)**2
    require(w>=0,'head sign')
    if w==0:require(p==max(n-1,0) and c==(0 if n==0 else a+1),'head decoded soundness')
counts['head_decoded_soundness']=14*14*200*16
for a,b in product(range(65),repeat=2):
    p=pair(a,b);n=p+1;c=a+1;t=0 if a>=b else 1;s=a-b if a>=b else b-a-1
    require(val(head,locals())==0,'head completeness')
require(val(head,{'n':0,'c':0,'p':0,'a':0,'b':0,'t':0,'s':0})==0,'head nil')
counts['head_completeness']=65**2+1

# Independently evaluate all sparse expansions at deterministic integer points.
for rec in records:
    pp={tuple(x['monomial']):int(x['coefficient']) for x in rec['expanded_terms']}
    for t in range(15):
        assignment={x:((i+2)*(t+3))%13-3 for i,x in enumerate(rec['inputs']+rec['auxiliaries'])}
        require(val(rec['expression'],assignment)==evpoly(pp,assignment),'sparse expansion agreement')
counts['sparse_expansion_points']=15*len(records)
metrics=[{k:r[k] for k in ['name','auxiliary_count','degree','tree_binary_operations','shared_dag_binary_operations','monomials']} for r in records]
save('CHECKS.json',{'status':'PASS','scope':'exact symbolic expansions and finite controls; universal proofs in PROOF.md; no entire checker polynomial',
 'counts':counts,'total_numeric_controls':sum(counts.values()),'gadgets':metrics})
print(json.dumps({'status':'PASS','total_numeric_controls':sum(counts.values()),'gadgets':metrics},indent=2))
