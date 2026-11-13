#!/usr/bin/env python3
"""Independent formal polynomial/JSON check; this does not invoke Lean."""
import hashlib, json
from pathlib import Path
root=Path(__file__).resolve().parents[2]
source=root/'research/trace74-direct-four-block-draft/Trace74DirectFourBlock.lean'
graph=root/'research/trace74-mask-coordinate-probe/candidate.json'
assert hashlib.sha256(source.read_bytes()).hexdigest()=='1405f58decb30ba349a3e0c7b5bc6afab01fbca4082e112fb513210336fa436e'
assert hashlib.sha256(graph.read_bytes()).hexdigest()=='dafefaa40173c9f75c414171896e19ddcf5f5eec82a0612d82a4e23988ee7353'
n=6; zero=(0,)*n
def con(x): return {zero:x} if x else {}
def var(i):
    a=[0]*n; a[i]=1; return {tuple(a):1}
def add(a,b):
    z=a.copy()
    for k,v in b.items(): z[k]=z.get(k,0)+v
    return {k:v for k,v in z.items() if v}
def neg(a): return {k:-v for k,v in a.items()}
def sub(a,b): return add(a,neg(b))
def mul(a,b):
    z={}
    for x,v in a.items():
        for y,w in b.items():
            k=tuple(i+j for i,j in zip(x,y)); z[k]=z.get(k,0)+v*w
    return {k:v for k,v in z.items() if v}
def power(a,n):
    r=con(1)
    for _ in range(n): r=mul(r,a)
    return r
b,j,f,c,m,h=map(var,range(n)); one=con(1)
q=add(mul(b,j),one)
rows=json.loads(graph.read_text())['source']
expected=[['bJ','*','beta','J'],['q','+','bJ',1],['q2','*','q','q'],['qmF','-','q','F'],['G1','*','q','qmF'],['G','-','G1','C'],['q2m1','-','q2',1],['Gq','*','G','q2m1'],['qMF','*','q','MF'],['MCqMF','+','MC','qMF'],['RJ','*','MCqMF','J'],['R','+','Gq','RJ']]
for row in expected: assert row in rows, row
env={'beta':b,'J':j,'F':f,'C':c,'MC':m,'MF':add(b,h)}
def get(x): return con(x) if isinstance(x,int) else env[x]
for name,op,x,y in expected:
    a,v=get(x),get(y)
    env[name]={'+':add,'-':sub,'*':mul}[op](a,v)
lhs=add(mul(sub(mul(q,sub(q,f)),c),sub(power(q,2),one)),mul(add(m,mul(q,add(b,h))),j))
rhs=add(add(add(add(sub(c,one),add(mul(m,j),one)),mul(q,add(f,sub(mul(h,j),one)))),mul(power(q,2),sub(q,c))),mul(power(q,3),sub(sub(q,one),f)))
assert env['q']==q and env['R']==lhs==rhs
print('PASS: exact free integer polynomial identity and external JSON rank cone with q=beta*J+1, MF=beta+HP')
print('Source-only polynomial check; no Lean replay, natural subtraction conversion, graph binding, or 74-zero deduction.')
