#!/usr/bin/env python3
"""Check all boundary identities over Z[beta, low, high], directly from Lean gates."""
import hashlib, json, re, sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('requires python3 -I -S -B')
r=Path(__file__).resolve().parents[2]
f=r/'research/p64-qcube72-free-main-candidate/P64QCube72Free.lean'
s=f.read_text().split('-- BEGIN GENERATED GRAPH',1)[1].split('-- END GENERATED GRAPH',1)[0]
rows=[]
for line in s.splitlines():
    if not line.strip(): continue
    m=re.fullmatch(r'  let (\w+) := (\w+) ([+*\-]) (\w+)',line)
    if not m: raise ValueError(('unparsed',line))
    n,x,op,y=m.groups(); rows.append((n,op,x,y))
if len(rows)!=72: raise ValueError('row count')
# Sparse integral polynomials, exponents index beta, low and high respectively.
zero={}; one={(0,0,0):1}; b={(1,0,0):1}; low={(0,1,0):1}; high={(0,0,1):1}
def add(a,b,sign=1):
    out=a.copy()
    for k,v in b.items():
        out[k]=out.get(k,0)+sign*v
        if out[k]==0: del out[k]
    return out
def mul(a,b):
    out={}
    for k,v in a.items():
        for l,w in b.items():
            m=tuple(i+j for i,j in zip(k,l)); out[m]=out.get(m,0)+v*w
    return {k:v for k,v in out.items() if v}
def value(d,key):
    return {(0,0,0):int(key)} if key.isdigit() and int(key) else ({} if key.isdigit() else d[key])
for J in (1,2):
    jb=b if J==1 else add(b,b)
    d={'beta':b,'MC':low,'MF':add(b,high),'K0':jb,'J':one if J==1 else add(one,one),'F':one,'alpha':add(jb,one,-1),'z':one,'f':one,'i':one,'T':one,'s':zero,'w':one,'t':one,'eta':zero,'zeta':one,'y':one,'h':zero}
    for n,op,x,y in rows:
        a,c=value(d,x),value(d,y)
        d[n]=mul(a,c) if op=='*' else add(a,c,-1 if op=='-' else 1)
    expected={'Y':zero,'U':zero,'ell':zero,'c':zero,'a':zero,'H':{(0,0,0):3},'Delta':{(0,0,0):3},'k':one,'A0':one,'M':zero,'W':zero,'Na':one,'Lt':zero,'polynomial':zero}
    for name,want in expected.items():
        if d[name]!=want: raise ValueError((J,name,d[name]))
print(json.dumps({'status':'PASS_EXACT_POLYNOMIAL_IDENTITIES','graph_gates':len(rows),'J_cases':[1,2],'domain':'integer polynomial ring in beta, low mask, high mask','scope':'boundary vector with three zero witnesses; no strictly positive solution','source_sha256':hashlib.sha256(f.read_bytes()).hexdigest()},sort_keys=True,indent=2))
