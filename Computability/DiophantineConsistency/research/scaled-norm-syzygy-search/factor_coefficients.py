#!/usr/bin/env python3
"""Small exact invertible cut substitution for prospective correction coefficients.
No equation/Lean source is generated; this is data-only symbolic exploration.
"""
import hashlib,json,resource
from pathlib import Path
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
resource.setrlimit(resource.RLIMIT_CPU,(20,20))
HERE=Path(__file__).resolve().parent
SOURCE=HERE/'SCALED_LAYERS.json'
# Set by the author after the complete preceding bounded check.
PIN='379d71b2d605e461c549652c9d6f655516d9b2b1e3721add43d3093f3712d084'
NAMES=['B','C','G','f','i','T','s','w','n','eta','k','m','gamma','unused_beta','K0','MC','MF']
ZERO=(0,)*17
def require(b,m):
    if not b:raise ValueError(m)
def add(a,b,k=1):
    d=dict(a)
    for m,c in b.items():d[m]=d.get(m,0)+k*c
    return {m:c for m,c in d.items() if c}
def mul(a,b):
    d={}
    for m,c in a.items():
        for n,e in b.items():
            q=tuple(x+y for x,y in zip(m,n));d[q]=d.get(q,0)+c*e
    require(len(d)<=10000,'small term cap')
    return {m:c for m,c in d.items() if c}
def const(c):return {ZERO:c}if c else{}
def sym(i):
    m=list(ZERO);m[i]=1;return{tuple(m):1}
def power(a,n):
    p=const(1)
    for _ in range(n):p=mul(p,a)
    return p
raw=SOURCE.read_bytes();require(hashlib.sha256(raw).hexdigest()==PIN,'layer pin')
data=json.loads(raw)
# The exact invertible linear change is F=K0*C-G and alpha=B-F-C.
# All original J/beta exponents occur equally, allowing the cut B=beta*J.
F=add(mul(sym(14),sym(1)),sym(2),-1)
alpha=add(add(sym(0),F,-1),sym(1),-1)
def transform(rows):
    out={}
    for m,c in rows:
        require(m[0]==m[13],'B substitution has balanced beta exponent')
        q=const(c)
        for j,n in enumerate(m):
            if j==13:continue
            if n:q=mul(q,power(F if j==1 else alpha if j==2 else sym(j),n))
        out=add(out,q)
    return out
def encode(p):return [[list(m),c]for m,c in sorted(p.items())]
items={'q0':data['initial_P_coefficient']['leader'],
       'rp':data['stages'][1]['correction_P']['leader'],
       'rs':data['stages'][1]['correction_S']['leader']}
result={}
for label,rows in items.items():
    p=transform(rows)
    groups={}
    for m,c in p.items():
        key=(m[3],m[5])
        groups.setdefault(key,{})[m]=c
    result[label]={'terms':len(p),'polynomial':encode(p),
      'groups_by_f_T':[{'f':f,'T':t,'terms':len(q),'polynomial':encode(q)}for(f,t),q in sorted(groups.items())]}
print(json.dumps({'scope':'Exact cut transforms, not a paid candidate',
 'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 'input_sha256':PIN,'symbols':NAMES,'coefficients':result},indent=2))
