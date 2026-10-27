#!/usr/bin/env python3
"""Bounded exact P/Q/Z norm combinations, never the full auxiliary expansion.

The coordinate change k=eta+zeta is invertible (zeta=k-eta). It keeps total
unknown degree and makes the norm leading monomials small. Parent graph and
certificate are inert pinned data. No candidate or Lean source is written.
"""
from pathlib import Path
from functools import lru_cache
import hashlib,json,resource,time

resource.setrlimit(resource.RLIMIT_AS,(1024*1024**2,1024*1024**2))
resource.setrlimit(resource.RLIMIT_CPU,(30,30))
START=time.monotonic()
HERE=Path(__file__).resolve().parent
PARENT=HERE.parent/'thirteen-unit-sphere96/polynomial.json'
GRAPH_PIN='48573f58aac3d60f706eb7f52e92f5c061bd74d41ad7e9e9ee3e2ea43dcd9ca1'
CERT=HERE.parent/'thirteen-second-first-norm-corrections/CERTIFICATE.json'
CERT_PIN='b05205f7a5e40dcddf78d77fd6a170a79c4e0df45c3ba23c9bc8b68c3f44d3e5'
NAMES=['J','F','alpha','f','i','T','s','w','n','eta','k','m','gamma','beta','K0','MC','MF']
ZERO=(0,)*len(NAMES)

def require(ok,message):
    if not ok:raise ValueError(message)
def pin(path,want):
    raw=path.read_bytes();require(hashlib.sha256(raw).hexdigest()==want,'pin '+str(path));return json.loads(raw)
graph=pin(PARENT,GRAPH_PIN);prior=pin(CERT,CERT_PIN)
rows={r[0]:r[1:] for r in graph['source']}

def add(a,b,sign=1):
    out=dict(a)
    for m,c in b.items():out[m]=out.get(m,0)+sign*c
    return {m:c for m,c in out.items() if c}
def mul(a,b):
    require(time.monotonic()-START<25,'25-second elapsed cap')
    out={}
    for ma,ca in a.items():
        for mb,cb in b.items():
            m=tuple(x+y for x,y in zip(ma,mb));out[m]=out.get(m,0)+ca*cb
        require(len(out)<=25000,'25000-term cap')
    return {m:c for m,c in out.items() if c}
def const(c):return {ZERO:c} if c else {}
def sym(s):
    m=list(ZERO);m[NAMES.index(s)]=1;return {tuple(m):1}
def power(a,n):
    out=const(1)
    for _ in range(n):out=mul(out,a)
    return out
def degree(a):return max((sum(m[:13]) for m in a),default=-1)
def lead(a):
    d=degree(a);return {m:c for m,c in a.items() if sum(m[:13])==d}
def encoded(a):return [[list(m),c] for m,c in sorted(a.items())]
def summary(a):return {'degree':degree(a),'terms':len(a),'leader':encoded(lead(a))}
@lru_cache(None)
def value(name):
    if isinstance(name,int):return const(name)
    if name=='zeta':return add(sym('k'),sym('eta'),-1)
    if name in rows:
        op,x,y=rows[name];a,b=value(x),value(y)
        return mul(a,b) if op=='*' else add(a,b,1 if op=='+' else -1)
    return sym(name)

P,Q,Z=value('N0'),value('N1'),value('Z')
require((degree(P),degree(Q),degree(Z))==(22,18,36),'actual norm degrees')
Pm,Qm,Zm=add(P,const(1),-1),add(Q,const(1),-1),add(Z,const(1),-1)
S=add(mul(mul(const(8),sym('gamma')),Pm),mul(value('kY'),Qm))
expectedS=mul(mul(mul(mul(const(4),lead(value('E'))),lead(value('Y'))),
                  power(lead(value('kY')),2)),add(mul(const(4),sym('gamma')),sym('k'),-1))
require(degree(S)==21 and lead(S)==expectedS,'complete first syzygy leader')
D=add(mul(power(mul(value('hi'),value('kY')),2),Pm),Zm,-1)
expectedD=const(2)
for a,n in [(value('hi'),2),(value('E'),1),(value('Y'),1),(value('kY'),4)]:
    expectedD=mul(expectedD,power(lead(a),n))
require(degree(D)==34 and lead(D)==expectedD,'complete strong syzygy leader')

# Transform all302 terms of the previous degree44 leader to the k coordinate.
u={}
for m,c in prior['variants']['88']['exact_degree']['complete_corrected_auxiliary_leader']:
    term=const(c)
    for j,n in enumerate(m):
        base=add(sym('k'),sym('eta'),-1) if j==10 else sym(NAMES[j])
        if n:term=mul(term,power(base,n))
    u=add(u,term)
require(degree(u)==44,'invertible coordinate degree')
A=add(sym('k'),mul(const(4),sym('gamma')),-1)
C0=lead(value('C'));G0=add(mul(sym('K0'),C0),sym('F'),-1)
H=const(8)
for a,n in [(lead(value('qm')),2),(lead(value('kY')),2),
            (sym('f'),6),(sym('T'),4),(G0,2)]:H=mul(H,power(a,n))
scaled=mul(A,u)
remainder=add(scaled,mul(H,lead(S)),-1)
require(not any(m[7]<2 for m in remainder),'syzygy cancels all w-linear terms')

# The remaining degree45 component is a genuine polynomial multiple of P22.
pm,pc=next(iter(lead(P).items()))
require(len(lead(P))==1 and pc==-1,'monomial first-norm leader in new coordinates')
quot={}
for m,c in remainder.items():
    require(all(x>=y for x,y in zip(m,pm)),'polynomial quotient, no negative powers')
    quot[tuple(x-y for x,y in zip(m,pm))]=-c
require(mul(quot,lead(P))==remainder,'complete leading-ideal decomposition')
require(degree(quot)==23,'first-norm correction quotient degree')

out={'scope':'Exact small norm combinations and leading-ideal decomposition; no new candidate',
 'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 'graph_sha256':GRAPH_PIN,'certificate_sha256':CERT_PIN,'symbols':NAMES,
 'norms':{'P':summary(P),'Q':summary(Q),'Z':summary(Z)},
 'S':{'definition':'8*gamma*(P-1)+kY*(Q-1)',**summary(S)},
 'D':{'definition':'(b*i*kY)^2*(P-1)-(Z-1)',**summary(D)},
 'scaled_auxiliary_leader':{'A':'k-4*gamma','degree':45,'terms':len(scaled)},
 'S_multiplier_leader':summary(H),'P_multiplier_leader':summary(quot),
 'complete_decomposition':'A*lead44(U88)=H*lead21(S)+quot*lead22(P)',
 'remaining_requirements':['actual full lower-layer cancellation','fully paid schedule',
     'nonzero scale under Q=1 with positive variables','complete positive zero-set proof']}
print(json.dumps(out,indent=2))
