#!/usr/bin/env python3
"""Bounded exact high-layer scaled-auxiliary probe; no candidate graph.

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

# Retain seven drops from propagated upper bounds, without sharpening
# after cancellation. Only the separately exact full norms use sharp bounds.
# Thus all retained layers remain exact, even across the four U88 cancellations.
DROP=7
FULL88=HERE.parent/'thirteen-second-first-norm-corrections/polynomial88.json'
FULL88_PIN='32d896933d3f3a524adfad130bacddd5cb137bfe9438e62dfcfec570a8c0e8e1'
rows88={r[0]:r[1:] for r in pin(FULL88,FULL88_PIN)['source']}
def trim(p,d):return {m:c for m,c in p.items() if c and sum(m[:13])>=d-DROP}
def jp(p):
    d=degree(p);return (max(0,d),trim(p,max(0,d)))
def ja(a,b,sign=1):
    d=max(a[0],b[0]);return (d,trim(add(a[1],b[1],sign),d))
def jm(a,b):
    d=a[0]+b[0];out={};minimum=d-DROP
    require(time.monotonic()-START<25,'25-second elapsed cap')
    for ma,ca in a[1].items():
        for mb,cb in b[1].items():
            if sum(ma[:13])+sum(mb[:13])<minimum:continue
            m=tuple(x+y for x,y in zip(ma,mb));out[m]=out.get(m,0)+ca*cb
        require(len(out)<=25000,'25000-term jet cap')
    return (d,trim(out,d))
@lru_cache(None)
def jet(name):
    if isinstance(name,int):return jp(const(name))
    if name in ('N0','N1','Z'):return jp(value(name))
    if name=='zeta':return jp(add(sym('k'),sym('eta'),-1))
    if name in rows88:
        op,x,y=rows88[name];a,b=jet(x),jet(y)
        return jm(a,b)if op=='*'else ja(a,b,1 if op=='+'else-1)
    return jp(sym(name))
uj=jet('correctedU')
require(degree(uj[1])==44 and lead(uj[1])==u,'actual U88 retained leader')
# First remove its degree44 terms containing w^2 by the monomial P22.
q0={}
for m,c in u.items():
    if m[7]>=2:
        require(all(x>=y for x,y in zip(m,pm)),'initial monomial quotient')
        q0[tuple(x-y for x,y in zip(m,pm))]=-c
base=ja(uj,jm(jp(q0),jp(Pm)),-1)
require(all(m[7]==1 for m in lead(base[1])),'initial w-square cancellation')
Hlift=const(8)
for v,n in [(value('qm'),2),(value('kY'),2),(sym('f'),6),(sym('T'),4),
            (add(mul(sym('K0'),value('C')),sym('F'),-1),2)]:
    Hlift=mul(Hlift,power(v,n))
require(lead(Hlift)==H,'literal lift has prescribed leading component')
current=ja(jm(jp(A),base),jm(jp(Hlift),jp(S)),-1)
records=[{'stage':'scaled and first S correction','propagated_bound':current[0],
          'actual_retained_degree':degree(current[1]),'terms':len(current[1]),
          'leader':encoded(lead(current[1]))}]

# One bounded reduction at the next layer, with an explicit failure receipt.
# S21 = baseMonomial*(k-4gamma), where baseMonomial has coefficient -4.
def next_ideal_reduction(top):
    pquot={};rest={}
    for m,c in top.items():
        if all(x>=y for x,y in zip(m,pm)):
            pquot[tuple(x-y for x,y in zip(m,pm))]=-c
        else:rest[m]=c
    baseMon=list(ZERO)
    for name,n in [('J',13),('beta',13),('k',2),('s',4),('w',1)]:baseMon[NAMES.index(name)]=n
    divided={}
    for m,c in rest.items():
        if c%4 or not all(x>=y for x,y in zip(m,baseMon)):
            return None,{'reason':'not divisible by S common monomial','witness':[list(m),c]}
        divided[tuple(x-y for x,y in zip(m,baseMon))]=-c//4
    squot={};work=dict(divided)
    while any(m[10]>0 for m in work):
        m=max((m for m in work if m[10]>0),key=lambda m:(m[10],m))
        c=work[m];qm=list(m);qm[10]-=1;qm=tuple(qm)
        squot[qm]=squot.get(qm,0)+c
        work=add(work,mul({qm:c},A),-1)
    if work:return None,{'reason':'nonzero remainder modulo k-4gamma','remainder':encoded(work)}
    require(add(mul(pquot,lead(P)),mul(squot,lead(S)))==top,'full next-layer ideal identity')
    return (pquot,squot),None

deg=degree(current[1]);red,failure=next_ideal_reduction(lead(current[1]))
if red is not None:
    rp,rs=red
    current=ja(ja(current,jm(jp(rp),jp(Pm)),-1),jm(jp(rs),jp(S)),-1)
    records.append({'stage':'next complete homogeneous layer removed','correction_P':summary(rp),
       'correction_S':summary(rs),'propagated_bound':current[0],
       'actual_retained_degree':degree(current[1]),'terms':len(current[1]),
       'leader':encoded(lead(current[1]))})
require(current[0]-DROP<=degree(current[1]),'reported degree retained within exact window')
out={'scope':'Bounded leading-layer exploration, no candidate or paid schedule',
 'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 'parent_graph_sha256':GRAPH_PIN,'parent88_sha256':FULL88_PIN,'parent_certificate_sha256':CERT_PIN,
 'symbols':NAMES,'retained_drops':DROP,'initial_P_coefficient':summary(q0),
 'initial_S_coefficient_lift':summary(Hlift),'stages':records,'failed_next_reduction':failure,
 'remaining_requirements':['compact fully paid coefficient schedule','complete zero-set and specialized leader audit']}
print(json.dumps(out,indent=2))
