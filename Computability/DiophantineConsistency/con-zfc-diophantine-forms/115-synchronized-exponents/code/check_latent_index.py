#!/usr/bin/env python3
"""Independent finite audit of latent-index raw rows; no producer imports."""
from collections import defaultdict
from hashlib import sha256
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / 'direct/raw_complete.json'
raw = SOURCE.read_bytes()
d = json.loads(raw)
rows = d['rows']
gates = {r['gate']: r for r in rows if r.get('gate') is not None}
names = {v['name']: i for i, v in enumerate(d['variables'])}

def need(ok, msg):
    if not ok:
        raise ValueError(msg)

def clean(p):
    return {m:c for m,c in p.items() if c}

def add(*ps):
    z=defaultdict(int)
    for p in ps:
        for m,c in p.items(): z[m]+=c
    return clean(z)

def scale(c,p): return clean({m:c*v for m,v in p.items()})
def mul(*ps):
    z={():1}
    for p in ps:
        q=defaultdict(int)
        for m,c in z.items():
            for n,e in p.items(): q[tuple(sorted(m+n))]+=c*e
        z=clean(q)
    return z

def var(i): return {(i,):1}
def atom(a): return {():a[1]} if a[0]=='c' else var(a[1])

def expander(stops):
    memo={i:var(i) for i in stops}
    active=set()
    def v(i):
        if i in memo:return memo[i]
        if i not in gates:return var(i)
        need(i not in active, 'cyclic raw gate')
        active.add(i)
        terms=gates[i]['terms']
        own=sum(c for c,m in terms if m==[i])
        need(own==1, 'nonmonic raw gate')
        need(all(i not in m or m==[i] for c,m in terms), 'nonlinear own gate')
        out=scale(-1, add(*(scale(c,mul(*(v(j)for j in m)))
                         for c,m in terms if m!=[i])))
        active.remove(i);memo[i]=out
        return out
    def row(r):return add(*(scale(c,mul(*(v(j)for j in m)))for c,m in r['terms']))
    return v,row

def named(label):
    rs=[r for r in rows if r['label']==label]
    need(len(rs)==1,'unique row '+label)
    return rs[0]

rho=d['rho'][1]
T=d['factorials'][0]['output'][1]
H=d['factorials'][0]['input'][1]
t=d['factorials'][1]['input'][1]
e=d['powers'][0]['exponent'][1]
M=d['powers'][0]['output'][1]
R=d['powers'][1]['base'][1]
W,A,Z=[a[1]for a in d['scale']]
U,V,B=[a[1]for a in d['auxiliary']]

v,rr=expander({T})
need(v(rho)==mul(var(T),var(T)), 'rho exactly T squared')
need(any(p['base']==['v',T] and p['exponent']==['v',t] for p in d['powers']), 'T is a power base at exponent t')
rho_plus=[p['base'][1]for p in d['powers'] if p['base'][0]=='v' and
          expander({rho})[0](p['base'][1])==add(var(rho),{():1})]
need(bool(rho_plus), 'rho+1 is a power base')

need(d['powers'][1]['exponent']==['v',e] and d['powers'][1]['output']==['v',H], 'carrier and H share one exponent')
need(expander({t})[0](e)==scale(4194304,var(t)), 'e is 2^22 times t')
need(expander({names['t0']})[0](t)==add(var(names['t0']),{():2}), 't=t0+2')
need(expander({t,names['x'],names['y'],names['M0']})[0](R)==
     add({():2},var(t),var(names['x']),var(names['y']),var(names['M0'])), 'R definition')

power_atoms={tuple(p[k])for p in d['powers']for k in ('base','exponent','output')}
stops={a[1]for a in power_atoms if a[0]=='v'}|{W}
_,rr=expander(stops)
need(rr(named('shared.frame_definition'))==add(var(W),{():-2},
      *(scale(-1,atom(a))for a in power_atoms)), 'frame includes exact distinct power atoms')

seedmap={tuple(x['exponent']):x['pair']for x in d['seeds']}
indexmap={tuple(x['exponent']):x['pair']for x in d['indices']}
need(('v',rho)in seedmap,'latent rho is a genuine seed')
need(not any(p['exponent']==['v',rho]for p in d['powers']), 'rho is actually latent')
Ys=[p[1][1]for p in seedmap.values()]
qm1=names['shared_index.Vquotient_minus1']
_,rr=expander(set(Ys)|{V,qm1})
yp=mul(*(mul(var(y),var(y))for y in Ys))
need(rr(named('shared_index.V_positive_product'))==
     add(var(V),scale(-1,mul(yp,add(var(qm1),{():1})))),
     'common auxiliary product includes every seed ordinate squared')

D=d['discriminant'][1]
_,rr=expander({A,D})
need(rr(named('index_addition.D_definition'))==add(mul(var(A),var(A)),scale(-1,var(D)),{():-1}),
     'addition discriminant D=A squared minus one')
known=set(seedmap)
checked=[]
for deriv in d['derivations']:
    target=tuple(deriv['target'])
    if deriv['kind']=='sum':
        sources=[tuple(x)for x in deriv['sources']]
        need(all(x in known for x in sources),'sum derivation is acyclic')
        p1,p2=[indexmap[x]for x in sources]
        x,y,u,w=[a[1]for a in p1+p2]
        ev,_=expander({x,y,u,w,D})
        wantx=add(mul(var(x),var(u)),mul(var(D),var(y),var(w)))
        wanty=add(mul(var(x),var(w)),mul(var(y),var(u)))
        need(ev(deriv['pair'][0][1])==wantx and ev(deriv['pair'][1][1])==wanty,
             'literal sum addition identities')
        ex,_=expander({s[1]for s in sources})
        need(ex(target[1])==add(*(atom(s)for s in sources)), 'target exponent is source sum')
    elif deriv['kind']=='shift':
        source=tuple(deriv['source']);need(source in known,'shift derivation is acyclic')
        need(deriv['shift']==1, 'inspected shift is one')
        x,y=[a[1]for a in indexmap[source]]
        ev,_=expander({x,y,A,D})
        need(ev(deriv['pair'][0][1])==add(mul(var(x),var(A)),mul(var(D),var(y))) and
             ev(deriv['pair'][1][1])==add(var(x),mul(var(y),var(A))),
             'literal shift addition identities')
        ex,_=expander({source[1]})
        need(ex(target[1])==add(atom(source),{():1}), 'target exponent is source plus one')
    else: raise ValueError('unreviewed derivation kind')
    known.add(target);checked.append(deriv['kind'])
need(known==set(indexmap),'all indices accounted for by seeds and acyclic additions')

receipt=dict(status='PASS',scope='Exact raw polynomial identities and acyclic index inventory; no producer imports; not the unbounded semantic proof',
             source=str(SOURCE.relative_to(ROOT)),source_sha256=sha256(raw).hexdigest(),
             power_calls=len(d['powers']),seeds=len(seedmap),indices=len(indexmap),
             latent_seed=rho,derived_indices=checked,
             checks=['rho=T^2','T base present','rho+1 base present','t=t0+2','common exponent=2^22*t',
                     'R definition','exact frame atom sum','latent rho certified','complete seed ordinate product',
                     'D=A^2-1','all three literal Pell additions','acyclic index ledger'])
out=ROOT/'checks/LATENT_INDEX.json'
out.write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
