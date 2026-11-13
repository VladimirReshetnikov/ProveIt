#!/usr/bin/env python3
"""Independent, finite, no-Lean check of the rational rank rewrite."""
import gzip
import hashlib
import json
import math
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
RESEARCH = HERE.parents[1] / 'research'
NEW = RESEARCH / 'normalized106-rational66'
OLD = RESEARCH / 'fourteen-normalized-product106'
PIN = {'new': '61784a1cdc3594174c3e321712322cebdffff20be51ef7f2bc0feb3b8f9498a4',
       'old': '0485cd1e884b918d766261b1780be117238f0813a965c6d8ae4d805176a5f6e1',
       'cert': '16358ce2d453371d2f2d1cad8ab22136ea61ec9ff77200a55264ad56d4a57879',
       'author': '082d6634b57ed71f8c61a466a05a0dc09bf8577685a45747b4e4249ff259836a'}
def sha(b): return hashlib.sha256(b).hexdigest()
def read(path, expected):
    b = path.read_bytes()
    if sha(b) != expected: raise ValueError('hash mismatch: ' + str(path))
    return json.loads(b)
def need(v, why):
    if not v: raise ValueError(why)

old = read(OLD / 'polynomial.json', PIN['old'])
new = read(NEW / 'polynomial.json', PIN['new'])
cert = read(OLD / 'CERTIFICATE.json', PIN['cert'])
reported = read(NEW / 'result.json', PIN['author'])
need(cert['graph_sha256'] == PIN['old'] and cert['degree']['exact_degree'] == 106, 'parent degree binding')
need(new['witnesses'] == old['witnesses'] and len(new['witnesses']) == len(set(new['witnesses'])) == 14, 'witness list')
need(new['output'] == old['output'] == 'polynomial', 'output')
need(new['derived_rational_leaves'] == {'Urank': {'numerator':'MF', 'denominator':'beta'}}, 'rational port')
need(new['derived_integer_leaves'] == {'Wrank': 'MC-MF'}, 'integer port')
need(new['coefficient_binding'] == old['coefficient_binding'], 'port binding metadata')
need(new['fixed_runtime_leaves'] == ['beta', 'K0', 'Urank', 'Wrank'], 'leaf list')
a, b = old['source'], new['source']
start = next(i for i, r in enumerate(a) if r[0] == 'q2minus1')
end = next(i for i, r in enumerate(a) if r[0] == 'R')
start2 = next(i for i, r in enumerate(b) if r[0] == 'q2minus1')
end2 = next(i for i, r in enumerate(b) if r[0] == 'R')
need(a[:start] == b[:start2] and a[end+1:] == b[end2+1:], 'unchanged rows differ')
need(a[:3] == [['qm','*','beta','J'],['q','+','qm',1],['q2','*','q','q']], 'q substitution')
need(a[start:end+1] == [['q2minus1','-','q2',1],['rproduct','*','gap','q2minus1'],
  ['qMF','*','q','MF'],['maskfactor','+','MC','qMF'],['mask','*','maskfactor','J'],['R','+','rproduct','mask']], 'old rank rows')
need(b[start2:end2+1] == [['q2minus1','-','q2',1],['shifted_gap','+','gap','Urank'],
  ['rank_product','*','q2minus1','shifted_gap'],['rank_linear','*','J','Wrank'],['R','+','rank_product','rank_linear']], 'new rank rows')

# Verify beta*(new rank-old rank)=0 exactly as a polynomial in formal
# beta,J,gap,MC,MF, after the graph's substitution q=1+beta*J.
z=(0,0,0,0,0)
def add(*ps):
    o={}
    for p in ps:
        for k,v in p.items(): o[k]=o.get(k,0)+v
    return {k:v for k,v in o.items() if v}
def neg(p): return {k:-v for k,v in p.items()}
def mul(p,q):
    o={}
    for a,x in p.items():
        for b,y in q.items():
            k=tuple(i+j for i,j in zip(a,b));o[k]=o.get(k,0)+x*y
    return {k:v for k,v in o.items() if v}
one={z:1}
def var(i):
    t=list(z);t[i]=1;return {tuple(t):1}
B,J,G,C,F=(var(i) for i in range(5))
q=add(one,mul(B,J)); q2m=add(mul(q,q),neg(one))
scaled_new=add(mul(q2m,add(mul(B,G),F)),mul(mul(B,J),add(C,neg(F))))
scaled_old=mul(B,add(mul(G,q2m),mul(J,add(C,mul(q,F)))))
need(add(scaled_new,neg(scaled_old)) == {}, 'symbolic rank identity')

ports={}
for name, meta in old['coefficient_binding']['ports'].items():
    compressed=(OLD/'coefficients'/meta['file']).read_bytes()
    raw=gzip.decompress(compressed)
    need(sha(compressed)==meta['gzip_sha256'] and sha(raw)==meta['raw_sha256'] and len(raw)==meta['raw_bytes'], 'port '+name)
    n=int.from_bytes(raw,'big');need(n.bit_length()==meta['bits'], 'port bits '+name);ports[name]=n
beta,mc,mf=ports['beta'],ports['MC'],ports['MF']
need(beta>0 and beta<mf<2*beta, 'beta and MF bounds')
gcd=math.gcd(beta,mf)
values={'beta':beta,'K0':ports['K0'],'Urank_numerator':mf//gcd,
        'Urank_denominator':beta//gcd,'Wrank':mc-mf}
need(values['Urank_denominator']>1, 'fraction is integral')
sizes={}
for name,value in values.items():
    bits=abs(value).bit_length();raw=abs(value).to_bytes((bits+7)//8,'big')
    sizes[name]={'bits':bits,'raw_magnitude_bytes':len(raw),'sha256':sha(raw),'negative':value<0}
need(sizes == reported['fixed_leaf_magnitudes'], 'leaf sizes or signs')
need(sum(v['raw_magnitude_bytes'] for v in sizes.values()) == 53223, 'storage sum')

known=set(new['witnesses']+new['fixed_runtime_leaves']); nodes={}
for name,op,x,y in b:
    need(name not in known and op in '+-*' and all(isinstance(t,int) or t in known for t in (x,y)), 'bad topology')
    nodes[name]=(op,x,y);known.add(name)
live=set();leaves=set();todo=[new['output']]
while todo:
    x=todo.pop()
    if isinstance(x,int): continue
    if x in nodes:
        if x not in live: live.add(x);todo.extend(nodes[x][1:])
    else:leaves.add(x)
counts=dict(Counter(nodes[x][0] for x in live))
need(len(b)==len(live)==66 and counts=={'*':37,'+':16,'-':13}, 'gate count/liveness')
need(leaves==set(new['witnesses']+new['fixed_runtime_leaves']), 'input liveness')
print(json.dumps({'status':'PASS','graph_sha256':PIN['new'],'parent_sha256':PIN['old'],
 'parent_degree_certificate_sha256':PIN['cert'],'witnesses':14,'gates':66,'counts':counts,
 'nonintegral_fixed_rational_leaf':True,'fixed_magnitudes':sizes,'raw_separate_bytes':53223,
 'scope':'external exact rational identity and historical degree inheritance; no Lean or new iPRA proof'},sort_keys=True))
