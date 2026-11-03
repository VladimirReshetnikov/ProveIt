#!/usr/bin/env python3
"""Read-only structural, coefficient and local polynomial identity checks."""
from collections import Counter
from hashlib import sha256
from pathlib import Path
import gzip, json, random, sys

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('invoke python3 -I -S -B without optimization')
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
OLD=ROOT/'con-zfc-diophantine-forms/163-trace-radical/compact/equations/trace75_degree402.json'
NEW=HERE/'candidate.json'
COEFF=ROOT/'candidates/ten-positive-qcube-product-square/coefficients'
PINS={OLD:'8b9b9421ae8a0762725852034b3db6d29b14660b3a4d0587e1494a933b5271c9',
      NEW:'dafefaa40173c9f75c414171896e19ddcf5f5eec82a0612d82a4e23988ee7353'}
def sha(d):return sha256(d).hexdigest()
def need(x,msg):
    if not x:raise RuntimeError(msg)
for path,h in PINS.items():need(sha(path.read_bytes())==h,'changed input: '+str(path))
o=json.loads(OLD.read_text());n=json.loads(NEW.read_text())
need(o['operations']==len(o['source'])==75,'old count')
need(n['operations']==len(n['source'])==74,'new count')
need(n['source_parent']['sha256']==PINS[OLD],'source pin')
need(n['witnesses']==['J','F','C','i','T','w','s','n','eta','zeta'],'witnesses')
need(o['witnesses']==['J','F','alpha','i','T','w','s','n','eta','zeta'],'old witnesses')
need(n['fixed_numerals']==o['fixed_numerals']==['beta','K0','MC','MF'],'ports')
need(n['coefficient_binding']==o['coefficient_binding'],'coefficient metadata changed')
need(n['output']==o['output']=='N','output')
need(Counter(r[1] for r in n['source'])=={'*':44,'+':16,'-':14},'new counts')
need(n['operation_breakdown']=={'*':44,'+':16,'-':14},'declared counts')

def graph(g):
    known=set(g['witnesses']+g['fixed_numerals']);d={}
    need(len(known)==14,'duplicate inputs')
    for row in g['source']:
        need(isinstance(row,list) and len(row)==4,'row format')
        name,op,a,b=row
        need(isinstance(name,str) and name not in known and op in ('+','-','*'),'row definition')
        for x in (a,b):need((type(x) is int and x>=0) or (isinstance(x,str) and x in known),'bad or forward operand')
        known.add(name);d[name]=(op,a,b)
    todo=[g['output']];live=set();inputs=set()
    while todo:
        x=todo.pop()
        if x in live:continue
        if x not in d:inputs.add(x);continue
        live.add(x)
        todo.extend(v for v in d[x][1:] if isinstance(v,str))
    need(live==set(d),'dead rows')
    need(inputs==set(g['witnesses']+g['fixed_numerals']),'dead inputs')
    return d
old_graph=graph(o);new_graph=graph(n)
oldrows={r[0]:r for r in o['source']};newrows={r[0]:r for r in n['source']}
need(oldrows['q']==['q','+','bJ',1] and oldrows['qmF']==['qmF','-','q','F'],'radix form')
need(oldrows['C']==['C','-','qmF','alpha'] and oldrows['G1']==['G1','*','bJ','qmF'] and oldrows['G']==['G','+','G1','alpha'],'old form')
need([r for r in o['source'] if 'alpha' in r[2:]]==[oldrows['C'],oldrows['G']],'alpha has other consumers')
need([r for r in o['source'] if 'G1' in r[2:]]==[oldrows['G']],'old G1 has other consumers')
expected=[]
for r in o['source']:
    if r[0]=='C':continue
    if r[0]=='G1':expected.append(['G1','*','q','qmF'])
    elif r[0]=='G':expected.append(['G','-','G1','C'])
    else:expected.append(r)
need(n['source']==expected,'unintended change or reordering')
# Sparse polynomials in Z[b,F,C] show old C=C and old G=new G exactly.
def add(a,b,sign=1):
    c=dict(a)
    for m,k in b.items():c[m]=c.get(m,0)+sign*k
    return {m:k for m,k in c.items() if k}
def mul(a,b):
    c={}
    for m,k in a.items():
        for v,l in b.items():
            t=tuple(i+j for i,j in zip(m,v));c[t]=c.get(t,0)+k*l
    return {m:k for m,k in c.items() if k}
one={(0,0,0):1};b={(1,0,0):1};f={(0,1,0):1};c={(0,0,1):1}
q=add(b,one);qmf=add(q,f,-1);alpha=add(qmf,c,-1)
need(add(qmf,alpha,-1)==c,'C identity')
need(add(mul(b,qmf),alpha)==add(mul(q,qmf),c,-1),'G identity')
# Induction over the verified rows gives equality of every shared observable
# register (G1 is private and differs); the old C row equals the new input.

def evaluate(rows,v,mod):
    v=dict(v)
    for x,op,a,b in rows:
        a=a if type(a) is int else v[a];b=b if type(b) is int else v[b]
        v[x]=({'+':lambda:a+b,'-':lambda:a-b,'*':lambda:a*b}[op]())%mod
    return v
rng=random.Random(675373);m=1000000007
for _ in range(100):
    v={x:rng.randrange(m) for x in n['witnesses']+n['fixed_numerals']}
    v0=dict(v);v0['alpha']=(v['beta']*v['J']+1-v['F']-v['C'])%m
    a=evaluate(o['source'],v0,m);z=evaluate(n['source'],v,m)
    for name in old_graph:
        if name!='G1':need(a[name]==z[name],'register sample: '+name)
# The inherited compressed parents are available in the repo. Verify their
# stored byte hashes and raw little-endian values against the exact metadata.
values={};payload={}
for port,item in n['coefficient_binding']['ports'].items():
    data=(COEFF/item['file']).read_bytes();raw=gzip.decompress(data)
    need(sha(data)==item['parent_gzip_sha256'],'parent gzip '+port)
    need(sha(raw)==item['raw_sha256'],'raw coefficient '+port)
    values[port]=int.from_bytes(raw,'little')
    need(values[port].bit_length()==item['bits'],'bit count '+port)
    payload[port]=item['raw_sha256']
need(values['beta']>=31 and values['beta']%2==1 and values['K0']>0,'basic fixed-port bounds')
need(0<values['MC']<values['beta']<values['MF']<2*values['beta'],'mask bounds')
for path,h in PINS.items():need(sha(path.read_bytes())==h,'input changed during run')
print(json.dumps({'status':'PASS','parent_sha256':PINS[OLD],'candidate_sha256':PINS[NEW],
 'old_live_rows':len(old_graph),'new_live_rows':len(new_graph),'live_inputs':14,
 'new_operations':dict(sorted(Counter(r[1] for r in n['source']).items())),
 'samples':100,'raw_coefficient_sha256':payload,
 'scope':'all-ring coordinate identity externally checked; positivity converse and iPRA unproved'},sort_keys=True))
