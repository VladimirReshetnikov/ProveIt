#!/usr/bin/env python3
"""Search certified acyclic unit-coefficient row eliminations of P207.

The elimination method is inherited from ProveIt report 152. This program
searches applications to the new oriented pooling equation. Its output is
a reproducible pivot list, not a proof of global minimality.
"""
from pathlib import Path
import json,random,sys,hashlib,argparse

ROOT=Path(__file__).resolve().parent
SOURCE=ROOT/'source216.json'
S=json.loads(SOURCE.read_text())
ROWS=S['residuals']
REMOVED_V={141,142,143,144,145,146,212,213,214,215}
REMOVED_R={97,98,99,100,101,102,149,150,151,152}
ACTIVE=[i for i in range(217) if i not in REMOVED_V]
KEEP_ROWS=[i for i in range(len(ROWS)) if i not in REMOVED_R]
BASE_SOURCE=ROOT/'source207.json'
EXTRA_COUNT=1
_extra_degree_evaluator=None

# A structural expression tree for the single new residual.
def var(i):return ('v',i)
def cn(i):return ('c',i)
def add(*args):
    if not args:return cn(0)
    out=args[0]
    for x in args[1:]:out=('+',out,x)
    return out
def mul(*args):
    if not args:return cn(1)
    out=args[0]
    for x in args[1:]:out=('*',out,x)
    return out
def sub(a,b):return ('-',a,b)
def square(a):return mul(a,a)
def port(i,offset=0):return add(var(i),cn(offset)) if offset else var(i)

PARAM=port(134,1)
BASES=[var(0),var(4),var(186),port(94,-1),var(94)]
REQUESTS=[
    (0,var(3),var(138),var(139),var(140)),
    (1,var(17),var(174),var(175),port(176,1)),
    (2,port(94,-1),var(174),var(175),port(176,1)),
    (4,var(95),var(147),var(148),var(149)),
    (3,var(96),var(138),var(139),var(140)),
    (4,var(100),var(150),port(151,-1),var(152)),
    (4,var(103),var(153),var(154),var(155)),
    (4,var(106),var(156),var(157),var(158)),
    (4,var(109),var(159),var(160),var(161)),
    (4,var(112),var(162),var(163),var(164)),
    (3,var(113),var(165),var(166),var(167)),
    (4,var(116),var(168),var(169),var(170)),
    (4,var(119),var(171),var(172),var(173)),
    (3,var(120),var(174),var(175),port(176,1)),
    (4,var(124),var(177),var(178),var(179)),
    (4,var(127),var(180),var(181),var(182)),
    (4,var(130),var(183),var(184),var(185)),
]
MODULI=[sub(sub(mul(cn(2),PARAM,n),square(n)),cn(1)) for n in BASES]
ERRORS=[]
for j,n in enumerate(BASES):
    rr=[(m,d,y,z) for b,m,d,y,z in REQUESTS if b==j]
    sm=add(*(sub(square(sub(m,d)),square(y)) for m,d,y,z in rr))
    hm=add(*(mul(y,sub(sub(m,d),z)) for m,d,y,z in rr))
    ERRORS.append(sub(sm,mul(cn(2),n,hm)))
POOL=sub(add(*(mul(BASES[j],ERRORS[j],*(MODULI[k] for k in range(5) if k!=j))
               for j in range(5))),mul(var(216),*MODULI))

POOL_NODES=[];_pool_table={}
def _pack(e):
    if e in _pool_table:return _pool_table[e]
    if e[0] in ('v','c'):n=e
    else:n=(e[0],_pack(e[1]),_pack(e[2]))
    i=len(POOL_NODES);POOL_NODES.append(n);_pool_table[e]=i;return i
POOL_ROOT=_pack(POOL)

def pool_degree(degree):
    result=[]
    for n in POOL_NODES:
        if n[0]=='v':d=degree[n[1]]
        elif n[0]=='c':d=0
        elif n[0]=='*':d=result[n[1]]+result[n[2]]
        else:d=max(result[n[1]],result[n[2]])
        result.append(d)
    return result[POOL_ROOT]

def configure(basepath):
    global BASE_SOURCE,ACTIVE,EXTRA_COUNT,_extra_degree_evaluator,KEEP_ROWS,REMOVED_R,REMOVED_V,CANDIDATES
    BASE_SOURCE=Path(basepath)
    data=json.loads(BASE_SOURCE.read_text());mapped=[];synthetic=216
    for v in data['variables']:
        old=v.get('source_index')
        if old is None:old=synthetic;synthetic+=1
        mapped.append(old)
    ACTIVE=mapped;nodes=data['nodes']
    KEEP_ROWS=[meta['parent_row'] for meta in data['residual_info'] if meta['parent_row'] is not None]
    REMOVED_R=set(range(len(ROWS)))-set(KEEP_ROWS)
    REMOVED_V=set(range(216))-set(ACTIVE)
    CANDIDATES=[]
    for r in KEEP_ROWS:
        terms=ROWS[r]['terms']
        for c,m in terms:
            if len(m)!=1 or abs(c)!=1:continue
            v=m[0]
            if v not in ACTIVE or any(v in mm for cc,mm in terms if mm!=[v]):continue
            expression=[(-c*cc,tuple(mm)) for cc,mm in terms if mm!=[v]]
            CANDIDATES.append((r,v,expression))
    roots=[r for r,meta in zip(data['residual_nodes'],data['residual_info']) if meta['parent_row'] is None]
    EXTRA_COUNT=len(roots);needed=set();stack=roots[:]
    while stack:
        i=stack.pop()
        if i in needed:continue
        needed.add(i)
        if nodes[i][0] in ('add','sub','mul'):stack.extend(nodes[i][1:])
    live=sorted(needed)
    def evaluate(degree):
        values={}
        for i in live:
            n=nodes[i]
            if n[0]=='var':d=degree[mapped[n[1]]]
            elif n[0]=='const':d=0
            elif n[0]=='mul':d=values[n[1]]+values[n[2]]
            else:d=max(values[n[1]],values[n[2]])
            values[i]=d
        return [values[r] for r in roots]
    _extra_degree_evaluator=evaluate

def expr_degree(expr,degree):
    op=expr[0]
    if op=='v':return degree[expr[1]]
    if op=='c':return 0
    a=expr_degree(expr[1],degree);b=expr_degree(expr[2],degree)
    return a+b if op=='*' else max(a,b)

CANDIDATES=[]
for r in KEEP_ROWS:
    terms=ROWS[r]['terms']
    for c,m in terms:
        if len(m)!=1 or abs(c)!=1:continue
        v=m[0]
        if any(v in mm for cc,mm in terms if mm!=[v]):continue
        expression=[(-c*cc,tuple(mm)) for cc,mm in terms if mm!=[v]]
        CANDIDATES.append((r,v,expression))

def analyze(defs,details=False):
    degree={v:1 for v in ACTIVE if v not in defs};visiting=set()
    def go(v):
        if v in degree:return degree[v]
        if v in visiting:raise ValueError('cycle')
        visiting.add(v)
        d=max((sum(go(w) for w in mon) for _,mon in defs[v][1]),default=0)
        visiting.remove(v);degree[v]=d;return d
    try:
        for v in defs:go(v)
    except ValueError:return None
    removed={r for r,_ in defs.values()}
    rd=[max((sum(degree[v] for v in mon) for _,mon in ROWS[r]['terms']),default=0)
        for r in KEEP_ROWS if r not in removed]
    rd.extend(_extra_degree_evaluator(degree) if _extra_degree_evaluator else [pool_degree(degree)])
    metric=(2*max(rd),sum(rd),sum(degree.values()))
    return (metric,degree,rd) if details else metric

def search(cap,seed=0,style=0):
    rng=random.Random(seed);defs={};steps=[]
    while True:
        candidates=[];removed={r for r,_ in defs.values()}
        for r,v,terms in CANDIDATES:
            if v in defs or r in removed:continue
            ds=defs|{v:(r,terms)}
            a=analyze(ds)
            if a is None or a[0]>cap:continue
            if style==0:key=(a[1],a[0],a[2],rng.random())
            elif style==1:key=(a[0],a[1],a[2],rng.random())
            elif style==2:key=(a[2],a[1],a[0],rng.random())
            elif style==3:key=(a[1]*(1+0.2*rng.random()),a[0],a[2])
            elif style==4:key=(rng.random(),a[1],a[0],a[2])
            else:key=(a[1]+style*rng.random(),a[0],a[2])
            candidates.append((key,r,v,terms,a))
        if not candidates:break
        _,r,v,terms,a=min(candidates)
        defs[v]=(r,terms);steps.append({'row':r,'variable':v})
    a=analyze(defs)
    return {'schema':'oriented-pooling-acyclic-pivots-v1','source_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
        'degree_cap':cap,'seed':seed,'style':style,'steps':steps,
        'metrics':{'variables':len(ACTIVE)-len(defs),'residuals':len(KEEP_ROWS)-len(defs)+EXTRA_COUNT,
                   'degree_upper_bound':a[0],'sum_row_degree':a[1],'sum_coordinate_degree':a[2]}}

def quick_search(cap,seed=0,style=0):
    rng=random.Random(seed);defs={};steps=[];candidates=list(CANDIDATES)
    occurrences={v:sum(v in mon for r in KEEP_ROWS for _,mon in ROWS[r]['terms']) for v in ACTIVE}
    if style==0:candidates.sort(key=lambda p:(occurrences[p[1]],len(p[2]),p[0],p[1]))
    elif style==1:candidates.sort(key=lambda p:(len(p[2]),occurrences[p[1]],p[0],p[1]))
    elif style==2:candidates.sort(key=lambda p:(-p[0],p[1]))
    elif style==3:candidates.sort(key=lambda p:(p[0],p[1]))
    elif style==4:candidates.sort(key=lambda p:(occurrences[p[1]]*(.5+rng.random()),len(p[2])))
    else:rng.shuffle(candidates)
    while True:
        added=False;removed={r for r,_ in defs.values()}
        for r,v,terms in candidates:
            if v in defs or r in removed:continue
            ds=defs|{v:(r,terms)};a=analyze(ds)
            if a is None or a[0]>cap:continue
            defs[v]=(r,terms);removed.add(r);steps.append({'row':r,'variable':v});added=True
        if not added:break
    a=analyze(defs)
    return {'schema':'oriented-pooling-acyclic-pivots-v1','source_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
        'degree_cap':cap,'seed':seed,'style':style,'method':'static-priority repeated feasible elimination',
        'steps':steps,'metrics':{'variables':len(ACTIVE)-len(defs),'residuals':len(KEEP_ROWS)-len(defs)+EXTRA_COUNT,
                   'degree_upper_bound':a[0],'sum_row_degree':a[1],'sum_coordinate_degree':a[2]}}

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('caps',type=int,nargs='*')
    parser.add_argument('--base',type=Path,default=BASE_SOURCE);parser.add_argument('--out',type=Path,default=ROOT/'profiles')
    parser.add_argument('--trials',type=int,default=24);args=parser.parse_args();configure(args.base)
    caps=args.caps or [24,32,48,64,128,256,512,1024,4096,131072]
    out=args.out;out.mkdir(parents=True,exist_ok=True)
    for cap in caps:
        best=None
        for seed,style in ([(0,0),(1,1),(2,2),(3,3)]+[(i,4) for i in range(4,16)]+[(i,5) for i in range(16,100)])[:args.trials]:
            p=quick_search(cap,seed,style)
            key=(p['metrics']['variables'],p['metrics']['degree_upper_bound'],p['metrics']['sum_row_degree'])
            if best is None or key<best[0]:best=(key,p)
        p=best[1]
        p['base_file']=BASE_SOURCE.name;p['base_sha256']=hashlib.sha256(BASE_SOURCE.read_bytes()).hexdigest()
        (out/f'cap{cap}.json').write_text(json.dumps(p,sort_keys=True,indent=2)+'\n')
        print(json.dumps({'cap':cap,**p['metrics']}),flush=True)
