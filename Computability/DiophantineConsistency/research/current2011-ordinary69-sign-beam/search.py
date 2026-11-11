#!/usr/bin/env python3
"""Bounded exact-rewrite beam over the 69/84 graph; no Lean or new graph."""
import ast, collections, hashlib, itertools, json, random, sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
root = Path(__file__).resolve().parents[4]
research = root / 'Computability/DiophantineConsistency/research'
engine = research / 'nine-sharing-sign14-positive74-structural-search/search_canonical.py'
graphfile = research / 'current2011-ordinary69-84-candidate/polynomial.json'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def need(x,msg):
    if not x: raise RuntimeError(msg)
need(sha(engine)=='5f683e6e9b3cc46450e4edcc566610862730b8e58ab574a4e12496dc67b71bb6','engine pin')
need(sha(graphfile)=='c9781e95b9d8e3124afadfe3ee5874eb3eb76ce9f1aaef02c7b3bf49ed93e80a','graph pin')
source=engine.read_text(); parsed=ast.parse(source); wanted={'node','graph','opof','alternatives','replace'}; N=[]; I={}
found=set()
for stmt in parsed.body:
    if isinstance(stmt,ast.FunctionDef) and stmt.name in wanted:
        need(stmt.name not in found,'duplicate function');found.add(stmt.name)
        exec(compile(ast.Module(body=[stmt],type_ignores=[]),'<pinned-engine>','exec'))
need(found==wanted,'engine function set')
g=json.loads(graphfile.read_text());vals={};cons=collections.defaultdict(list)
for name,op,a,b in g['source']:
    need(name not in vals and op in ('+','-','*'),'topology')
    def arg(x):
        if type(x)==int:return 'lit:'+str(x)
        need(type(x)==str,'operand');cons[x].append(name)
        return vals.get(x,'leaf:'+x)
    vals[name]=node({'+':'add','-':'sub','*':'mul'}[op],arg(a),arg(b))
root_node=vals[g['output']];need(len(g['source'])==69 and len(graph(root_node))==69,'source gate count')
need(set(cons)-set(vals)==set(g['witnesses']+g['fixed_numerals']),'input interface')
need(cons['N0']==['PQ'] and cons['N1']==['PQ'] and cons['Nt']==['PQW'],'factor sole consumers')
rows={row[0]:row for row in g['source']}
need(rows['PQ']==['PQ','*','N0','N1'] and rows['PQW']==['PQW','*','PQ','Nt'],'factor product structure')
# Each double-negated product is an identity in the free commutative ring.
def mul(a,b):
    out={}
    for x,c in a.items():
        for y,d in b.items():
            z=tuple(u+v for u,v in zip(x,y));out[z]=out.get(z,0)+c*d
    return {x:c for x,c in out.items() if c}
def add(a,b,sgn=1):
    out=dict(a)
    for x,c in b.items():out[x]=out.get(x,0)+sgn*c
    return {x:c for x,c in out.items() if c}
atom=[{tuple(int(i==j) for i in range(3)):1} for j in range(3)]
x=mul(mul(atom[0],atom[1]),atom[2]);quad=add(mul(x,x),x,-2)
for i,j in itertools.combinations(range(3),2):
    vv=[{k:(-v if t in (i,j) else v) for k,v in a.items()} for t,a in enumerate(atom)]
    xx=mul(mul(vv[0],vv[1]),vv[2]);need(add(mul(xx,xx),xx,-2)==quad,'sign certificate')
control=node('add',node('mul','control:a','control:b'),node('mul','control:a','control:c'))
need(len(graph(control))==3 and min(len(graph(x)) for x in alternatives(control))==2,'factor positive control')
rng=random.Random(69085);beam={root_node:[]};starts={}
for pair in itertools.combinations(('N0','N1','Nt'),2):
    rr=root_node;path=[]
    for name in pair:
        old=vals[name];op,a,b=N[old];need(op=='sub','factor operation');new=node('sub',b,a);rr=replace(rr,old,new);path.append(('negate',name))
    starts['+'.join(pair)]=len(graph(rr));beam[rr]=path
need(all(c==69 for c in starts.values()),'sign variant census')
seen=set(beam);best=69;depths=[]
for depth in range(10):
    candidates={}
    for current,path in beam.items():
        allg=sorted(graph(current));rng.shuffle(allg)
        for target in allg:
            alt=sorted(alternatives(target));rng.shuffle(alt)
            for other in alt:
                nr=replace(current,target,other)
                if nr in seen:continue
                seen.add(nr);count=len(graph(nr));p=path+[(target,other)]
                best=min(best,count)
                if count<=71:candidates[nr]=(count,p)
    ranked=sorted(candidates.items(),key=lambda x:(x[1][0],rng.random()))[:160]
    beam={rr:path for rr,(count,path) in ranked}
    depths.append({'depth':depth,'states_at_most_71':len(candidates),'beam':len(beam),'best':best})
    if best<69 or not candidates:break
need(best==69,'potential smaller candidate requires separate exact validation')
print(json.dumps({'status':'PASS_BOUNDED_SEARCH','graph_sha256':sha(graphfile),'engine_sha256':sha(engine),'original_count':69,'sign_variants':starts,'seed':69085,'depth_limit':10,'beam_limit':160,'intermediate_gate_limit':71,'best_observed':best,'depths':depths,'scope':'Bounded beam only; no global minimality, candidate, Lean proof, or file-semantic binding.'},indent=2,sort_keys=True))
