#!/usr/bin/env python3
"""Independent tuple-monomial exact residual expansion and fixed-byte ray."""
import pathlib,json,hashlib,gzip,collections
D=pathlib.Path(__file__).resolve().parents[2];P=D/'con-zfc-diophantine-forms/72-congruence-sextic';C=D/'con-zfc-diophantine-forms/44-b4-sparse/native/coefficients';prime=1000000007
sha=lambda p:hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
def add(a,b,sign=1):
 c=dict(a)
 for k,v in b.items():c[k]=c.get(k,0)+sign*v
 return {k:v for k,v in c.items() if v}
def mul(a,b):
 c={}
 for x,u in a.items():
  for y,v in b.items():
   k=tuple(i+j for i,j in zip(x,y));c[k]=c.get(k,0)+u*v
 return {k:v for k,v in c.items() if v}
def packed_exponent_bound(g):
 names=g['witnesses']+g['fixed_ports'];N=len(names);zero=(0,)*N;bounds={n:tuple(int(i==j) for i in range(N)) for j,n in enumerate(names)}
 def calc(e):
  if type(e)==int:return zero
  if type(e)==str:return bounds[e]
  op,a,b=e;x,y=calc(a),calc(b);return tuple(u+v if op=='*' else max(u,v) for u,v in zip(x,y))
 for n,e in g['derived_fixed_leaves'].items():bounds[n]=calc(e)
 for n,op,a,b in g['source']:bounds[n]=calc([op,a,b])
 return max(max(x) for x in bounds.values())
def sparse_residuals(g):
 names=g['witnesses']+g['fixed_ports'];N=len(names);zero=(0,)*N;env={n:{tuple(int(i==j) for i in range(N)):1} for j,n in enumerate(names)}
 def calc(e):
  if type(e)==int:return {zero:e} if e else {}
  if type(e)==str:return env[e]
  op,a,b=e;x,y=calc(a),calc(b);return mul(x,y) if op=='*' else add(x,y,1 if op=='+' else -1)
 for n,e in g['derived_fixed_leaves'].items():env[n]=calc(e)
 required=set(g['residuals'])
 for n,op,a,b in reversed(g['source']):
  if n in required:
   if type(a)==str:required.add(a)
   if type(b)==str:required.add(b)
 for n,op,a,b in g['source']:
  if n in required:env[n]=calc([op,a,b])
 return {n:max((sum(k[:len(g['witnesses'])]) for k in env[n]),default=-1) for n in g['residuals']}
def prove_finalizer(g):
 names=g['residuals'];N=len(names);zero=(0,)*N;cut={n:{tuple(int(i==j) for i in range(N)):1} for j,n in enumerate(names)}
 def v(x):return {zero:x} if type(x)==int and x else ({} if type(x)==int else cut[x])
 last=max(i for i,row in enumerate(g['source']) if row[0] in names)
 for n,op,a,b in g['source'][last+1:]:
  x,y=v(a),v(b);cut[n]=mul(x,y) if op=='*' else add(x,y,1 if op=='+' else -1)
 want={}
 for n in names:want=add(want,mul(cut[n],cut[n]))
 assert cut[g['output']]==want
def poly(a,b,op):
 out=[0]*(len(a)+len(b)-1 if op=='*' else max(len(a),len(b)))
 if op=='*':
  for i,x in enumerate(a):
   for j,y in enumerate(b):out[i+j]=(out[i+j]+x*y)%prime
 else:
  for i,x in enumerate(a):out[i]=(out[i]+x)%prime
  for i,y in enumerate(b):out[i]=(out[i]+(y if op=='+' else -y))%prime
 while len(out)>1 and not out[-1]:out.pop()
 return out
results={}
for kind,gpin,bpin,degree,lead in [('positive13','1968b1a0c887eb5a94794d8fdd7635f56432da4d235e81cf5ce4ab4790840d49','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf',28,148768232),('positive14','91a307011482e1850b97ae4a4222f024bcbbde00a7a7850e6635e8b875729495', 'f3ebbe2956482e2965c286d4a2cc648b99106e3e3859f1feb6cbebae820dc2ec',24,925559841)]:
 gp=P/kind/('p13_degree28.json' if kind=='positive13' else 'p14_degree24.json');bp=P/kind/'ACTIVE_BINDING.json';assert sha(gp)==gpin and sha(bp)==bpin;g=json.loads(gp.read_text());b=json.loads(bp.read_text());assert b['polynomial_sha256']==gpin and b['MF_convention'].startswith('Already shifted') and g['fixed_ports']==['beta','K0','MC','MF'] and g['derived_fixed_leaves']==b['derived_fixed_leaves']
 vals={}
 for n in g['fixed_ports']:
  m=b['ports'][n];p=(P/kind/m['path']).resolve();gz=p.read_bytes();raw=gzip.decompress(gz);assert gz==(C/p.name).read_bytes() and hashlib.sha256(gz).hexdigest()==m['sha256_gzip'] and hashlib.sha256(raw).hexdigest()==m['sha256_raw'] and len(raw)==m['raw_bytes'] and raw[-1]!=0 and int.from_bytes(raw,'little').bit_length()==m['bits'];vals[n]=int.from_bytes(raw,'little')%prime
 def evalconst(e):
  if type(e)==int:return e%prime
  if type(e)==str:return vals[e]
  op,a,b=e;aa,bb=evalconst(a),evalconst(b);return (aa+bb if op=='+' else aa*bb)%prime
 assert list(g['derived_fixed_leaves'])==['B','b','b2','L','Kfinal','four_beta']
 for n,e in g['derived_fixed_leaves'].items():assert n not in vals;vals[n]=evalconst(e)
 w=g['witnesses'];v={n:[0,1] for n in w};v.update({k:[a] for k,a in vals.items()});counts=collections.Counter();edges={}
 for n,op,a,b in g['source']:
  assert n not in v and op in '+-*' and all(type(x)==int or x in v for x in (a,b));v[n]=poly([a%prime] if type(a)==int else v[a],[b%prime] if type(b)==int else v[b],op);edges[n]=(a,b);counts[op]+=1
 seen=set();leaves=set();todo=[g['output']]
 while todo:
  n=todo.pop()
  if type(n)==str and n in edges:
   if n not in seen:seen.add(n);todo.extend(edges[n])
  elif type(n)==str:leaves.add(n)
 assert len(seen)==len(g['source'])==g['operations'] and dict(counts)==g['operation_breakdown'] and set(w+g['fixed_ports'])<=leaves
 packed_bound=packed_exponent_bound(g);assert packed_bound<64;ds=sparse_residuals(g);prove_finalizer(g);ray=v[g['output']];assert 2*max(ds.values())==len(ray)-1==degree and ray[-1]==lead and g['exact_degree']==degree
 results[kind]={'operations':len(seen),'counts':dict(counts),'residual_degrees':ds,'largest_uncancelled_exponent':packed_bound,'degree_upper':degree,'ray_degree':len(ray)-1,'leading_ray_mod_prime':ray[-1]}
print(json.dumps({'status':'PASS','prime':prime,'results':results,'scope':'Independent tuple-monomial external certificate; six derived leaves are constants; no Lean byte/degree theorem.'},indent=2,sort_keys=True))
