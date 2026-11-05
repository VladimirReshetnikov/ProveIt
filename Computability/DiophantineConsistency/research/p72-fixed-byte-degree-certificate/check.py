#!/usr/bin/env python3
"""Exact syntactic upper and fixed-byte diagonal lower degree bounds for P72."""
import collections,gzip,hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
D=Path(__file__).resolve().parents[2];P=D/'con-zfc-diophantine-forms/72-congruence-sextic';C=D/'con-zfc-diophantine-forms/44-b4-sparse/native/coefficients';prime=1000000007
sha=lambda b:hashlib.sha256(b).hexdigest()
def need(v,s):
 if not v:raise RuntimeError(s)
def poly(a,b,op):
 out=[0]*(len(a)+len(b)-1 if op=='*' else max(len(a),len(b)))
 if op=='*':
  for i,x in enumerate(a):
   for j,y in enumerate(b):out[i+j]=(out[i+j]+x*y)%prime
 else:
  for i,x in enumerate(a):out[i]=(out[i]+x)%prime
  for i,y in enumerate(b):out[i]=(out[i]+(y if op=='+' else -y))%prime
 while len(out)>1 and out[-1]==0:out.pop()
 return out
def symbolic_residual_degrees(g):
 # Integer sparse polynomials in all witnesses and the four symbolic ports.
 # Six-bit packing is safe only after checking uncancelled exponent bounds.
 names=g['witnesses']+g['fixed_ports'];N=len(names);bits=6;zero=(0,)*N
 bounds={n:tuple(int(i==j) for i in range(N)) for j,n in enumerate(names)}
 def bd(e):
  if type(e)==int:return zero
  if type(e)==str:return bounds[e]
  op,a,b=e;x,y=bd(a),bd(b);return tuple(u+v if op=='*' else max(u,v) for u,v in zip(x,y))
 for n,e in g['derived_fixed_leaves'].items():bounds[n]=bd(e)
 for n,op,a,b in g['source']:
  x=zero if type(a)==int else bounds[a];y=zero if type(b)==int else bounds[b];bounds[n]=tuple(u+v if op=='*' else max(u,v) for u,v in zip(x,y))
 need(max(max(v) for v in bounds.values())<2**bits,'packed exponent overflow')
 def add(a,b,sign=1):
  c=dict(a)
  for k,v in b.items():c[k]=c.get(k,0)+sign*v
  return {k:v for k,v in c.items() if v}
 def mul(a,b):
  c={}
  for x,u in a.items():
   for y,v in b.items():c[x+y]=c.get(x+y,0)+u*v
  return {k:v for k,v in c.items() if v}
 env={n:{1<<(bits*j):1} for j,n in enumerate(names)}
 def calc(e):
  if type(e)==int:return {0:e} if e else {}
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
 def wd(k):return sum((k>>(bits*j))&63 for j in range(len(g['witnesses'])))
 ds={n:max((wd(k) for k in env[n]),default=-1) for n in g['residuals']}
 # Independently verify the literal finalizer as a polynomial over independent residual cuts.
 r=g['residuals'];last=max(i for i,row in enumerate(g['source']) if row[0] in r)
 cuts={n:{1<<(bits*j):1} for j,n in enumerate(r)}
 def cv(v):return {0:v} if type(v)==int and v else ({} if type(v)==int else cuts[v])
 for n,op,a,b in g['source'][last+1:]:
  x,y=cv(a),cv(b);cuts[n]=mul(x,y) if op=='*' else add(x,y,1 if op=='+' else -1)
 expected={}
 for n in r:expected=add(expected,mul(cuts[n],cuts[n]))
 need(cuts[g['output']]==expected,'finalizer is not exactly sum of residual squares')
 return ds,2*max(ds.values())
out={}
for label,pin,want in [('positive13','1968b1a0c887eb5a94794d8fdd7635f56432da4d235e81cf5ce4ab4790840d49',28),('positive14','91a307011482e1850b97ae4a4222f024bcbbde00a7a7850e6635e8b875729495',24)]:
 dir=P/label;file=dir/('p13_degree28.json' if label=='positive13' else 'p14_degree24.json');raw=file.read_bytes();need(sha(raw)==pin,'graph pin '+label);g=json.loads(raw);br=(dir/'ACTIVE_BINDING.json').read_bytes();need(sha(br)==('6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf' if label=='positive13' else 'f3ebbe2956482e2965c286d4a2cc648b99106e3e3859f1feb6cbebae820dc2ec'),'binding pin');bind=json.loads(br);need(bind['polynomial_sha256']==pin,'binding graph')
 witnesses=g['witnesses'];need(len(witnesses)==(13 if label=='positive13' else 14) and len(set(witnesses))==len(witnesses),'witnesses');need(g['fixed_ports']==['beta','K0','MC','MF'] and bind['MF_convention'].startswith('Already shifted'),'port convention')
 residues={};portmeta={};missing=[]
 for name in g['fixed_ports']:
  meta=bind['ports'][name];declared=(dir/meta['path']).resolve();need(declared.is_file(),'declared payload missing '+name);gz=declared.read_bytes();need(gz==(C/Path(meta['path']).name).read_bytes(),'source44 byte mismatch '+name);rawp=gzip.decompress(gz);need(sha(gz)==meta['sha256_gzip'] and sha(rawp)==meta['sha256_raw'] and len(rawp)==meta['raw_bytes'] and int.from_bytes(rawp,'little').bit_length()==meta['bits'],'port '+name);need(not rawp or rawp[-1]!=0,'nonminimal bytes');residues[name]=int.from_bytes(rawp,'little')%prime;portmeta[name]={'declared_path':str(declared),'declared_exists':declared.is_file(),'fallback_path':str((C/Path(meta['path']).name).resolve()),'raw_sha256':sha(rawp),'gzip_sha256':sha(gz)}
  if not declared.is_file():missing.append(name)
 if label=='positive13':need(g['derived_fixed_leaves']==bind['derived_fixed_leaves'],'derived binding')
 vals=dict(residues)
 def constant(expr):
  if type(expr)==int:return expr%prime
  if type(expr)==str:return vals[expr]
  need(type(expr)==list and len(expr)==3 and expr[0] in ('+','*'),'derived recipe');a,b=constant(expr[1]),constant(expr[2]);return (a+b if expr[0]=='+' else a*b)%prime
 need(list(g['derived_fixed_leaves'])==['B','b','b2','L','Kfinal','four_beta'],'derived order')
 for name,expr in g['derived_fixed_leaves'].items():need(name not in vals,'derived clash');vals[name]=constant(expr)
 deg={n:1 for n in witnesses};deg.update({n:0 for n in vals});ray={n:[0,1] for n in witnesses};ray.update({n:[v] for n,v in vals.items()});edges={};counts=collections.Counter()
 for name,op,a,b in g['source']:
  need(name not in deg and op in ('+','-','*') and all(type(x)==int or x in deg for x in (a,b)),'topology '+name)
  da=0 if type(a)==int else deg[a];db=0 if type(b)==int else deg[b];deg[name]=da+db if op=='*' else max(da,db);ray[name]=poly([a%prime] if type(a)==int else ray[a],[b%prime] if type(b)==int else ray[b],op);edges[name]=(a,b);counts[op]+=1
 seen=set();leaves=set();todo=[g['output']]
 while todo:
  n=todo.pop()
  if type(n)==str and n in edges:
   if n not in seen:seen.add(n);todo.extend(edges[n])
  elif type(n)==str:leaves.add(n)
 need(len(seen)==len(g['source'])==g['operations'] and dict(counts)==g['operation_breakdown'] and set(witnesses+g['fixed_ports'])<=leaves,'count/live')
 result=ray[g['output']];residual_degrees,upper=symbolic_residual_degrees(g);need(upper==len(result)-1==want and result[-1]!=0 and g['exact_degree']==want,'degree certificate')
 out[label]={'graph_sha256':pin,'operations':len(seen),'counts':dict(counts),'naive_gate_degree_upper':deg[g['output']],'residual_degrees_exact_symbolic':residual_degrees,'degree_upper':upper,'diagonal_degree':len(result)-1,'diagonal_leading_coefficient_mod_1000000007':result[-1],'ports':portmeta,'missing_declared_port_paths':missing,'derived_fixed_leaves':list(g['derived_fixed_leaves'])}
print(json.dumps({'status':'PASS_EXTERNAL_FIXED_BYTE_DEGREES','prime':prime,'results':out,'scope':'All six beta-derived leaves count as fixed constants. Restored declared paths are byte-identical to the hash-matched source44 files. No Lean JSON, byte, or degree theorem.'},indent=2,sort_keys=True))
