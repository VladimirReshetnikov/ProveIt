#!/usr/bin/env python3
"""Independently verify delayed materialization and every quadratic signed-gate residual."""
import collections,gzip,hashlib,json,random,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];G=D/'candidates/one-page-padding-staircase-carrier65-2011';raw=(G/'polynomial.json').read_bytes();assert hashlib.sha256(raw).hexdigest()=='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e';g=json.loads(raw);s=json.loads((P/'seed.json').read_text());assert s['source_graph_sha256']==hashlib.sha256(raw).hexdigest() and s['coefficient_binding']==g['coefficient_binding'] and s['fixed_ports']==g['fixed_numerals']
ports=g['coefficient_binding']['ports'];root=(G/g['coefficient_binding']['path']).resolve();fixed_values={}
for name,meta in ports.items():
 p=root/meta['file'];gz=p.read_bytes();raw=gzip.decompress(gz);assert hashlib.sha256(gz).hexdigest()==meta['gzip_sha256'] and hashlib.sha256(raw).hexdigest()==meta['raw_sha256'] and len(raw)==meta['raw_bytes'] and int.from_bytes(raw,'big').bit_length()==meta['bits'] and int.from_bytes(raw,'big')>0,name;fixed_values[name]=int.from_bytes(raw,'big')
# Polynomial indeterminates for ports and coordinates; port degree is zero.
def clean(a):return {m:c for m,c in a.items() if c}
def plus(a,b,sgn=1):
 z=collections.Counter(a)
 for m,c in b.items():z[m]+=sgn*c
 return clean(z)
def times(a,b):
 z=collections.Counter()
 for x,c in a.items():
  for y,d in b.items():z[tuple(sorted(x+y))]+=c*d
 return clean(z)
def atom(x):return {(str(x),):1}
def const(n):return {():n} if n else {}
def pol(t):
 op=t[0]
 if op=='num':return const(t[1])
 if op in ('var','port'):return atom(op+':'+str(t[1]))
 a,b=map(pol,t[1:]);return times(a,b) if op=='mul' else plus(a,b,1 if op=='add' else -1)
def degree(p):return max((sum(x.startswith('var:') for x in m) for m in p),default=0)
def used(t):
 if t[0]=='var':return {t[1]}
 if t[0] in ('num','port'):return set()
 return used(t[1])|used(t[2])
# Separate polynomial reconstruction; ports are formal indeterminates but
# degree-zero, and input values are shifted by one.
pair={n:(plus(atom('var:'+str(i+1)),const(1)),{}) for i,n in enumerate(g['witnesses'])};pair.update({n:(atom('port:'+n),{}) for n in g['fixed_numerals']});get=lambda x:(const(x),{}) if type(x)==int else pair[x]
rows=s['gate_records'];res=s['residuals'];assert len(rows)==65 and len(res)==39 and s['jones_witness_count']==52 and s['coordinate_count']==53 and s['input_coordinate']==0
assert rows[0]['name']=='qm' and rows[0]['kind']=='inline' and rows[1]['name']=='q' and rows[1]['kind']=='inline' and rows[2]['name']=='q2' and rows[2]['positive_coordinate']==15
idx=0;coords=set(range(1,15));inlined=materialized=0;construction=[]
for i,(gr,rr) in enumerate(zip(g['source'],rows)):
 name,op,l,r=gr;assert (rr['name'],rr['op'],rr['left'],rr['right'])==(name,op,l,r);ap,an=get(l);bp,bn=get(r)
 ep=plus(ap,bp) if op=='+' else plus(ap,bn) if op=='-' else plus(times(ap,bp),times(an,bn))
 en=plus(an,bn) if op=='+' else plus(an,bp) if op=='-' else plus(times(ap,bn),times(an,bp))
 target=times(plus(ap,an,-1),plus(bp,bn,-1)) if op=='*' else plus(plus(ap,an,-1),plus(bp,bn,-1),1 if op=='+' else -1)
 assert all(c>=0 for c in ep.values()) and all(c>=0 for c in en.values())
 assert plus(ep,en,-1)==target;dg=max(degree(ep),degree(en));assert rr['pair_degree']==dg and dg<=2
 if name==g['output']:
  assert i==64 and rr['kind']=='output' and res[idx]['kind']=='output' and res[idx]['gate']==name and pol(res[idx]['expr'])==target;idx+=1;continue
 if rr['kind']=='inline':
  assert dg<=2;inlined+=1;pair[name]=(ep,en)
 else:
  assert rr['kind']=='materialized' and dg==2;materialized+=1;ip=rr['positive_coordinate'];assert 15<=ip<53 and ip not in coords;coords.add(ip);rpos=res[idx];assert rpos['kind']=='positive' and rpos['gate']==name and pol(rpos['expr'])==plus(atom('var:'+str(ip)),ep,-1);idx+=1
  if en:
   ine=rr['negative_coordinate'];assert 15<=ine<53 and ine not in coords;coords.add(ine);rneg=res[idx];assert rneg['kind']=='negative' and rneg['gate']==name and pol(rneg['expr'])==plus(atom('var:'+str(ine)),en,-1);idx+=1;pair[name]=(atom('var:'+str(ip)),atom('var:'+str(ine)))
  else:assert 'negative_coordinate' not in rr;ine=None;pair[name]=(atom('var:'+str(ip)),{})
  construction.append((ip,ine,ep,en))
assert idx==len(res) and (inlined,materialized)==(37,27) and len(construction)==27 and coords==set(range(1,53))
assert max(degree(pol(x['expr'])) for x in res)==2 and set.union(*(used(x['expr']) for x in res))==set(range(1,53))
# The input-0 coordinate is absent, and at all zero witnesses first residual
# is -(beta+1)^2. Beta bytes are positive, so it is nonzero for every input x.
def evalpoly(p,v,ports):
 total=0
 for m,c in p.items():
  t=c
  for x in m:t*=v[int(x[4:])] if x.startswith('var:') else ports[x[5:]]
  total+=t
 return total
zero={i:0 for i in range(53)};assert evalpoly(pol(res[0]['expr']),zero,fixed_values)==-(fixed_values['beta']+1)**2!=0
rng=random.Random(8241)
for _ in range(12):
 vals={i:rng.randrange(3) for i in range(1,15)};vals[0]=rng.randrange(4);p={n:rng.randrange(1,5) for n in g['fixed_numerals']};sv={n:vals[i+1]+1 for i,n in enumerate(g['witnesses'])};sv.update(p)
 for ip,ine,ep,en in construction:
  vp=evalpoly(ep,vals,p);vn=evalpoly(en,vals,p);assert vp>=0 and vn>=0;vals[ip]=vp
  if ine is not None:vals[ine]=vn
 for name,op,l,r in g['source']:
  a=l if type(l)==int else sv[l];b=r if type(r)==int else sv[r];sv[name]=a+b if op=='+' else a-b if op=='-' else a*b
 assert sum(evalpoly(pol(x['expr']),vals,p)**2 for x in res)==sv[g['output']]**2
print(json.dumps({'status':'PASS_EXTERNAL_CANDIDATE','source_gates':65,'inlined_gates':inlined,'materialized_gates':materialized,'materialized_gate_witnesses':38,'residuals':len(res),'jones_witnesses':52,'total_seed_coordinates':53,'maximum_residual_degree':2,'seed_degree_upper':4,'normalization_first_residual':'-(beta+1)^2 nonzero for every distinguished input','tested_assignments':12,'scope':'External polynomial gate identities and witness construction; no Lean quartic/model/Jones proof or nine-variable graph/degree claim.'},indent=2,sort_keys=True))
