#!/usr/bin/env python3
"""Independently verify delayed materialization and every quadratic signed-gate residual."""
import collections,gzip,hashlib,json,random,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];C=D/'research/nine-sharing-quartic65-sign33-candidate';G=D/'candidates/one-page-padding-staircase-carrier65-2011';raw=(G/'polynomial.json').read_bytes();assert hashlib.sha256(raw).hexdigest()=='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e';g=json.loads(raw);assert hashlib.sha256((C/'seed.json').read_bytes()).hexdigest()=='a8cd4d01962b9380065ebbd3d7b75db3ffcadf18969099398bd151c4e2219e75' and hashlib.sha256((C/'build.py').read_bytes()).hexdigest()=='bfd718c5f0eced2e362bc7940c61c66769fcb0eaf72ad18ff0bc436056fabb0b';s=json.loads((C/'seed.json').read_text());assert s['source_graph_sha256']==hashlib.sha256(raw).hexdigest() and s['coefficient_binding']==g['coefficient_binding'] and s['fixed_ports']==g['fixed_numerals']
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
rows=s['gate_records'];res=s['residuals'];assert len(rows)==60 and len(res)==24 and s['jones_witness_count']==33 and s['coordinate_count']==34 and s['input_coordinate']==0 and s['omitted_graph_rows']==g['source'][60:]
assert rows[0]['name']=='qm' and rows[0]['kind']=='inline' and rows[1]['name']=='q' and rows[1]['kind']=='inline' and rows[2]['name']=='q2' and rows[2]['positive_coordinate']==15
norms={'N0':1,'N1':1,'Na':1,'Nt':1,'scaled_Ns':'Delta'};assert s['norm_targets']==norms
idx=0;coords=set(range(1,15));inlined=materialized=0;construction=[];seen_norms=[];signed=[]
for i,(gr,rr) in enumerate(zip(g['source'][:60],rows)):
 name,op,l,r=gr;assert (rr['name'],rr['op'],rr['left'],rr['right'])==(name,op,l,r);ap,an=get(l);bp,bn=get(r)
 ep=plus(ap,bp) if op=='+' else plus(ap,bn) if op=='-' else plus(times(ap,bp),times(an,bn))
 en=plus(an,bn) if op=='+' else plus(an,bp) if op=='-' else plus(times(ap,bn),times(an,bp))
 target=times(plus(ap,an,-1),plus(bp,bn,-1)) if op=='*' else plus(plus(ap,an,-1),plus(bp,bn,-1),1 if op=='+' else -1)
 assert all(c>=0 for c in ep.values()) and all(c>=0 for c in en.values())
 assert plus(ep,en,-1)==target;dg=max(degree(ep),degree(en));assert rr['pair_degree']==dg and dg<=2
 if name in norms:
  assert rr['kind']=='norm' and rr['target']==norms[name] and res[idx]['kind']=='norm' and res[idx]['gate']==name and res[idx]['target']==norms[name]
  norm_target=plus(*get('Delta'),-1) if name=='scaled_Ns' else const(1)
  assert pol(res[idx]['expr'])==plus(target,norm_target,-1);idx+=1;pair[name]=(ep,en);seen_norms.append(name);continue
 if rr['kind']=='inline':
  assert dg<=2;inlined+=1;pair[name]=(ep,en)
 else:
  assert rr['kind']=='materialized' and dg==2;materialized+=1
  if 'sign_coordinate' in rr:
   sign=rr['sign'];ip=rr['sign_coordinate'];assert 15<=ip<34 and ip not in coords and sign in (-1,1);coords.add(ip);r=res[idx];assert r['kind']=='signed' and r['gate']==name and r['sign']==sign;assert pol(r['expr'])==plus(atom('var:'+str(ip)),target,-sign);idx+=1
   pair[name]=(atom('var:'+str(ip)),{}) if sign==1 else ({},atom('var:'+str(ip)));signed.append((name,sign));construction.append((ip,None,ep,en,sign))
  else:
   ip=rr['positive_coordinate'];assert 15<=ip<34 and ip not in coords;coords.add(ip);r=res[idx];assert r['kind']=='positive' and r['gate']==name and pol(r['expr'])==plus(atom('var:'+str(ip)),ep,-1);idx+=1
   assert not en and 'negative_coordinate' not in rr;pair[name]=(atom('var:'+str(ip)),{});construction.append((ip,None,ep,en,0))
assert idx==len(res) and (inlined,materialized)==(36,19) and len(construction)==19 and coords==set(range(1,34)) and set(seen_norms)==set(norms) and signed==[('gap',1),('tau',1),('cTminusR',1),('V',1),('V2minusY2',-1)]
assert max(degree(pol(x['expr'])) for x in res)==2 and set.union(*(used(x['expr']) for x in res))==set(range(1,34))
# The input-0 coordinate is absent, and at all zero witnesses first residual
# is -(beta+1)^2. Beta bytes are positive, so it is nonzero for every input x.
def evalpoly(p,v,ports):
 total=0
 for m,c in p.items():
  t=c
  for x in m:t*=v[int(x[4:])] if x.startswith('var:') else ports[x[5:]]
  total+=t
 return total
zero={i:0 for i in range(34)};assert evalpoly(pol(res[0]['expr']),zero,fixed_values)==-(fixed_values['beta']+1)**2!=0
rng=random.Random(8241);negative_signed=0
for _ in range(8):
 vals={i:rng.randrange(3) for i in range(1,15)};vals[0]=rng.randrange(4);p={n:rng.randrange(1,5) for n in g['fixed_numerals']};sv={n:vals[i+1]+1 for i,n in enumerate(g['witnesses'])};sv.update(p)
 for ip,ine,ep,en,sign in construction:
  vp=evalpoly(ep,vals,p);vn=evalpoly(en,vals,p);vals[ip]=(vp-vn)*sign if sign else vp
  if sign and vals[ip]<0:negative_signed+=1
 for name,op,l,r in g['source'][:60]:
  a=l if type(l)==int else sv[l];b=r if type(r)==int else sv[r];sv[name]=a+b if op=='+' else a-b if op=='-' else a*b
 expected=sum((sv[name]-(sv[t] if isinstance(t,str) else t))**2 for name,t in norms.items())
 assert sum(evalpoly(pol(x['expr']),vals,p)**2 for x in res)==expected
assert negative_signed>0
# Independently verify Z = Delta * (f² - Delta*(i*c²)²).
delta=atom('D');f=atom('f');i=atom('i');c=atom('c');I=times(i,times(c,c));S=times(delta,I);Z=plus(times(delta,times(f,f)),times(S,S),-1);strong=plus(times(f,f),times(delta,times(I,I)),-1);assert Z==times(delta,strong)
F=D/'research/current2011-spheres-fresh-base/FreshCarrierSpheres.lean';C65=D/'Lean/DiophantineConsistency/Carrier65.lean';hs=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();assert hs(F)=='a9e4d44f3ef37f81f192d9d7fa03678eaa53ca5ec216b3257a3a6fa7ab48f6a5' and hs(C65)=='be2f2cb6833d190818541a57bb9b7c148c5975864d6af518f511b67f80fb1154'
fs=F.read_text();cs=C65.read_text();assert 'variable (F : Facts R) (p : Fin 4 → R) (v : Fin 14 → R) (hb : 0 < p 0) (hv : ∀ j, 0 < v j)' in fs
for q in ['discrete : Discrete R','mod4 : Nonempty (R →+* ZMod 4)','near : ∀ A x y : R','consecutive : ∀ n x y : R','theorem value65_zero_iff_norms','Carrier65.value p v = 0 ↔','strong (core p v) = 1','theorem modelFacts : Facts (DiffRing V)']:assert q in fs,q
assert 'def strong (b : Core R) : R := b.f ^ 2 - b.delta * (b.i * b.c ^ 2) ^ 2' in cs
I=D/'Lean/DiophantineConsistency/ArithmeticCarrier94Indices.lean';isrc=I.read_text();assert 'theorem ordinary_first_indices (beta K MC MF J F alpha z f i T s w N eta zeta y gamma : V)' in isrc and '(i*c*c)*(i*c*c)+delta a=delta a*f*f →' in isrc and '2*R<c' in isrc
# If i is replaced by Delta*i_source then i*c² = Delta*i_source*c² = S.
assert times(times(delta,i),times(c,c))==S
srcaudit=D/'reviews/nine-sharing-quartic65-59-independent';assert hs(srcaudit/'source_check.py')=='5c4d3ab4769952fce2ae125287a6af75863cb18e3b7c8752553bc5f6b46e1c18' and hs(srcaudit/'source_result.json')=='6733a6246154ed58e5284843cba4750d5cb867e23f541fb451637952b1bcb953'
q=subprocess.run([sys.executable,'-I','-S','-B',str(srcaudit/'source_check.py')],capture_output=True);assert q.returncode==0 and not q.stderr and q.stdout==(srcaudit/'source_result.json').read_bytes()
print(json.dumps({'status':'PASS_CONDITIONAL_EXTERNAL_SIGN_REVIEW','source_gates_used':60,'omitted_product_gates':5,'inlined_gates':inlined,'materialized_gates':materialized,'materialized_gate_witnesses':19,'residuals':len(res),'jones_witnesses':33,'total_seed_coordinates':34,'maximum_residual_degree':2,'normalization':'-(beta+1)^2 nonzero for all distinguished inputs','sample_assignments':8,'negative_signed_assignments':negative_signed,'scope':'Ring identities with conditional sign obligations; no natural-witness model proof, Lean bridge or iPRA endpoint.'},indent=2,sort_keys=True))
