"""Independent algebra/count/degree checks. Does not import the generator."""
import collections, gzip, hashlib, json, pathlib, random
import sympy as sp
ROOT=pathlib.Path(__file__).resolve().parent

def require(v,msg):
 if not v:raise RuntimeError(msg)
def digest(n):return hashlib.sha256(json.dumps(n,separators=(',',':')).encode()).hexdigest()
def hashes(d):
 h=[]
 for i,n in enumerate(d['nodes']):
  if n[0] in ('add','sub','mul'):
   require(all(type(x)==int and 0<=x<i for x in n[1:]),'bad topology')
   a,b=(h[j] for j in n[1:]);h.append(digest([n[0],*sorted([a,b])]) if n[0] in ('add','mul') else digest([n[0],a,b]))
  else:h.append(digest(n))
 return h

def topology(d):
 hashes(d);live=set()
 def walk(i):
  if i in live:return
  live.add(i)
  if d['nodes'][i][0] in ('add','sub','mul'):
   for j in d['nodes'][i][1:]:walk(j)
 walk(d['output']);require(len(live)==len(d['nodes']),'dead nodes')
 ct=collections.Counter(n[0] for n in d['nodes'] if n[0] in ('add','sub','mul'))
 require(dict(ct)==d['operation_counts'],'counts');require(sum(ct.values())==d['operations'],'total')
 deg=[]
 for n in d['nodes']:
  deg.append(1 if n[0]=='variable' else 0 if n[0] in ('integer','coefficient') else sum(deg[j] for j in n[1:]) if n[0]=='mul' else max(deg[j] for j in n[1:]))
 require(deg[d['output']]==d['syntactic_bound'],'bound')
 return {'counts':dict(ct),'operations':sum(ct.values()),'syntactic_bound':deg[-1]}

# Verify every source prefix register by exact recursively hashed arithmetic
# expressions after the three explicitly listed source modifications.
parent=json.loads((ROOT/'provenance/scalar_parent.json').read_text())
changed=json.loads(json.dumps(parent))
changed['nodes'][83]=['mul',81,4] # I=r*c²
changed['nodes'][111]=['mul',82,39] # S=(s*r)*H
for i,n in {103:['mul',31,30],104:['mul',38,8],105:['sub',103,104],106:['mul',30,105],107:['sub',106,31]}.items():changed['nodes'][i]=n
expected=hashes(changed)
docs=[json.loads((ROOT/name).read_text()) for name in ('equation.json','equation_reduced.json')]
result={}
binding=json.loads((ROOT/'coefficients/BINDING.json').read_text())
actual={}
for name,item in binding['payloads'].items():
 raw=gzip.decompress((ROOT/'coefficients'/item['file']).read_bytes())
 require(hashlib.sha256(raw).hexdigest()==item['raw_sha256'],'coefficient hash '+name)
 require(len(raw)==item['raw_bytes'],'coefficient bytes '+name)
 actual[name]=int.from_bytes(raw,'little')
 require(actual[name].bit_length()==item['bits'],'coefficient bits '+name)
require(actual['beta']==2**1064921-1,'actual beta recipe')
result['actual_coefficient_payload_hashes']=True
result['actual_beta_recipe']=True
for name,d in zip(('minimal','reduced'),docs):
 result[name]=topology(d);hh=hashes(d)
 for k,v in parent['named_registers'].items():
  if v<=122 and k in d['named_registers']:
   require(hh[d['named_registers'][k]]==expected[v],f'prefix mismatch {k}')
 require(d['variables']==parent['variables'],'variables changed')
 require({n[1] for n in d['nodes'] if n[0]=='coefficient'}=={n[1] for n in parent['nodes'] if n[0]=='coefficient'},'coefficient leaf mismatch')

# Independent generic norm by multiplying conjugates in a multiquadratic algebra.
z,a,b,e,c=sp.symbols('z a b e c');rads=[a,b,e,c]
def extension_mul(f,g):
 out={}
 for i,x in f.items():
  for j,y in g.items():
   term=x*y;shared=i&j
   for k,r in enumerate(rads):
    if shared>>k&1:term*=r
   mask=i^j;out[mask]=out.get(mask,0)+term
 return {k:sp.expand(v) for k,v in out.items() if sp.expand(v)!=0}
f={0:z,1:-1,2:-1,4:-1,8:-1}
for bit in (1,2,4,8):f=extension_mul(f,{k:(-v if k&bit else v) for k,v in f.items()})
require(set(f)=={0},'radical elimination');generic=f[0]

def symbolic(d,cuts,out=None):
 memo={d['named_registers'][k]:v for k,v in cuts.items()}
 def get(i):
  if i in memo:return memo[i]
  n=d['nodes'][i]
  if n[0]=='integer':v=sp.Integer(n[1])
  elif n[0] in ('variable','coefficient'):v=sp.Symbol(n[1])
  else:
   x,y=(get(j) for j in n[1:]);v=x+y if n[0]=='add' else x-y if n[0]=='sub' else x*y
  memo[i]=v;return v
 return get(d['output'] if out is None else out)
minimal=docs[0];reduced=docs[1]
mgeneric=sp.expand(symbolic(minimal,{'center':z,'ra':a,'rb':b,'re':e,'rn':c}))
require(sp.expand(mgeneric-generic)==0,'literal norm differs from sign product')
B,L,E=sp.symbols('B L E')
rpoly=sp.expand(symbolic(reduced,{'Bcenter':B,'Lcenter':L,'center_defect':E,'ra':a,'rb':b,'re':e}))
require(sp.expand(rpoly-generic.subs({z:B+L,c:L**2-E}))==0,'reduced norm identity')
S,Q,V,N,A,Df,Dt,Dg=sp.symbols('S Q V n A Df Dt Dg')
cuts={'S':S,'Q':Q,'V':V,'n':N,'Acarrier':A,'Df':Df,'Dt':Dt,'Dg':Dg}
# Prefix cut points verify the minimal/reduced bridge without expanding prefix.
for d,forms in [(minimal,{'center':S*(N+Q*V)-A,'ra':9*S*S*Df,'rb':81*S*S*Dt,'re':729*S*S*Dg,'rn':S*S*(Q-1)*(Q*V*V-1)}),(reduced,{'Bcenter':S*N-A,'Lcenter':S*Q*V,'center_defect':S*S*(Q*(V*V+1)-1),'center':S*(N+Q*V)-A,'rn':S*S*(Q-1)*(Q*V*V-1)})]:
 for k,v in forms.items():require(sp.expand(symbolic(d,cuts,d['named_registers'][k])-v)==0,'bridge '+k)
require(reduced['syntactic_bound']==768,'upper bound768')

# Formal top term of the paired expression. All other terms have degree<96:
# deg(B,L,E,a,b,e)=(35,61,92,34,50,62).
# Hence top P=(2LB)^8, degree768. Independently expand the selected coefficient.
beta,j,w,v,C,zv,s,r,cv,T=sp.symbols('beta j w v C z s r c T')
q0=6*beta*j;W0=12*w;Y0=2*v*q0**3;a0=q0*W0*Y0;F0=W0*C-q0*zv;R0=-q0**3*F0
I0=r*cv**2;S0=4*s*r*a0;L0=-S0*a0**6*I0**4*R0;B0=-(4*a0)**5*T**5
poly_top=sp.Poly(sp.expand((2*L0*B0)**8),j,w,v,C,zv,s,r,cv,T)
coeff_C=poly_top.coeff_monomial(j**408*w**104*v**96*C**8*s**8*r**40*cv**64*T**40)
coeff_z=poly_top.coeff_monomial(j**416*w**96*v**96*zv**8*s**8*r**40*cv**64*T**40)
require(coeff_C==2**816*3**512*beta**408,'explicit C monomial')
require(coeff_z==2**808*3**512*beta**416,'explicit z monomial')
require(poly_top.total_degree()==768,'top total degree')
result['exact_degree']=768
result['degree_certificate']={'C_monomial':{'j':408,'w':104,'v':96,'C':8,'s':8,'r':40,'c':64,'T':40},'coefficient':'2^816 * 3^512 * beta^408','z_monomial':{'j':416,'w':96,'v':96,'z':8,'s':8,'r':40,'c':64,'T':40},'z_coefficient':'2^808 * 3^512 * beta^416'}
# Supplemental signed modular evaluations and a deliberately incorrect final sign.
rng=random.Random(768141)
def val(d,vs,cs,p):
 arr=[]
 for n in d['nodes']:
  op=n[0]
  if op=='integer':q=n[1]
  elif op=='variable':q=vs[n[1]]
  elif op=='coefficient':q=cs[n[1]]
  else:
   x,y=(arr[j] for j in n[1:]);q=x+y if op=='add' else x-y if op=='sub' else x*y
  arr.append(q%p)
 return arr[d['output']]
negative=False
for p in (1000003,1000033,1000037):
 for k in range(120):
  vs={v:rng.randrange(-30,31) for v in minimal['variables']};cs={name:value%p for name,value in actual.items()}
  require(val(minimal,vs,cs,p)==val(reduced,vs,cs,p),'signed replay')
  mutated=json.loads(json.dumps(minimal));mutated['nodes'][-1][0]='add'
  if val(mutated,vs,cs,p)!=val(minimal,vs,cs,p):negative=True
require(negative,'negative control did not reject')
result['supplemental_signed_replays']=360
result['negative_control_rejected']=True
result['generic_sign_product_identity']=True
result['polynomial_identical_minimal_and_reduced']=True
result['prefix_exact_hash_checks']=True
result['scope']='Exact universal polynomial identities, topology, counts and degree. Inherited calibration and new existence theorem are ordinary mathematical proofs, not decided by finite tests.'
(ROOT/'CHECKS.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
