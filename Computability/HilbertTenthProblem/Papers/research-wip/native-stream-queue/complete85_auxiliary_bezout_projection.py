#!/usr/bin/env python3
"""Complete universal85 auxiliary quotient; authenticated JSON-only parents."""
import argparse,hashlib,json,random,copy,tempfile
from pathlib import Path
from collections import Counter
from fractions import Fraction
if not __debug__:raise RuntimeError('Run without -O')
PINS={'complete86_transport_quotient_shear.py': 'c1cb668ae5538d168652c07627c00255d9c00a7d6373feb45da8c7c3806c9c45', 'complete86_transport_quotient_shear.json': '77ec7894c68f16e8d2dbb48f7c444bf7ab5e2c08f895bdad877f61b8c9c96efc', 'complete86_transport_quotient_shear.md': 'fd0254d6cb0a35686cd824e3f29384c9aed8141444256ce0a9442133a2785541', 'complete86_factored_first_root.md': '9f2b50449e0724e523e9dd5d022f229b77504976f23ee52ca2917cf11ceb322b', 'complete75_coupled_index_linear88.md': '1533ef2411347335704f46a8a1020d8d46dea1147b03e9c9d35684a687172e39', 'complete75_normalized_strong87.md': '9c1cfa3ccd5a71c127c8e6aa341fad6e857788d708129e04ea177dbbcdccfb3b', 'complete75_asymmetric_scale_tradeoffs.md': '3fb7aad219cc05570531c2e806bd4f4998681777963063761106400514a146c2', 'complete75_reversed_auxiliary89.md': '4eddb6627b6261b1d8f8617006e443908574c0b7b2d3fdda15ff85dc86bd9700', '../../1980/PELL_RELAXED_AUXILIARY_PROOF.md': '9849260ea2776d26e9b615e0e1ed6fcd9b1c9e0e4cedb6cd8aaa2c0346ecbc90', 'complete113_asymmetric_retained109.md': 'cee18b24b50fcea5f3cd6fa9fb20f8dbdd5ae9f5e99107e24ffff4e66b3305f0'}
PINS.update({'complete86_factored_first_root.py':'29cf4100b846bcbabb05185550b7d9ead6b572746048b94998a13c83eeaff40f','complete86_factored_first_root.json':'2dfe46fe9c5537ff51eb3c542806c58242238363e6018f9daab7eabf0b6fe61e'})

def require(x, message):
 if not x: raise ValueError(message)
def sha(b): return hashlib.sha256(b).hexdigest()
def typed(a,b):
 if type(a) is not type(b): return False
 if isinstance(a,dict): return a.keys()==b.keys() and all(typed(a[k],b[k]) for k in a)
 if isinstance(a,list): return len(a)==len(b) and all(typed(x,y) for x,y in zip(a,b))
 return a==b
# Independent sparse polynomial arithmetic for the complete outer cones.
def const(x): return {():x} if x else {}
def atom(x): return {((x,1),):1}
def add(a,b,sign=1):
 z=dict(a)
 for m,c in b.items():
  z[m]=z.get(m,0)+sign*c
  if not z[m]: del z[m]
 return z
def mul(a,b):
 z={}
 for m,c in a.items():
  for n,d in b.items():
   e=dict(m)
   for v,k in n:e[v]=e.get(v,0)+k
   mon=tuple(sorted(e.items()));z[mon]=z.get(mon,0)+c*d
 return {m:c for m,c in z.items() if c}
def power(a,n):
 z=const(1)
 while n:
  if n&1:z=mul(z,a)
  a=mul(a,a);n//=2
 return z
def total(xs):
 z={}
 for x in xs:z=add(z,x)
 return z
def scale(n,p): return mul(const(n),p)
def value(x,e): return e[x] if isinstance(x,str) else const(x)
def poly_cone(rows,free,target,cuts):
 defs={n:(o,a,b) for n,o,a,b in rows};env={n:atom(n) for n in free};env.update(cuts)
 def go(n):
  if type(n) is int:return const(n)
  if n not in env:
   op,a,b=defs[n];a,b=go(a),go(b);env[n]=mul(a,b) if op=='*' else add(a,b,1 if op=='+' else -1)
  return env[n]
 return go(target)
def run(rows,v):
 e=dict(v)
 for n,o,a,b in rows:
  a=e[a] if isinstance(a,str) else a;b=e[b] if isinstance(b,str) else b
  e[n]=a*b if o=='*' else a+b if o=='+' else a-b
 return e
def account(p):
 free=p['free'];degree={n:1 for n in free};defs={};c=Counter()
 require(len(free)==len(set(free)),'unique input leaves')
 for n,o,a,b in p['source']:
  require(n not in degree and o in ('+','-','*'),'fresh legal gate')
  require(all(type(t) is int or type(t) is str and t in degree for t in (a,b)),'closed exact-type schedule')
  da,db=(degree.get(t,0) for t in (a,b));degree[n]=da+db if o=='*' else max(da,db)
  defs[n]=(a,b);c['M' if o=='*' else 'A']+=1
 seen=set();used=set();stack=[p['output']]
 while stack:
  n=stack.pop()
  if type(n) is int:continue
  if n not in defs:used.add(n)
  elif n not in seen:seen.add(n);stack.extend(defs[n])
 require(seen==set(defs) and used==set(free),'all gates and supplied leaves live')
 ans=dict(operations=len(defs),M=c['M'],A=c['A'],degree_upper=degree[p['output']])
 require(ans==p['ledger'],'literal full ledger')
 return ans
# Exact ring-expression DAG: addition is a sparse linear combination of
# nonlinear node IDs, sufficient for D=(D-u)+u without a proof cut.
class Ring:
 def __init__(self):self.memo={};self.next=1
 def leaf(self,key):
  if key not in self.memo:self.memo[key]=self.next;self.next+=1
  return ((self.memo[key],1),)
 def number(self,n):return ((0,n),) if n else ()
 def op(self,o,a,b):
  if o in ('+','-'):
   z=dict(a)
   for k,v in b:z[k]=z.get(k,0)+(v if o=='+' else -v)
   return tuple(sorted((k,v) for k,v in z.items() if v))
  if not a or not b:return ()
  if len(a)==1 and a[0][0]==0:return tuple((k,a[0][1]*v) for k,v in b)
  if len(b)==1 and b[0][0]==0:return tuple((k,b[0][1]*v) for k,v in a)
  return self.leaf(('*',tuple(sorted((a,b)))))
 def execute(self,p,env):
  e=dict(env)
  for n,o,a,b in p['source']:
   av=e[a] if isinstance(a,str) else self.number(a);bv=e[b] if isinstance(b,str) else self.number(b)
   e[n]=self.op(o,av,bv)
  return e



FACTOR_NAMES=['norm_first','norm_main','norm_input','norm_aux','norm_index','norm_transport','norm_strong']
NEW='auxiliary_quotient'
REMOVED={'of','aux_u_rhs','jc','linear_difference','norm_linear','eight_units'}

def canonical_parent(root):
 blobs={}
 for n,h in PINS.items():
  path=Path(root)/n
  if not path.exists():path=Path(__file__).resolve().parent/n
  b=path.read_bytes();require(sha(b)==h,'frozen parent '+n);blobs[n]=b
 r=json.loads(blobs['complete86_transport_quotient_shear.json'])
 require(r['source_sha256']==sha(blobs['complete86_transport_quotient_shear.py']),'parent selfsource')
 require(r['parent_pins']=={n:PINS[n] for n in ('complete86_factored_first_root.py','complete86_factored_first_root.json','complete86_factored_first_root.md')},'actual complete parent provenance')
 p=r['forms'][0]['packet'];require(p['normalized'] is True and p['ledger']['operations']==86,'exact normalized86 parent')
 return p

def _make(parent):
 d={r[0]:r for r in parent['source']}
 require(d['of']==['of','*','o','f'] and d['aux_u_rhs']==['aux_u_rhs','-','of','R10a'],'actual old auxiliary coordinate')
 require(d['jc']==['jc','*','j','R10a'] and d['linear_difference']==['linear_difference','-','aux_u_rhs','jc'] and d['norm_linear']==['norm_linear','+','linear_difference','index_difference'],'actual linear factor')
 require([r for r in parent['source'] if 'o' in r[2:]]==[d['of']] and [r for r in parent['source'] if 'j' in r[2:]]==[d['jc']],'all consumers of removed supplied coordinates')
 require([r for r in parent['source'] if 'norm_linear' in r[2:]]==[['eight_units','*','seven_units','norm_linear']],'private omitted final factor')
 require(d['norm_strong']==['norm_strong','-','L16','strong_difference'] and d['L16']==['L16','*','f','f'],'normalized strong root square is already paid')
 newrows=[['auxiliary_Tf','*',NEW,'f'],['auxiliary_Tf_minus_one','-','auxiliary_Tf',1],['auxiliary_c_Tf','*','R10a','auxiliary_Tf_minus_one'],['auxiliary_R_f2','*','r_lhs','L16'],['aux_u_rhs','-','auxiliary_c_Tf','auxiliary_R_f2']]
 rows=[list(r) for r in parent['source'] if r[0] not in REMOVED]+newrows
 for r in rows:
  if r[0]=='polynomial':r[:]=['polynomial','-','seven_units',1]
 free=[NEW if v=='o' else v for v in parent['free'] if v!='j'];available=set(free);ordered=[]
 while rows:
  pending=[]
  for r in rows:
   if all(type(v)is int or v in available for v in r[2:]):ordered.append(r);available.add(r[0])
   else:pending.append(r)
  require(len(pending)<len(rows),'literal source topological closure');rows=pending
 p=dict(source=ordered,free=free,output='polynomial',witnesses=[v for v in free if v not in parent['ledger']['fixed_numerals']+['x']],fixed_numerals=parent['ledger']['fixed_numerals'],ordinary_input='x',normalized=True)
 degrees={v:int(v not in p['fixed_numerals']) for v in free};ops=Counter()
 for n,o,a,b in ordered:degrees[n]=degrees.get(a,0)+degrees.get(b,0) if o=='*' else max(degrees.get(a,0),degrees.get(b,0));ops[o]+=1
 p['ledger']=dict(operations=len(ordered),M=ops['*'],A=ops['+']+ops['-'],degree_upper=degrees['polynomial'])
 p.update(exact_degree=175,factor_exact_degrees=[22,18,32,60,7,2,34],full_positive_zero_bijection=True,whole_positive_orthant_map=False,entire_polynomial_identity=False,scope='Positive ordinary input and18 positive witnesses, with exactly the inherited valid fixed-program numeral recipe. Full positive-zero bijection; offzero polynomial correction only.')
 # account uses degree one for numeral leaves, so use it for closure/liveness
 # with a matching elementary temporary bound, then retain fixed-slice bound.
 q=dict(p);elementary={n:1 for n in free}
 for n,o,a,b in ordered:elementary[n]=elementary.get(a,0)+elementary.get(b,0) if o=='*' else max(elementary.get(a,0),elementary.get(b,0))
 q['ledger']=dict(p['ledger'],degree_upper=elementary['polynomial']);account(q)
 require(p['ledger']['operations']==85 and p['ledger']['M']==48 and p['ledger']['A']==37 and len(p['witnesses'])==18,'full literal85 ledger and18 positive witnesses')
 return p

def local_proof():
 c,t,f,r,d,i,k=[atom(v) for v in ('c','T','f','R','Delta','i','K')]
 f2=power(f,2);S=add(f2,mul(d,mul(power(i,2),power(c,4))),-1)
 restored_o=add(mul(c,t),mul(r,f),-1)
 restored_j=add(add(mul(t,f),mul(r,mul(d,mul(power(i,2),power(c,3)))),-1),const(1),-1)
 V=add(mul(c,add(mul(t,f),const(1),-1)),mul(r,f2),-1)
 require(add(mul(restored_o,f),c,-1)==V,'actual auxiliary coordinate graph identity')
 linear=add(add(V,mul(restored_j,c),-1),k)
 correction=add(add(k,r,-1),mul(r,add(const(1),S,-1)))
 require(linear==correction,'exact omitted-factor correction Nk+R(1-Ns)')
 # In fact V+R-c*j=R*(1-Ns), explicitly retained in the correction.
 require(add(add(V,r),mul(c,restored_j),-1)==mul(r,add(const(1),S,-1)),'offzero divisibility correction')
 return dict(auxiliary_graph=True,omitted_factor_correction=True,zero_only_divisibility=True)

def complete_proof(parent,child):
 old={r[0]:r for r in parent['source']};new={r[0]:r for r in child['source']}
 require(all(new[n]==row for n,row in old.items() if n not in REMOVED|{'polynomial'}),'every retained old instruction literal')
 ring=Ring();common={v:ring.leaf(('free',v)) for v in child['free']};V=ring.leaf(('proved_auxiliary_V',))
 def evaluate(p):
  e=dict(common);e.update({v:ring.leaf(('removed',v)) for v in ('o','j')})
  for n,o,a,b in p['source']:
   av=e[a] if type(a)is str else ring.number(a);bv=e[b] if type(b)is str else ring.number(b)
   e[n]=V if n=='aux_u_rhs' else ring.op(o,av,bv)
  return e
 a=evaluate(parent);b=evaluate(child)
 require(all(a[n]==b[n] for n in FACTOR_NAMES),'all seven retained complete factors after proved auxiliary cut')
 # Independently expand literal product finalizers with factor ports free.
 oldf=FACTOR_NAMES+['norm_linear'];pa=poly_cone(parent['source'],parent['free'],'polynomial',{n:atom(n) for n in oldf})
 pb=poly_cone(child['source'],child['free'],'polynomial',{n:atom(n) for n in FACTOR_NAMES})
 require(add(pa,const(1))==mul(add(pb,const(1)),atom('norm_linear')),'whole product correction, not polynomial equality')
 return dict(retained_instructions=len(old)-len(REMOVED)-1,retained_factor_identities=7,complete_product_correction=True)

def degree(child):
 # Full dense univariate coefficient expansions over two prime fields,
 # plus the uniform homogeneous proof stated in the companion.
 results=[]
 for B in (16,32):
  prime=1000000007;weights={v:1+int(sha((v+str(B)).encode()),16)%7 for v in child['witnesses']+['x']}
  numerals=dict(Bm1=B-1,Kconstant=3,twice_cell_bits=8,inner_bits=7,MC=1,MF=B)
  env={v:[0,weights[v]] if v in weights else [numerals[v]] for v in child['free']}
  def plus(a,b,s=1):
   z=[0]*max(len(a),len(b))
   for j,c in enumerate(a):z[j]+=c
   for j,c in enumerate(b):z[j]+=s*c
   z=[c%prime for c in z]
   while len(z)>1 and z[-1]==0:z.pop()
   return z
  def product(a,b):
   z=[0]*(len(a)+len(b)-1)
   for j,c in enumerate(a):
    for k,d in enumerate(b):z[j+k]=(z[j+k]+c*d)%prime
   while len(z)>1 and z[-1]==0:z.pop()
   return z
  for n,o,a,b in child['source']:
   av=env[a] if type(a)is str else [a%prime];bv=env[b] if type(b)is str else [b%prime];env[n]=product(av,bv) if o=='*' else plus(av,bv,1 if o=='+' else -1)
  require([len(env[n])-1 for n in FACTOR_NAMES]==[22,18,32,60,7,2,34] and len(env['polynomial'])-1==175,'actual full coefficient expansion degrees')
  Q=(B-1)*weights['Jrep'];kg=weights['eta']+weights['zeta'];gg=weights['rho']+weights['sigma'];ctop=Q-weights['F']-weights['Z']-weights['alpha']-8*weights['x'];tt=weights['w']*ctop-weights['transport_quotient']*Q
  lead=32*Q**103*weights['h']*gg*weights['delta']**2*weights['i']**4*kg**13*weights['w']**16*weights['s']**29*weights[NEW]**2*weights['f']**2*tt
  require(lead%prime==env['polynomial'][-1]!=0,'uniform leader specialized to actual full coefficient')
  results.append(dict(B=B,exact_degree=175,factor_degrees=[22,18,32,60,7,2,34],leading_coefficient=env['polynomial'][-1],coefficient_sha256=sha(json.dumps(env['polynomial']).encode())))
 return results

def numerical_corrections(parent,child):
 rng=random.Random(8585);count=0
 for case in range(32):
  v={n:rng.randint(1,3) if case<8 else rng.randint(-2,3) for n in child['free']}
  v.update(Bm1=15,Kconstant=3,twice_cell_bits=8,inner_bits=7,MC=1,MF=16)
  if case>=24:v={n:Fraction(a,3) if n not in child['fixed_numerals'] else a for n,a in v.items()}
  ne=run(child['source'],v);c=ne['R10a'];f=v['f'];r=ne['r_lhs'];d=ne['A'];i=v['i'];T=v[NEW]
  restored={n:v[n] for n in parent['free'] if n not in ('o','j')};restored['o']=c*T-r*f;restored['j']=T*f-r*d*i*i*c**3-1
  pe=run(parent['source'],restored);multiplier=ne['norm_index']+r*(1-ne['norm_strong'])
  require(all(pe[n]==ne[n] for n in FACTOR_NAMES),'all seven full evaluated factors')
  require(pe['norm_linear']==multiplier and pe['polynomial']+1==(ne['polynomial']+1)*multiplier,'full signed/rational offzero correction')
  count+=1
 return dict(full_corrections=count,rational=8,positive_offzero_restoration_claimed=False)

def build(*,root):
 return _make(canonical_parent(root))

def checked(packet,*,root):
 expected=build(root=root)
 require(typed(packet,expected),'exact canonical complete85 packet')
 return expected

def _assignment(packet,values,signed):
 require(type(signed)is bool,'exact Boolean signed flag')
 require(type(values)is dict and set(values)==set(packet['free']),'exact complete assignment keys')
 require(all(type(v)is int for v in values.values()),'exact integer assignment values')
 if not signed:require(all(values[n]>0 for n in packet['witnesses']+['x']),'positive supplied witnesses/input')
 return dict(values)

def evaluate(packet,values,*,root,signed=False):
 p=checked(packet,root=root);v=_assignment(p,values,signed)
 return run(p['source'],v)[p['output']]

def integer_restore(packet,values,*,root):
 p=checked(packet,root=root);v=_assignment(p,values,True);e=run(p['source'],v)
 c,f,R,D,i,T=e['R10a'],v['f'],e['r_lhs'],e['A'],v['i'],v[NEW]
 old=canonical_parent(root);out={n:v[n] for n in old['free'] if n not in ('o','j')}
 out['o']=c*T-R*f;out['j']=T*f-R*D*i*i*c**3-1
 return out

def restore_zero(packet,values,*,root):
 p=checked(packet,root=root);v=_assignment(p,values,False)
 require(run(p['source'],v)[p['output']]==0,'complete positive child zero required')
 out=integer_restore(p,v,root=root);old=canonical_parent(root)
 require(all(out[n]>0 for n in old['witnesses']) and run(old['source'],out)[old['output']]==0,'proved positive parent restoration')
 return out

def project_parent_zero(values,*,root):
 old=canonical_parent(root);v=_assignment(old,values,False);e=run(old['source'],v)
 require(e[old['output']]==0,'complete positive parent zero required')
 c=e['R10a'];numerator=v['o']+e['r_lhs']*v['f']
 require(c>0 and numerator%c==0,'proved auxiliary quotient integrality')
 p=build(root=root);out={n:v[n] for n in p['free'] if n!=NEW};out[NEW]=numerator//c
 require(out[NEW]>0 and run(p['source'],out)[p['output']]==0,'proved positive child projection')
 return out

def api_checks(root,p):
 rejects=0
 def reject(call):
  nonlocal rejects
  try:call()
  except (ValueError,TypeError):rejects+=1
  else:raise ValueError('malformed input accepted')
 values={n:1 for n in p['free']};values.update(Bm1=15,Kconstant=3,twice_cell_bits=8,inner_bits=7,MC=1,MF=16)
 for mutation in (lambda q:q['ledger'].__setitem__('operations',84),lambda q:q['source'][0].__setitem__(1,'+'),lambda q:q.__setitem__('exact_degree',True),lambda q:q['witnesses'].pop(),lambda q:q.__setitem__('extra',0)):
  bad=copy.deepcopy(p);mutation(bad);reject(lambda:checked(bad,root=root))
 for bad in ({},dict(values,extra=1),dict(values,x=True),dict(values,x=Fraction(1)),dict(values,x=0)):
  reject(lambda bad=bad:evaluate(p,bad,root=root))
 reject(lambda:evaluate(p,values,root=root,signed=1));reject(lambda:restore_zero(p,values,root=root))
 old=canonical_parent(root);ov={n:1 for n in old['free']};reject(lambda:project_parent_zero(ov,root=root))
 a=build(root=root);a['source'][0][1]='+';a['free'].clear();require(typed(build(root=root),p),'independent canonical packet copies')
 a=checked(p,root=root);a['witnesses'].clear();require(typed(build(root=root),p),'independent checked copy')
 out=integer_restore(p,values,root=root);out['o']=0;require(integer_restore(p,values,root=root)['o']!=0,'independent polynomial map copies')
 warm=0
 with tempfile.TemporaryDirectory(prefix='pascal85_pins_') as tmp:
  sandbox=Path(tmp)/'WIP';sandbox.mkdir()
  for n,h in PINS.items():
   original=Path(root)/n
   if not original.exists():original=Path(__file__).resolve().parent/n
   target=sandbox/n;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(original.read_bytes())
  build(root=sandbox)
  for n in PINS:
   target=sandbox/n;b=target.read_bytes();target.write_bytes(b+b' ')
   reject(lambda:build(root=sandbox));target.write_bytes(b);warm+=1
 return dict(rejections=rejects,warm_pins=warm,copies=3,complete_zero_map_fixtures_materialized=False)

def verify(root):
 parent=canonical_parent(root);p=_make(parent)
 return dict(status='PASS',source_sha256=sha(Path(__file__).read_bytes()),parent_pins=PINS,packet=p,local=local_proof(),structural=complete_proof(parent,p),degree_checks=degree(p),numeric=numerical_corrections(parent,p),api=api_checks(root,p),scope='Normalized parent only; complete literal85=48M37A and18 positive witnesses. Full offzero correction, not same-polynomial equality. Positive-zero bijection and uniform exact degree175 are proved in the companion; no giant native Pell tuple is materialized.')

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();r=verify(a.root)
 if a.expect:require(typed(r,json.loads(a.expect.read_text())),'exact typed saved receipt')
 if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 print(json.dumps(dict(status=r['status'],ledger=r['packet']['ledger'],witnesses=len(r['packet']['witnesses']),structural=r['structural'],numeric=r['numeric'])))
if __name__=='__main__':main()
