#!/usr/bin/env python3
"""Independent saved-source audit; no author or historical module execution."""
import argparse, hashlib, json
from collections import Counter
from fractions import Fraction
from pathlib import Path
if not __debug__: raise RuntimeError('Run without optimized Python')
AUTHOR_PINS = {'complete85_auxiliary_bezout_projection.py': '3f619205a670b420312ba31d52b89cd8c87c169763ddf6c317c2db44ef0698f0', 'complete85_auxiliary_bezout_projection.json': 'e7ddc113f96cde37efc9d1973daffa5e4cef221db2c1d1c6ad1cf1772cd59edc', 'complete85_auxiliary_bezout_projection.md': 'd8f91555bed114470ee5dfb742175079f2df25e9c04d75abbf16752e70a91a4b'}
PARENT_PINS = {
 'complete86_transport_quotient_shear.py':'c1cb668ae5538d168652c07627c00255d9c00a7d6373feb45da8c7c3806c9c45',
 'complete86_transport_quotient_shear.json':'77ec7894c68f16e8d2dbb48f7c444bf7ab5e2c08f895bdad877f61b8c9c96efc',
 'complete86_transport_quotient_shear.md':'fd0254d6cb0a35686cd824e3f29384c9aed8141444256ce0a9442133a2785541'}
FACTORS=['norm_first','norm_main','norm_input','norm_aux','norm_index','norm_transport','norm_strong']
FIXED=['Bm1','Kconstant','twice_cell_bits','inner_bits','MC','MF']
def require(v,m):
 if not v: raise ValueError(m)
def sha(b): return hashlib.sha256(b).hexdigest()
def stable(v): return json.dumps(v,sort_keys=True,separators=(',',':')).encode()
def same(a,b):
 if type(a)is not type(b):return False
 if isinstance(a,dict):return a.keys()==b.keys() and all(same(a[k],b[k])for k in a)
 if isinstance(a,list):return len(a)==len(b) and all(same(x,y)for x,y in zip(a,b))
 return a==b
def atom(v):return {((v,1),):1}
def const(v):return {():v} if v else {}
def add(a,b,s=1):
 z=dict(a)
 for m,c in b.items():z[m]=z.get(m,0)+s*c
 return {m:c for m,c in z.items()if c}
def mul(a,b):
 z={}
 for m,c in a.items():
  for n,d in b.items():
   e=dict(m)
   for v,k in n:e[v]=e.get(v,0)+k
   q=tuple(sorted(e.items()));z[q]=z.get(q,0)+c*d
 return {m:c for m,c in z.items()if c}
def power(a,n):
 z=const(1)
 for _ in range(n):z=mul(z,a)
 return z
def sum_polys(xs):
 z={}
 for x in xs:z=add(z,x)
 return z
def plus(a,b,s=1):
 d=max(a[0],b[0]);return d,add(a[1]if a[0]==d else{},b[1]if b[0]==d else{},s)
def times(a,b):return a[0]+b[0],mul(a[1],b[1])
def ledger(p):
 require(len(p['free'])==len(set(p['free'])),'unique supplied leaves')
 degrees={v:0 if v in FIXED else 1 for v in p['free']};defs={};counts=Counter()
 for n,o,a,b in p['source']:
  require(n not in degrees and o in ('+','-','*'),'fresh supported row')
  require(all(type(v)is int or type(v)is str and v in degrees for v in (a,b)),'strict closed source')
  da,db=(degrees.get(v,0)for v in (a,b));degrees[n]=da+db if o=='*'else max(da,db)
  defs[n]=(a,b);counts['M'if o=='*'else'A']+=1
 seen=set();leaves=set();todo=[p['output']]
 while todo:
  n=todo.pop()
  if type(n)is int:continue
  if n not in defs:leaves.add(n)
  elif n not in seen:seen.add(n);todo.extend(defs[n])
 require(seen==set(defs) and leaves==set(p['free']),'all gates and declared coordinates live')
 return dict(operations=len(defs),M=counts['M'],A=counts['A'],naive_degree_upper=degrees[p['output']])
def source_reconstruction(old,new):
 remove={'of','jc','linear_difference','norm_linear','eight_units'}
 expected={n:[n,o,a,b] for n,o,a,b in old['source'] if n not in remove}
 expected.update({r[0]:r for r in [
  ['auxiliary_Tf','*','auxiliary_quotient','f'],
  ['auxiliary_Tf_minus_one','-','auxiliary_Tf',1],
  ['auxiliary_c_Tf','*','R10a','auxiliary_Tf_minus_one'],
  ['auxiliary_R_f2','*','r_lhs','L16'],
  ['aux_u_rhs','-','auxiliary_c_Tf','auxiliary_R_f2'],
  ['polynomial','-','seven_units',1]]})
 require(expected=={r[0]:r for r in new['source']},'independent entire source reconstruction')
 require(new['free']==[('auxiliary_quotient'if n=='j'else n)for n in old['free']if n!='o'],'exact free-coordinate replacement')
 require(new['witnesses']==[n for n in new['free']if n not in FIXED+['x']] and len(new['witnesses'])==18,'exact positive witness interface')
 require(new['fixed_numerals']==FIXED and new['ordinary_input']=='x' and new['normalized']is True and new['output']=='polynomial','compiler interface retained')
 uses=lambda v:[r[0]for r in old['source']if v in r[2:]]
 require(uses('o')==['of'] and uses('j')==['jc'],'old coordinates private to proved cones')
 require(uses('norm_linear')==['eight_units'] and uses('eight_units')==['polynomial'],'omitted final factor fully accounted')
 require(old['source'][-1]==['polynomial','-','eight_units',1],'actual full parent finalizer')
 return len(set(expected)&{r[0]for r in old['source']})-2

def local_and_finalizer_proofs():
 c,f,i,d,R,T,K=[atom(n)for n in ('c','f','i','Delta','R','T','index_difference')]
 q=mul(d,mul(power(i,2),power(c,4)));Ns=add(power(f,2),q,-1);Nk=add(K,R,-1)
 o=add(mul(c,T),mul(R,f),-1)
 j=add(add(mul(T,f),mul(R,mul(d,mul(power(i,2),power(c,3)))),-1),const(1),-1)
 V=add(mul(c,add(mul(T,f),const(1),-1)),mul(R,power(f,2)),-1)
 require(add(mul(o,f),c,-1)==V,'entire restored auxiliary expression')
 linear=add(add(V,mul(j,c),-1),K)
 correction=add(Nk,mul(R,add(const(1),Ns,-1)))
 require(linear==correction,'exact omitted factor correction')
 # Inverse quotient identities become integral/true on the retained strong
 # and coupled-index equations. These are not off-zero domain assertions.
 require(add(mul(o,f),R)==add(mul(c,add(j,const(1))),mul(R,add(const(1),Ns,-1))),'divisibility correction identity')
 oldunits=[atom(n)for n in FACTORS];product=const(1)
 for z in oldunits:product=mul(product,z)
 corr=add(atom('norm_index'),mul(atom('R'),add(const(1),atom('norm_strong'),-1)))
 child=add(product,const(1),-1);parent=add(mul(product,corr),const(1),-1)
 require(add(parent,const(1))==mul(add(child,const(1)),corr),'full product-minus-one correction')
 # Prove, without using unit equations, each cancellation used in degrees.
 x,a,b,g,h=[atom(n)for n in ('X','a','c','gamma','H')]
 left=add(power(sum_polys([x,mul(a,b),g]),2),mul(add(power(a,2),h),power(b,2)),-1)
 v=add(x,g);right=add(mul(v,add(v,mul(const(2),mul(a,b)))),mul(h,power(b,2)),-1)
 require(left==right,'all-value norm cancellation')
 return dict(auxiliary_identity=True,omitted_factor_identity=True,inverse_divisibility_correction=True,full_finalizer_identity=True,norm_cancellation_identity=True)

def actual_finalizers(old,new):
 def expand(p,names):
  defs={r[0]:r[1:]for r in p['source']};env={n:atom(n)for n in names}
  def get(v):
   if type(v)is int:return const(v)
   if v not in env:
    o,a,b=defs[v];av,bv=get(a),get(b);env[v]=mul(av,bv)if o=='*'else add(av,bv,1 if o=='+'else-1)
   return env[v]
  return get(p['output'])
 child=expand(new,FACTORS);parent=expand(old,FACTORS+['norm_linear'])
 product=const(1)
 for n in FACTORS:product=mul(product,atom(n))
 require(child==add(product,const(1),-1),'literal entire child finalizer')
 require(parent==add(mul(product,atom('norm_linear')),const(1),-1),'literal entire parent finalizer')
 return dict(complete_parent_factors=8,complete_child_factors=7,full_source_finalizers=2)

def degree(p):
 defs={r[0]:r[1:]for r in p['source']}
 guards={'norm_main':['-','L15','Ac2'],'L15':['*','R14','R14'],'R14':['+','D1','gam'],'D1':['+','wn2','cam2'],'cam2':['*','R10a','R12'],
 'norm_input':['-','mu2','scaled_kappa2'],'mu2':['*','exponent_rhs','exponent_rhs'],'exponent_rhs':['+','exponent_partial','modulus_multiple'],'exponent_partial':['+','W','difference_multiple'],'difference_multiple':['*','index_rhs','R12'],
 'Ac2':['*','A','c2'],'c2':['*','R10a','R10a'],'scaled_kappa2':['*','A','kappa2'],'kappa2':['*','index_rhs','index_rhs'],'A':['+','a_square','a4m5'],'a_square':['*','R12','R12']}
 require(all(defs[n]==row for n,row in guards.items()),'literal norm cone guards')
 e={n:(0 if n in FIXED else 1,atom(n))for n in p['free']}
 for n,o,a,b in p['source']:
  av=e[a]if type(a)is str else(0,const(a));bv=e[b]if type(b)is str else(0,const(b))
  v=times(av,bv)if o=='*'else plus(av,bv,1 if o=='+'else-1)
  if n in ('norm_main','norm_input'):
   off='wn2'if n=='norm_main'else'W';shift='gam'if n=='norm_main'else'modulus_multiple';ordinate='R10a'if n=='norm_main'else'index_rhs'
   t=plus(e[off],e[shift]);v=plus(times(t,plus(t,times((0,const(2)),times(e['R12'],e[ordinate])))),times(e['a4m5'],times(e[ordinate],e[ordinate])),-1)
  e[n]=v
  require(bool(v[1]),'nonzero symbolic top form '+n)
 q=mul(atom('Bm1'),atom('Jrep'));k=add(atom('eta'),atom('zeta'));g=add(atom('rho'),atom('sigma'))
 c1=q
 for n in ('F','Z','alpha'):c1=add(c1,atom(n),-1)
 c1=add(c1,mul(atom('twice_cell_bits'),atom('x')),-1)
 t2=add(mul(atom('w'),c1),mul(atom('transport_quotient'),q),-1)
 wanted=const(32)
 for poly,exp in [(q,103),(atom('h'),1),(g,1),(atom('delta'),2),(atom('i'),4),(k,13),(atom('w'),16),(atom('s'),29),(t2,1),(atom('auxiliary_quotient'),2),(atom('f'),2)]:wanted=mul(wanted,power(poly,exp))
 require(e['polynomial']==(175,wanted),'entire uniform homogeneous leading form')
 fd=[e[n][0]for n in FACTORS];require(fd==[22,18,32,60,7,2,34]and sum(fd)==175,'actual exact factor degrees')
 return dict(exact_degree=175,factor_degrees=fd,whole_leading_monomials=len(wanted),leading_form_sha256=sha(stable(sorted((list(m),c)for m,c in wanted.items()))),uniform_fixed_numeral_proof=True)

def evaluate(p,v):
 e=dict(v)
 for n,o,a,b in p['source']:
  a=e[a]if type(a)is str else a;b=e[b]if type(b)is str else b
  e[n]=a*b if o=='*'else a+b if o=='+'else a-b
 return e

def numeric_corrections(old,new):
 counts=Counter()
 for case in range(24):
  values={n:((j+3)*(case+5)%11)-5 for j,n in enumerate(new['free'])}
  if case>=16:values={n:Fraction(v,3)for n,v in values.items()}
  e=evaluate(new,values);c,f,i,R,T,d=(e[n]for n in ('R10a','f','i','r_lhs','auxiliary_quotient','A'))
  restored={n:values[n]for n in old['free']if n not in ('o','j')}
  restored.update(o=c*T-R*f,j=T*f-R*d*i*i*c*c*c-1)
  parent=evaluate(old,restored)
  for n in FACTORS:require(parent[n]==e[n],'entire retained factor '+n)
  require(parent['norm_linear']==e['norm_index']+R*(1-e['norm_strong']),'evaluated omitted factor')
  require(parent['polynomial']+1==(e['polynomial']+1)*parent['norm_linear'],'entire evaluated correction')
  counts['whole_corrections']+=1;counts['retained_factor_values']+=7
  if case>=16:counts['rational_corrections']+=1
 return dict(counts)

def verify(root,author_root):
 require(len(AUTHOR_PINS)==3,'author must be frozen')
 blobs={}
 for manifest,base in [(PARENT_PINS,root),(AUTHOR_PINS,author_root)]:
  for name,pin in manifest.items():
   b=(base/name).read_bytes();require(sha(b)==pin,'pinned '+name);blobs[name]=b
 rec=json.loads(blobs['complete85_auxiliary_bezout_projection.json']);require(rec['source_sha256']==sha(blobs['complete85_auxiliary_bezout_projection.py']),'author receipt self-source pin')
 old=json.loads(blobs['complete86_transport_quotient_shear.json'])['forms'][0]['packet'];new=rec['packet']
 for name,pin in rec['parent_pins'].items():require(sha((root/name).read_bytes())==pin,'author proof dependency '+name)
 unchanged=source_reconstruction(old,new);require(new['exact_degree']==175 and new['factor_exact_degrees']==[22,18,32,60,7,2,34],'saved degree metadata');ld=ledger(new);require(ld==dict(operations=85,M=48,A=37,naive_degree_upper=185),'independent full arithmetic ledger')
 return dict(status='PASS',source_sha256=sha(Path(__file__).read_bytes()),author_pins=AUTHOR_PINS,parent_pins=PARENT_PINS,authenticated_proof_dependencies=rec['parent_pins'],ledger=ld,positive_witnesses=18,source_reconstruction=dict(complete=True,unchanged_rows=unchanged),identities=local_and_finalizer_proofs(),finalizers=actual_finalizers(old,new),degree=degree(new),numeric=numeric_corrections(old,new),scope='Independent saved complete source, exact full correction and uniform degree; positive-zero transfer is separately proved in author/math notes. No author or historical Python executed; no full native Pell zero materialized; no off-zero positive-orthant bijection claimed.')
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',type=Path,required=True);ap.add_argument('--author-root',type=Path);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args()
 r=verify(a.root,a.author_root or a.root)
 if a.expect:require(same(r,json.loads(a.expect.read_text())),'exact typed saved receipt')
 if a.output:a.output.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
 print(json.dumps(dict(status='PASS',ledger=r['ledger'],degree=r['degree'],numeric=r['numeric'])))
if __name__=='__main__':main()
