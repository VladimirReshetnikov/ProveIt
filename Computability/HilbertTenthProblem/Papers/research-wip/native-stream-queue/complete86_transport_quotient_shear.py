#!/usr/bin/env python3
"""Positive transport quotient shear in both complete first-root polynomials."""
import argparse,copy,hashlib,json,random,subprocess,sys,tempfile
from collections import Counter
from fractions import Fraction
from pathlib import Path
if not __debug__:raise RuntimeError('Run without -O')
PINS={
 'complete86_factored_first_root.py':'29cf4100b846bcbabb05185550b7d9ead6b572746048b94998a13c83eeaff40f',
 'complete86_factored_first_root.json':'2dfe46fe9c5537ff51eb3c542806c58242238363e6018f9daab7eabf0b6fe61e',
 'complete86_factored_first_root.md':'9f2b50449e0724e523e9dd5d022f229b77504976f23ee52ca2917cf11ceb322b'}
CONSTANTS=['Bm1','Kconstant','twice_cell_bits','inner_bits','MC','MF']
FACTORS=['norm_first','norm_main','norm_input','norm_aux','norm_index','norm_transport','norm_strong','norm_linear']
def need(ok,msg):
 if not ok:raise ValueError(msg)
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys()and all(exact(a[k],b[k])for k in a)
 if type(a)is list:return len(a)==len(b)and all(exact(x,y)for x,y in zip(a,b))
 return a==b
def sha(b):return hashlib.sha256(b).hexdigest()
def authenticate(root):
 root=Path(__file__).resolve().parent if root is None else Path(root);blobs={}
 for name,pin in PINS.items():
  b=(root/name).read_bytes();need(sha(b)==pin,'Pinned parent '+name);blobs[name]=b
 return json.loads(blobs['complete86_factored_first_root.json'])
def canonical_parent(normalized=True,*,root=None):
 need(type(normalized)is bool,'Exact normalized flag')
 forms=authenticate(root)['forms'];need([f['normalized']for f in forms]==[True,False],'Both actual parents')
 return copy.deepcopy(forms[0 if normalized else 1])
def run(rows,values):
 e=dict(values)
 for n,o,a,b in rows:
  a=e[a]if type(a)is str else a;b=e[b]if type(b)is str else b;e[n]=a*b if o=='*'else a+b if o=='+'else a-b
 return e

def ledger(rows,witnesses):
 free=witnesses+['x']+CONSTANTS;known=set(free);need(len(known)==len(free),'Unique free coordinates')
 ds={n:0 if n in CONSTANTS else 1 for n in free};defs={};M=0
 for row in rows:
  need(type(row)is list and len(row)==4,'Exact gate row');n,o,a,b=row
  need(type(n)is str and n not in known and o in('+','-','*'),'Fresh legal gate')
  need(all(type(v)is int or type(v)is str and v in known for v in(a,b)),'Literal closure')
  da=ds[a]if type(a)is str else 0;db=ds[b]if type(b)is str else 0
  ds[n]=da+db if o=='*'else max(da,db);defs[n]=(a,b);known.add(n);M+=o=='*'
 live=set();todo=['polynomial']
 while todo:
  n=todo.pop()
  if type(n)is int or n in live:continue
  live.add(n);todo.extend(defs.get(n,()))
 need(set(defs)|set(free)<=live,'Every paid gate and supplied port live')
 return dict(operations=len(rows),M=M,A=len(rows)-M,certificate_operations=len(rows)-1,positive_witnesses=len(witnesses),all_gates_live=True,ordinary_input='x',fixed_numerals=CONSTANTS[:],degree_upper_bound=ds['polynomial'],factor_degree_bounds=[ds[n]for n in FACTORS])

def _rewrite(old):
 rows=old['source'];defs={n:[o,a,b]for n,o,a,b in rows}
 required={'q':['+','repunit',1],'wn2':['*','w','q'],'kinner':['+','Kconstant','wn2'],'innerC':['*','kinner','marked_rhs'],'transport_partial':['+','innerC','q_minus_F'],'local_rhs':['*','zplus','repunit'],'norm_transport':['-','transport_partial','local_rhs']}
 need(all(defs.get(n)==row for n,row in required.items()),'Actual full transport cone and q relation')
 need([n for n,o,a,b in rows if 'zplus'in(a,b)]==['local_rhs'],'Private old quotient')
 need([n for n,o,a,b in rows if 'kinner'in(a,b)]==['innerC'],'Private old coefficient sum')
 witnesses=['transport_quotient'if n=='zplus'else n for n in old['witnesses']]
 new=[[n,o,('transport_quotient'if a=='zplus'else a),('w'if n=='kinner'else 'transport_quotient'if b=='zplus'else b)]for n,o,a,b in rows]
 l=ledger(new,witnesses);mode=old['normalized'];need((l['operations'],l['M'],l['A'])==((86,48,38)if mode else(87,47,40)),'Entire unchanged operation count')
 degree=178 if mode else 134;need(l['degree_upper_bound']==(188 if mode else 144),'Literal syntactic bound')
 exact_factors=old['ledger']['factor_degrees'][:];need(exact_factors[5]==3,'Parent exact transport degree');exact_factors[5]=2;need(sum(exact_factors)==degree,'Inherited seven-factor upper bounds plus new quadratic transport')
 return dict(normalized=mode,source=new,output='polynomial',witnesses=witnesses,free=witnesses+['x']+CONSTANTS,ledger=l,exact_degree=degree,factor_exact_degrees=exact_factors,parent_exact_degree=179 if mode else 135,parent_pins=copy.deepcopy(PINS),coordinate={'old':'zplus','new':'transport_quotient','forward':'transport_quotient=zplus-w*marked_rhs','inverse':'zplus=transport_quotient+w*marked_rhs'},full_integer_coordinate_bijection=True,full_positive_zero_bijection=True,whole_positive_orthant_map=False,scope='Both complete universal fixed-program sources. Same19 positive witnesses and86/87 operations; exactdegrees178/134. Program numerals require the inherited compiler recipe, not merely arbitrary positive values.')
def build(normalized=True,*,root=None):return _rewrite(canonical_parent(normalized,root=root))
def rewrite(parent,*,root=None):
 need(type(parent)is dict and type(parent.get('normalized'))is bool,'Canonical parent type')
 old=canonical_parent(parent['normalized'],root=root);need(exact(parent,old),'Exact full parent packet');return _rewrite(old)
def checked(packet,*,root=None):
 need(type(packet)is dict and type(packet.get('normalized'))is bool,'Canonical packet type')
 p=build(packet['normalized'],root=root);need(exact(packet,p),'Exact current packet');return p
def polynomial_source(packet,*,root=None):return checked(packet,root=root)['source']
def value_check(values,free,positive=False):
 need(type(values)is dict and set(values)==set(free)and all(type(n)is str and type(v)is int for n,v in values.items()),'Exact integer supplied tuple')
 if positive:need(all(v>0 for v in values.values()),'Positive witnesses, input and numeral ports')
def evaluate(packet,values,*,signed=False,root=None):
 need(type(signed)is bool,'Exact signed flag');p=checked(packet,root=root);value_check(values,p['free'],not signed);return run(p['source'],values)[p['output']]
def content(v):return v['Bm1']*v['Jrep']+1-v['F']-v['Z']-v['alpha']-v['twice_cell_bits']*v['x']
def inverse_values(v):
 r=dict(v);r['zplus']=r.pop('transport_quotient')+v['w']*content(v);return r
def forward_values(v):
 r=dict(v);r['transport_quotient']=r.pop('zplus')-v['w']*content(v);return r
def integer_pullback(packet,values,*,root=None):
 p=checked(packet,root=root);value_check(values,p['free']);return inverse_values(values)
def integer_pushforward(packet,values,*,root=None):
 p=checked(packet,root=root);old=canonical_parent(p['normalized'],root=root);value_check(values,old['witnesses']+['x']+CONSTANTS);return forward_values(values)
def restore_child_zero(packet,values,*,root=None):
 p=checked(packet,root=root);value_check(values,p['free'],True);need(run(p['source'],values)[p['output']]==0,'Complete child zero required');r=inverse_values(values);need(min(r.values())>0,'Proved positive restored tuple');return r
def project_parent_zero(packet,values,*,root=None):
 p=checked(packet,root=root);old=canonical_parent(p['normalized'],root=root);value_check(values,old['witnesses']+['x']+CONSTANTS,True);need(run(old['source'],values)[old['output']]==0,'Complete parent zero required');r=forward_values(values);need(min(r.values())>0,'Proved positive projected tuple');return r

# Sparse local coefficient arithmetic uses independent r,w,K,C,t,U cuts.
def local_proof():
 zero=(0,)*6
 def const(c):return{zero:c}if c else{}
 def variable(i):return{tuple(int(j==i)for j in range(6)):1}
 def add(a,b,sign=1):
  c=dict(a)
  for m,v in b.items():c[m]=c.get(m,0)+sign*v
  return{m:v for m,v in c.items()if v}
 def mul(a,b):
  c={}
  for m,v in a.items():
   for n,w in b.items():
    key=tuple(x+y for x,y in zip(m,n));c[key]=c.get(key,0)+v*w
  return{m:v for m,v in c.items()if v}
 r,w,K,C,t,U=[variable(i)for i in range(6)];q=add(r,const(1));z=add(t,mul(w,C))
 old=add(add(mul(add(K,mul(w,q)),C),U),mul(z,r),-1)
 new=add(add(mul(add(K,w),C),U),mul(t,r),-1)
 need(old==new,'Exact transport polynomial under quotient shear');return len(new)
def structure(old,p):
 ids={}
 def intern(key):
  if key not in ids:ids[key]=len(ids)
  return ids[key]
 def evalrows(rows):
  e={n:intern(('free',n))for n in old['witnesses']+p['free']}
  for n,o,a,b in rows:
   at=lambda v:intern(('const',v))if type(v)is int else e[v]
   e[n]=intern(('proved_transport_shear',))if n=='norm_transport'else intern((o,at(a),at(b)))
  return e
 a=evalrows(old['source']);b=evalrows(p['source'])
 need(all(a[n]==b[n]for n in FACTORS+['polynomial']),'All other factors and complete finalizer unchanged at proved cut')
 return len(FACTORS)+1

def dense(rows,values,prime):
 def add(a,b,sign=1):
  c=[((a[i]if i<len(a)else 0)+sign*(b[i]if i<len(b)else 0))%prime for i in range(max(len(a),len(b)))]
  while len(c)>1 and c[-1]==0:c.pop()
  return c
 def mul(a,b):
  c=[0]*(len(a)+len(b)-1)
  for i,x in enumerate(a):
   for j,y in enumerate(b):c[i+j]=(c[i+j]+x*y)%prime
  while len(c)>1 and c[-1]==0:c.pop()
  return c
 e=dict(values)
 for n,o,a,b in rows:
  a=e[a]if type(a)is str else[a%prime];b=e[b]if type(b)is str else[b%prime];e[n]=mul(a,b)if o=='*'else add(a,b,1 if o=='+'else-1)
 return e

def verify(root):
 counts=Counter();forms=[];rng=random.Random(8617887134);need(local_proof()==4,'Four local monomials');counts['local_coefficient_identity']=1
 for normalized in(True,False):
  old=canonical_parent(normalized,root=root);p=build(normalized,root=root);counts['factor_and_finalizer_identities']+=structure(old,p)
  need(exact(rewrite(old,root=root),p)and exact(checked(p,root=root),p),'Public canonical source')
  degree_cases=[]
  for B,prime in((16,1009),(32,1013),(64,1019)):
   env={n:[j+1,2*j+3]for j,n in enumerate(p['witnesses']+['x'])}
   env.update({n:[v]for n,v in dict(Bm1=B-1,Kconstant=3+5*B,twice_cell_bits=2*(B.bit_length()-1),inner_bits=3,MC=B-2,MF=B+3).items()})
   polys=dense(p['source'],env,prime);wanted=[22,18,32,56 if normalized else 24,7,2,34 if normalized else 22,7]
   top={n:v[1]for n,v in env.items()if len(v)==2};Q=(B-1)*top['Jrep'];kk=top['eta']+top['zeta'];gamma=top['rho']+top['sigma'];C=Q-top['F']-top['Z']-top['alpha']-env['twice_cell_bits'][0]*top['x'];Nt=top['w']*C-top['transport_quotient']*Q
   leading=(-32*Q**107*top['h']**2*gamma*top['delta']**2*top['i']**4*kk**13*top['w']**17*top['s']**30*Nt)if normalized else(32*Q**79*top['h']**2*gamma*top['delta']**2*top['i']**2*top['f']**2*kk**9*top['w']**13*top['s']**22*Nt)
   need([len(polys[n])-1 for n in FACTORS]==wanted and len(polys['polynomial'])-1==p['exact_degree']and polys['polynomial'][-1]==leading%prime!=0,'Whole attained degree and uniform leading expression')
   degree_cases.append(dict(B=B,prime=prime,factor_degrees=wanted,degree=p['exact_degree'],leading_coefficient=polys['polynomial'][-1],all_coefficients_sha256=sha(json.dumps(polys['polynomial']).encode())));counts['dense_degree_checks']+=1
  for case in range(64):
   v={n:rng.randrange(-3,5)for n in p['free']}
   if case<16:v={n:rng.randrange(1,5)for n in v}
   if case>=48:v={n:Fraction(x,3)for n,x in v.items()};counts['rational_checks']+=1
   back=inverse_values(v);a=run(old['source'],back);b=run(p['source'],v)
   need(all(a[n]==b[n]for n in FACTORS+['polynomial'])and forward_values(back)==v,'Full algebraic identity and integer/rational coordinate roundtrip');counts['full_numeric_identities']+=1
   if case<48:
    need(evaluate(p,v,signed=case>=16,root=root)==b['polynomial']and exact(integer_pullback(p,v,root=root),back)and exact(integer_pushforward(p,back,root=root),v),'Public all-integer algebra')
  # Positive off-zero maps in both directions can leave the positive orthant.
  v={n:1 for n in p['free']};v.update(Bm1=15,Kconstant=83,twice_cell_bits=8,inner_bits=3,MC=14,MF=19,F=30)
  back=inverse_values(v);need(back['zplus']<0 and run(p['source'],v)['polynomial']!=0,'Inverse off-zero positivity boundary')
  ov={n:1 for n in old['witnesses']+['x']+CONSTANTS};ov.update(Bm1=31,Kconstant=83,twice_cell_bits=2,inner_bits=3,MC=14,MF=19,w=2)
  nv=forward_values(ov);need(nv['transport_quotient']<0 and run(old['source'],ov)['polynomial']!=0,'Forward off-zero positivity boundary')
  forms.append(dict(packet=p,degree_checks=degree_cases,inverse_positive_offzero_boundary=dict(assignment=v,restored_zplus=back['zplus']),forward_positive_offzero_boundary=dict(assignment=ov,projected_remainder=nv['transport_quotient'])))
 # Small local transport units include both signs; no full native tuple claim.
 local=[]
 for q in range(2,34):
  for F in range(1,q+3):
   for Z in(1,2):
    for alpha in(1,2):
     for ellx in(1,2,5):
      C=q-F-Z-alpha-ellx
      for w,K in((1,1),(2,3),(3,8)):
       for t in range(1,16):
        Nt=(K+w)*C+q-F-t*(q-1)
        if abs(Nt)==1:
         z=t+w*C;need(C>=0 and z>0 and (K+w*q)*C+q-F-z*(q-1)==Nt,'Positive local inverse for both unit signs');local.append([q,F,Z,alpha,ellx,w,K,t,Nt])
 need({r[-1]for r in local}=={-1,1},'Both transport unit signs represented');counts['local_unit_cases']=len(local)
 def reject(fn):
  try:fn()
  except(ValueError,TypeError,KeyError):counts['rejections']+=1
  else:raise ValueError('Malformed API accepted')
 p=build(root=root);old=canonical_parent(root=root);v={n:1 for n in p['free']}
 for mode in(0,1,None,'yes'):reject(lambda mode=mode:build(mode,root=root))
 for key in p:
  q=copy.deepcopy(p);del q[key];reject(lambda q=q:checked(q,root=root))
 for key,value in p.items():
  if type(value)in(dict,list):
   q=build(root=root);q[key].clear();need(exact(build(root=root),p),'Fresh mutable packet field');counts['copies']+=1
 for val in(True,1.0,Fraction(1)):
  vv=dict(v,x=val);reject(lambda vv=vv:evaluate(p,vv,signed=True,root=root))
 for mode in(0,1,None):reject(lambda mode=mode:evaluate(p,v,signed=mode,root=root))
 for fn in(restore_child_zero,):reject(lambda fn=fn:fn(p,v,root=root))
 reject(lambda:project_parent_zero(p,{n:1 for n in old['witnesses']+['x']+CONSTANTS},root=root))
 with tempfile.TemporaryDirectory(prefix='transport_shear_pins_')as tmp:
  blobs={n:Path(root,n).read_bytes()for n in PINS}
  for n,b in blobs.items():Path(tmp,n).write_bytes(b)
  build(root=tmp)
  for n,b in blobs.items():
   Path(tmp,n).write_bytes(b+b' ')
   for fn in(lambda:build(root=tmp),lambda:checked(p,root=tmp),lambda:integer_pullback(p,v,root=tmp)):reject(fn);counts['warm_pin_rejections']+=1
   Path(tmp,n).write_bytes(b)
 proc=subprocess.run([sys.executable,'-O',str(Path(__file__).resolve())],capture_output=True,text=True,timeout=30);need(proc.returncode!=0 and'Run without -O'in proc.stderr,'Optimized reject');counts['optimized_rejections']=1
 return dict(status='PASS_COMPLETE86_TRANSPORT_QUOTIENT_SHEAR',source_sha256=sha(Path(__file__).read_bytes()),parent_pins=copy.deepcopy(PINS),counts=dict(counts),forms=forms,local_unit_cases=local,scope='Full fixed-program universal86/178 and87/134 polynomials,19 positive witnesses. Full positive-zero bijection proved before compiler semantics, not whole-positive-orthant maps. No materialized full native Pell witness or unrestricted optimality claim.')
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();r=verify(a.root)
 need(exact(r,json.loads(json.dumps(r))),'Exact JSON type roundtrip')
 if a.expect:need(exact(r,json.loads(a.expect.read_text())),'Exact typed receipt')
 if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 print(r['status'],r['counts']);print([(f['packet']['ledger']['operations'],f['packet']['exact_degree'])for f in r['forms']])
if __name__=='__main__':main()
