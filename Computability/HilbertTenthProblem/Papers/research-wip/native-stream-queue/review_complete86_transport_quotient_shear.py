#!/usr/bin/env python3
"""Independent source, degree, coordinate, and maintained-API review."""
import argparse
import copy
import hashlib
import itertools
import json
import random
import subprocess
import sys
import tempfile
from collections import Counter
from fractions import Fraction
from pathlib import Path
from types import ModuleType

PINS={
 'complete86_transport_quotient_shear.py':'c1cb668ae5538d168652c07627c00255d9c00a7d6373feb45da8c7c3806c9c45',
 'complete86_transport_quotient_shear.json':'77ec7894c68f16e8d2dbb48f7c444bf7ab5e2c08f895bdad877f61b8c9c96efc',
 'complete86_transport_quotient_shear.md':'fd0254d6cb0a35686cd824e3f29384c9aed8141444256ce0a9442133a2785541',
 'complete86_factored_first_root.py':'29cf4100b846bcbabb05185550b7d9ead6b572746048b94998a13c83eeaff40f',
 'complete86_factored_first_root.json':'2dfe46fe9c5537ff51eb3c542806c58242238363e6018f9daab7eabf0b6fe61e',
 'complete86_factored_first_root.md':'9f2b50449e0724e523e9dd5d022f229b77504976f23ee52ca2917cf11ceb322b',
 '../../1980/FIXED_RAW_UNIVERSAL_75_PROOF.md':'e381124c969087ffa867448177a9df693d81e7bd85dd3a8489d443220fba053d',
}
CONSTANTS=['Bm1','Kconstant','twice_cell_bits','inner_bits','MC','MF']
FACTORS=['norm_first','norm_main','norm_input','norm_aux','norm_index','norm_transport','norm_strong','norm_linear']

def need(test,msg):
 if not test: raise AssertionError(msg)
def sha(data): return hashlib.sha256(data).hexdigest()
def stable(value): return json.dumps(value,sort_keys=True,separators=(',',':'))
def same(a,b): return type(a)is type(b) and (a.keys()==b.keys() and all(same(a[k],b[k])for k in a) if type(a)is dict else len(a)==len(b) and all(same(x,y)for x,y in zip(a,b)) if type(a)is list else a==b)

def add(a,b,sign=1):
 c=[(a[i]if i<len(a)else 0)+sign*(b[i]if i<len(b)else 0) for i in range(max(len(a),len(b)))]
 while len(c)>1 and not c[-1]: c.pop()
 return c
def mul(a,b):
 c=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b): c[i+j]+=x*y
 while len(c)>1 and not c[-1]: c.pop()
 return c
def power(a,n):
 p=[1]
 for _ in range(n): p=mul(p,a)
 return p
def polynomial_run(rows,values):
 e=copy.deepcopy(values)
 for name,op,a,b in rows:
  a=[a]if type(a)is int else e[a]; b=[b]if type(b)is int else e[b]
  e[name]=mul(a,b)if op=='*'else add(a,b,1 if op=='+'else-1)
 return e
def scalar_run(rows,values):
 e=dict(values)
 for name,op,a,b in rows:
  a=a if type(a)is int else e[a]; b=b if type(b)is int else e[b]
  e[name]=a*b if op=='*'else a+b if op=='+'else a-b
 return e
def C(v): return v['Bm1']*v['Jrep']+1-v['F']-v['Z']-v['alpha']-v['twice_cell_bits']*v['x']
def inverse(v):
 r=dict(v);r['zplus']=r.pop('transport_quotient')+v['w']*C(v);return r
def forward(v):
 r=dict(v);r['transport_quotient']=r.pop('zplus')-v['w']*C(v);return r

def local_ring_identity():
 # Own exact ring expansion; six truly independent cut ports.
 zero=(0,)*6
 def plus(a,b,sign=1):
  c=dict(a)
  for m,k in b.items(): c[m]=c.get(m,0)+sign*k
  return {m:k for m,k in c.items()if k}
 def times(a,b):
  c={}
  for m,x in a.items():
   for n,y in b.items():
    key=tuple(v+w for v,w in zip(m,n));c[key]=c.get(key,0)+x*y
  return {m:k for m,k in c.items()if k}
 r,w,K,c,t,U=[{tuple(int(i==j)for i in range(6)):1}for j in range(6)]
 old=plus(plus(times(plus(K,times(w,plus(r,{zero:1}))),c),U),times(plus(t,times(w,c)),r),-1)
 new=plus(plus(times(plus(K,w),c),U),times(t,r),-1)
 need(old==new and len(new)==4,'expanded local ring identity')
 return sha(stable(sorted((list(m),v)for m,v in new.items())).encode())

def recount(rows,free):
 defs={};degree={n:0 if n in CONSTANTS else 1 for n in free}; counts=Counter()
 for n,op,a,b in rows:
  need(type(n)is str and n not in degree and op in('+','-','*'),'typed acyclic gate')
  need(all(type(v)is int or type(v)is str and v in degree for v in(a,b)),'literal paid operands')
  ds=[0 if type(v)is int else degree[v]for v in(a,b)]
  degree[n]=sum(ds)if op=='*'else max(ds);defs[n]=(a,b);counts['M'if op=='*'else'A']+=1
 reached=set(); todo=['polynomial']
 while todo:
  n=todo.pop()
  if type(n)is int or n in reached: continue
  reached.add(n);todo.extend(defs.get(n,()))
 need(reached==set(defs)|set(free),'all paid gates and supplied ports live')
 return dict(operations=len(rows),M=counts['M'],A=counts['A'],syntactic_degree=degree['polynomial'],syntactic_factors=[degree[n]for n in FACTORS])

def structural(old,new,free):
 intern={}
 def atom(key):
  if key not in intern: intern[key]=len(intern)
  return intern[key]
 def visit(rows):
  e={n:atom(('free',n))for n in free+['zplus']}
  for n,op,a,b in rows:
   av=atom(('literal',a))if type(a)is int else e[a];bv=atom(('literal',b))if type(b)is int else e[b]
   e[n]=atom(('proved_transport',))if n=='norm_transport'else atom((op,av,bv))
  return e
 a=visit(old);b=visit(new);excluded={'kinner','innerC','transport_partial','local_rhs'}
 checked=[n for n,op,x,y in old if n not in excluded]
 need(all(a[n]==b[n]for n in checked),'entire retained DAG at proved transport cut')
 need(all(a[n]==b[n]for n in FACTORS+['polynomial']),'eight factors/full polynomial')
 return len(checked)

def verify(root,artifact_root):
 blobs={}
 for name,pin in PINS.items():
  path=(artifact_root/name)if name.startswith('complete86_transport_quotient_shear.')else(root/name)
  blobs[name]=path.read_bytes();need(sha(blobs[name])==pin,'pinned '+name)
 receipt=json.loads(blobs['complete86_transport_quotient_shear.json']); parents=json.loads(blobs['complete86_factored_first_root.json'])
 need(receipt['source_sha256']==PINS['complete86_transport_quotient_shear.py'],'receipt source authentication')
 need('fixed positive compiler numerals are B,DC,DR' in blobs['../../1980/FIXED_RAW_UNIVERSAL_75_PROOF.md'].decode(),'primary compiler positivity premise')
 counts=Counter();results=[];localhash=local_ring_identity();counts['independent_local_ring_identities']=1
 for oldform,newform in zip(parents['forms'],receipt['forms'],strict=True):
  p=newform['packet'];mode=oldform['normalized']; need(type(mode)is bool and p['normalized']is mode,'actual two modes')
  rows=oldform['source'];defs={n:(op,a,b)for n,op,a,b in rows}
  for name,row in {'repunit':('*','Bm1','Jrep'),'q':('+','repunit',1),'wn2':('*','w','q'),'q_minus_F':('-','q','F'),'q_minus_FZ':('-','q_minus_F','Z'),'C_after_alpha':('-','q_minus_FZ','alpha'),'scaled_t':('*','twice_cell_bits','x'),'marked_rhs':('-','C_after_alpha','scaled_t'),'kinner':('+','Kconstant','wn2'),'innerC':('*','kinner','marked_rhs'),'transport_partial':('+','innerC','q_minus_F'),'local_rhs':('*','zplus','repunit'),'norm_transport':('-','transport_partial','local_rhs')}.items(): need(defs[name]==row,'actual cut definition '+name)
  need([n for n,op,a,b in rows if 'zplus'in(a,b)]==['local_rhs'],'only old quotient consumer')
  need([n for n,op,a,b in rows if 'kinner'in(a,b)]==['innerC'],'only coefficient consumer')
  expected=copy.deepcopy(rows)
  for row in expected:
   if row[0]=='kinner':row[3]='w'
   if row[0]=='local_rhs':row[2]='transport_quotient'
  witnesses=['transport_quotient'if n=='zplus'else n for n in oldform['witnesses']];free=witnesses+['x']+CONSTANTS
  need(same(p['source'],expected)and same(p['witnesses'],witnesses)and same(p['free'],free),'complete independently reconstructed child')
  need(p['output']=='polynomial'and len(witnesses)==19,'ordinary interface')
  count=recount(expected,free);L=p['ledger']
  need((count['operations'],count['M'],count['A'])==((86,48,38)if mode else(87,47,40)),'full paid counts')
  need(all(L[k]==count[k]for k in('operations','M','A'))and L['certificate_operations']==count['operations']-1 and L['positive_witnesses']==19 and L['all_gates_live']is True,'ledger metadata')
  need(L['ordinary_input']=='x'and L['fixed_numerals']==CONSTANTS and L['degree_upper_bound']==count['syntactic_degree']and L['factor_degree_bounds']==count['syntactic_factors'],'degree/input metadata')
  counts['retained_register_identities']+=structural(rows,expected,free);counts['factor_and_full_output_identities']+=9;counts['full_live_gates']+=len(expected)
  wanted=[22,18,32,56 if mode else 24,7,2,34 if mode else 22,7]
  need(p['factor_exact_degrees']==wanted and p['exact_degree']==sum(wanted)and p['parent_exact_degree']==sum(wanted)+1,'exact degree metadata')
  need(p['parent_pins']=={n:v for n,v in PINS.items()if n.startswith('complete86_factored_first_root.')},'current parent pins')
  need(p['full_integer_coordinate_bijection']is True and p['full_positive_zero_bijection']is True and p['whole_positive_orthant_map']is False,'correct map domains')
  need(p['coordinate']=={'old':'zplus','new':'transport_quotient','forward':'transport_quotient=zplus-w*marked_rhs','inverse':'zplus=transport_quotient+w*marked_rhs'},'exact map metadata')
  degree_receipts=[]
  for case,B in enumerate((16,32,64)):
   v={n:[(i+case)%5-2,(i*3+case)%7+1]for i,n in enumerate(witnesses+['x'])}
   fixed=dict(Bm1=B-1,Kconstant=7+2*B,twice_cell_bits=2*(B.bit_length()-1),inner_bits=5,MC=B+1,MF=3*B+2)
   v.update({n:[val]for n,val in fixed.items()}); child=polynomial_run(expected,v)
   back=copy.deepcopy(v);back['zplus']=add(back.pop('transport_quotient'),mul(v['w'],child['marked_rhs']))
   parent=polynomial_run(rows,back)
   need(all(parent[n]==child[n]for n in FACTORS+['polynomial']),'complete exact integer-coefficient graph pullback')
   need([len(child[n])-1 for n in FACTORS]==wanted and len(child['polynomial'])-1==sum(wanted),'actual complete degree')
   top={n:a[-1]for n,a in v.items()if n not in CONSTANTS};Q=fixed['Bm1']*top['Jrep'];kk=top['eta']+top['zeta'];gamma=top['rho']+top['sigma'];ct=Q-top['F']-top['Z']-top['alpha']-fixed['twice_cell_bits']*top['x'];nt=top['w']*ct-top['transport_quotient']*Q
   lead=(-32*Q**107*top['h']**2*gamma*top['delta']**2*top['i']**4*kk**13*top['w']**17*top['s']**30*nt)if mode else(32*Q**79*top['h']**2*gamma*top['delta']**2*top['i']**2*top['f']**2*kk**9*top['w']**13*top['s']**22*nt)
   need(child['norm_transport'][-1]==nt and child['polynomial'][-1]==lead!=0,'complete uniform-leader specialization')
   degree_receipts.append({'B':B,'exact_degree':sum(wanted),'whole_coefficients_sha256':sha(stable(child['polynomial']).encode())});counts['full_exact_dense_coordinate_identities']+=1;counts['complete_degree_expansions']+=1
  rng=random.Random(812 if mode else 946)
  for case in range(24):
   v={n:rng.randrange(-3,5)for n in free}
   if case>=16:v={n:Fraction(x,5)for n,x in v.items()};counts['rational_numeric_identities']+=1
   a=scalar_run(rows,inverse(v));b=scalar_run(expected,v)
   need(all(a[n]==b[n]for n in FACTORS+['polynomial'])and forward(inverse(v))==v,'own signed/rational full identity')
   counts['complete_numeric_identities']+=1
  results.append({'normalized':mode,'independent_ledger':count,'exact_degree':sum(wanted),'degree_receipts':degree_receipts})
 # Exhaustive independent local unit-domain checks, both directions.
 signs=set()
 for q,K,w,F,Z,alpha,ellx,z in itertools.product(range(2,13),range(1,3),range(1,4),range(1,4),range(1,3),range(1,3),range(1,3),range(1,7)):
  c=q-F-Z-alpha-ellx;t=z-w*c;old=(K+w*q)*c+q-F-z*(q-1);new=(K+w)*c+q-F-t*(q-1)
  need(old==new,'local all-value forward identity')
  if abs(old)==1:need(c>=0 and t>0,'old positive unit direction');counts['old_local_unit_cases']+=1;signs.add(old)
  child=(K+w)*c+q-F-z*(q-1);lift=z+w*c
  need(child==(K+w*q)*c+q-F-lift*(q-1),'local inverse identity')
  if abs(child)==1:need(c>=0 and lift>0,'child positive unit direction');counts['new_local_unit_cases']+=1;signs.add(child)
  counts['local_domain_tuples']+=1
 need(signs=={-1,1},'both unit signs')
 # Execute only authenticated current maintained source, never its verify/main
 # and never any historical Python or bytecode.
 mod=ModuleType('independent_api_target');mod.__file__=str(artifact_root/'complete86_transport_quotient_shear.py');exec(compile(blobs['complete86_transport_quotient_shear.py'],mod.__file__,'exec'),mod.__dict__)
 def reject(fn,kind='typed_or_packet_rejections'):
  try: fn()
  except (ValueError,TypeError,KeyError) as exc:
   if kind=='warm_dependency_pin_rejections':need('Pinned parent 'in str(exc),'dependency guard precedes zero/domain rejection')
   counts[kind]+=1
  else:raise AssertionError('bad public call accepted')
 for mode,form,old in zip((True,False),receipt['forms'],parents['forms'],strict=True):
  p=form['packet'];need(same(mod.build(mode,root=root),p)and same(mod.rewrite(old,root=root),p)and same(mod.checked(p,root=root),p),'canonical maintained builders')
  need(same(mod.canonical_parent(mode,root=root),old)and same(mod.polynomial_source(p,root=root),p['source']),'canonical source access')
  rng=random.Random(512+mode)
  for case in range(12):
   v={n:rng.randrange(-2,5)for n in p['free']};expected=scalar_run(p['source'],v)['polynomial'];back=inverse(v)
   need(mod.evaluate(p,v,signed=True,root=root)==expected and same(mod.integer_pullback(p,v,root=root),back)and same(mod.integer_pushforward(p,back,root=root),v),'signed guarded API maps')
   counts['maintained_signed_api_roundtrips']+=1
  v={n:1 for n in p['free']};oldv=inverse(v)
  need(mod.evaluate(p,v,root=root)==scalar_run(p['source'],v)['polynomial'],'positive evaluation')
  boundary=dict(v);boundary.update(Bm1=15,Kconstant=83,twice_cell_bits=8,inner_bits=3,MC=14,MF=19,F=30)
  need(min(boundary.values())>0 and inverse(boundary)['zplus']<0 and mod.evaluate(p,boundary,root=root)!=0,'complete positive child off-zero boundary')
  oldboundary={n:1 for n in old['witnesses']+['x']+CONSTANTS};oldboundary.update(Bm1=31,Kconstant=83,twice_cell_bits=2,inner_bits=3,MC=14,MF=19,w=2)
  need(min(oldboundary.values())>0 and forward(oldboundary)['transport_quotient']<0 and scalar_run(old['source'],oldboundary)['polynomial']!=0,'complete positive parent off-zero boundary')
  counts['complete_positive_offzero_boundaries']+=2
  reject(lambda:mod.restore_child_zero(p,v,root=root));reject(lambda:mod.project_parent_zero(p,{n:1 for n in old['witnesses']+['x']+CONSTANTS},root=root))
  for key in p:
   bad=copy.deepcopy(p);del bad[key];reject(lambda bad=bad:mod.checked(bad,root=root))
  mutations=[('normalized',int(mode)),('exact_degree',float(p['exact_degree'])),('full_positive_zero_bijection',1)]
  for key,value in mutations:
   bad=copy.deepcopy(p);bad[key]=value;reject(lambda bad=bad:mod.checked(bad,root=root))
  bad=copy.deepcopy(p);bad['source'][0][1]='+';reject(lambda:mod.checked(bad,root=root))
  bad=copy.deepcopy(old);bad['source'][0][1]='+';reject(lambda:mod.rewrite(bad,root=root))
  for key in ('x','transport_quotient','Bm1'):
   for value in (True,1.0,Fraction(1),0,-1):
    bad=dict(v);bad[key]=value;reject(lambda bad=bad:mod.evaluate(p,bad,root=root))
  for key in ('x','transport_quotient','Bm1'):
   for value in (True,1.0,Fraction(1)):
    bad=dict(v);bad[key]=value;reject(lambda bad=bad:mod.integer_pullback(p,bad,root=root))
  for flag in (0,1,None,'yes'):reject(lambda flag=flag:mod.evaluate(p,v,signed=flag,root=root))
  for key,value in p.items():
   if type(value)in(dict,list):
    returned=mod.build(mode,root=root);returned[key].clear();need(same(mod.build(mode,root=root),p),'isolated returned field '+key);counts['defensive_copy_checks']+=1
  returned=mod.checked(p,root=root);returned['parent_pins'].clear();need(same(mod.checked(p,root=root),p),'nested proof pins copy');counts['defensive_copy_checks']+=1
  returned=mod.polynomial_source(p,root=root);returned[0][0]='poison';need(same(mod.polynomial_source(p,root=root),p['source']),'source copy');counts['defensive_copy_checks']+=1
  returned=mod.canonical_parent(mode,root=root);returned['source'][0][0]='poison';need(same(mod.canonical_parent(mode,root=root),old),'parent copy');counts['defensive_copy_checks']+=1
 for flag in (0,1,None,'yes'):reject(lambda flag=flag:mod.build(flag,root=root))
 p=receipt['forms'][0]['packet'];old=parents['forms'][0];v={n:1 for n in p['free']};ov={n:1 for n in old['witnesses']+['x']+CONSTANTS}
 with tempfile.TemporaryDirectory(prefix='independent_shear_pins_')as tmp:
  temp=Path(tmp)
  for name in mod.PINS:(temp/name).write_bytes(blobs[name])
  mod.build(root=temp)
  funcs=[lambda:mod.build(root=temp),lambda:mod.canonical_parent(root=temp),lambda:mod.rewrite(old,root=temp),lambda:mod.checked(p,root=temp),lambda:mod.polynomial_source(p,root=temp),lambda:mod.evaluate(p,v,root=temp),lambda:mod.integer_pullback(p,v,root=temp),lambda:mod.integer_pushforward(p,ov,root=temp),lambda:mod.restore_child_zero(p,v,root=temp),lambda:mod.project_parent_zero(p,ov,root=temp)]
  for name in mod.PINS:
   (temp/name).write_bytes(blobs[name]+b' ')
   for fn in funcs:reject(fn,'warm_dependency_pin_rejections')
   (temp/name).write_bytes(blobs[name])
 proc=subprocess.run([sys.executable,'-O',str(artifact_root/'complete86_transport_quotient_shear.py')],capture_output=True,text=True,timeout=20)
 need(proc.returncode!=0 and 'Run without -O'in proc.stderr,'optimized Python rejected');counts['optimized_mode_rejections']=1
 return {'status':'PASS independent full source and maintained API review','source_sha256':sha(Path(__file__).read_bytes()),'pins':PINS,'local_identity_sha256':localhash,'counts':dict(counts),'forms':results,'scope':'Full literal two-source reconstruction; exact ring cut plus downstream whole-DAG proof; inherited seven uniform factor bounds plus new quadratic nonzero leader; no historical Python/author verify, no materialized full positive universal/Pell zero. Only current maintained source executes for API checks.'}

if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--artifact-root',type=Path,default=Path('/tmp'));ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args()
 r=verify(a.root,a.artifact_root);out=json.dumps(r,sort_keys=True,indent=2)+'\n'
 if a.expect:need(a.expect.read_text()==out,'fresh exact receipt')
 if a.output:a.output.write_text(out)
 print(r['status'],r['counts'])
