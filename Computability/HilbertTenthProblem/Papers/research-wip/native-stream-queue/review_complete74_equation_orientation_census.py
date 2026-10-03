#!/usr/bin/env python3
"""Independent source/zero-equivalence/uniform-degree review of 56 orientations.
No author or historical Python module is executed. Exact coefficient arithmetic
keeps all six fixed numeral ports symbolic; source graphs read from JSON.
"""
import argparse,copy,hashlib,itertools,json
from functools import reduce
from pathlib import Path
from collections import Counter
if not __debug__:raise RuntimeError('run without -O')
parents={}
def need(v,m):
 if not v:raise ValueError(m)
def sha(b):return hashlib.sha256(b).hexdigest()
def stable(v):return json.dumps(v,sort_keys=True,separators=(',',':'))
def digest(v):return sha(stable(v).encode())
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys()and all(exact(a[k],b[k])for k in a)
 if type(a)is list:return len(a)==len(b)and all(exact(x,y)for x,y in zip(a,b))
 return a==b
def emit(mode,asym=False,E=False,K=False,I=False,U=False,T=False):
 p=parents[mode];rows=[list(r)for r in p['source']];cmp=[list(r)for r in p['comparisons']];d={r[0]:r for r in rows}
 if asym:d['wn2'][3]='q'
 if E:
  assert mode=='raw30';d['UM'][1:]=['-','a','sn2'];d['R12'][1:]=['*','wn2','sn2'];cmp[cmp.index(['a','R12'])]=['UM','R12']
 if K:
  assert mode=='raw30';d['ksn2'][1:]=['-','c','eta'];d['R10a'][1:]=['*','k','sn2'];cmp[cmp.index(['c','R10a'])]=['ksn2','R10a']
 if I:
  assert mode=='positive22';d['pell_gap'][1:]=['-','R10a','phi'];cmp[cmp.index(['R10a','pell_gap'])]=['pell_gap','index_rhs'];d['difference_multiple'][2]='pell_gap';d['kappa2'][2:]=['pell_gap','pell_gap']
 if U:d['H2'][2:]=['aux_u_rhs','aux_u_rhs']
 if T:d['L17'][2]='R16'
 todo=list(rows);done=set(p['witnesses']+p['fixed_numerals']+['x']);out=[]
 while todo:
  found=False
  for j,r in enumerate(todo):
   if all(type(v)is int or v in done for v in r[2:]):out.append(r);done.add(r[0]);todo.pop(j);found=True;break
  assert found
 return out,cmp

DIMS=7

Z=(0,)*DIMS

def C(v):return {Z:v}if v else{}

def V(i):return {tuple(int(i==j)for j in range(DIMS)):1}

def add(a,b,s=1):
 r=dict(a)
 for m,c in b.items():r[m]=r.get(m,0)+s*c
 return {m:c for m,c in r.items()if c}

def mul(a,b):
 r={}
 for m,c in a.items():
  for n,d in b.items():
   k=tuple(x+y for x,y in zip(m,n));r[k]=r.get(k,0)+c*d
 return {m:c for m,c in r.items()if c}

def execute(mode,rows,cmp):
 p=parents[mode];env={n:{(1,0,0,0,0,0,0):i+2}for i,n in enumerate(p['witnesses']+['x'])};env.update({n:V(i+1)for i,n in enumerate(p['fixed_numerals'])})
 for n,o,a,b in rows:
  aa=env[a]if type(a)is str else C(a);bb=env[b]if type(b)is str else C(b);env[n]=mul(aa,bb)if o=='*'else add(aa,bb,1 if o=='+'else-1)
 res=[add(env[a]if type(a)is str else C(a),env[b]if type(b)is str else C(b),-1)for a,b in cmp]
 deg=[max([m[0]for m in r],default=0)for r in res]
 tops=[{m:c for m,c in r.items()if m[0]==g}for r,g in zip(res,deg)]
 return deg,tops

def upper(mode,rows,cmp,I):
 p=parents[mode];d={n:1 for n in p['witnesses']+['x']};d.update({n:0 for n in p['fixed_numerals']})
 for n,o,a,b in rows:
  aa=d[a]if type(a)is str else 0;bb=d[b]if type(b)is str else 0;d[n]=aa+bb if o=='*'else max(aa,bb)
 out=[]
 for left,right in cmp:
  g=max(d.get(left,0),d.get(right,0))
  if mode!='raw30'and[left,right]==['L15','R15']:
   X,a,c,G,H=[d[n]for n in ('wn2','R12','R10a','gam','a4m5')];g=max(2*X,X+a+c,X+G,a+c+G,2*G,H+2*c,0)
  if mode!='raw30'and[left,right]==['mu2','norm_rhs']:
   a,k,r,H,W=[d[n]for n in ('R12','pell_gap'if I else'index_rhs','rho','a4m5','W')];g=max(2*W,a+k+W,r+W+H,a+r+k+H,2*r+2*H,H+2*k,0)
  out.append(g)
 return out

def all_cases():
 for mode in parents:
  for asym in (False,True):
   names=['E','K','U','T']if mode=='raw30'else['I','U','T']if mode=='positive22'else['U','T']
   for vv in itertools.product((False,True),repeat=len(names)):
    flags=dict(zip(names,vv));rows,cmp=emit(mode,asym,**flags);d,tops=execute(mode,rows,cmp);up=upper(mode,rows,cmp,flags.get('I',False));assert d==up,(mode,asym,flags,d,up)
    peak=max(d);winning=[(i,t)for i,t in enumerate(tops)if d[i]==peak]
    # Every fixed port remains symbolic: these coefficients are uniform
    # nonvanishing monomials of Bm1, not finite-constant experiments.
    usable=[(i,t)for i,t in winning if len(t)==1 and all(all(v==0 for v in m[2:])for m in t)]
    assert usable
    yield dict(mode=mode,asym=asym,flags=flags,residual_degrees=d,degree=2*peak,leader_residuals=[i for i,t in winning],uniform_leader_witness=[usable[0][0],[[list(m),c]for m,c in usable[0][1].items()]])

BASE='complete74_factored_first_norm'
AUTHOR='complete74_equation_orientation_census'
DEPENDENCIES={
'complete74_factored_first_norm.py':'7c4b10fa78a3fa6517083c41fc6228dd403fec5ac87f2ca6b80b45dd60e8b908',
'complete74_factored_first_norm.json':'7ebfa54d3846d1c3a6ff7b8e5cd143f3ac80f8299b51698a9f45681d3524eb28',
'complete74_factored_first_norm.md':'119b51ca9a5d50e0eb998b334af87c1ea3eb0913f956b4f9d7a985f5d1159d9f',
'complete74_asymmetric_scale_transfer.py':'c0f3852a1d4c50dba3d7aeb6c877290ebcf18b233dbf944d1870780ab942b8d6',
'complete74_asymmetric_scale_transfer.json':'14816c4da8738e3c27cc1ec0217c450075c0e47b20d77ec4c4d8159aac24dc88',
'complete74_asymmetric_scale_transfer.md':'0484dc71131d7d132e12c7961de731ca4c5bb91adc98447f72fed77882461fe3',
'review_complete74_asymmetric_scale_math.py':'fbefd6b86533634894eb66daf16788a523c15bcfc2cb0fa813b4f91fe140702f',
'review_complete74_asymmetric_scale_math.json':'759a29961791ce779819250b3e54cfc3ae412ec26d7db63c0865705caa297ca3',
'review_complete74_asymmetric_scale_math.md':'a7f8d64389597c5a8fff93bad1f023dfc440d736bb9d77f2acd549e758aa0b58',
'complete75_auxiliary_degree_tradeoffs.md':'6c56201bff3cfc95eb5677bf24f0ea2c27033995d8753aadeebf99447db36dcc'}
AUTHOR_PINS={'complete74_equation_orientation_census.py':'e4265e24f826fef6f4bfeebd2d5af2742b16f853b91f6f1a044ae3851099218e','complete74_equation_orientation_census.json':'627568df8674e3fbe32bac6881a9ef89587a902ed25476b2a541f1eff0875559','complete74_equation_orientation_census.md':'292f4b2ef80c9eca684e50e561efd21469a9ad9d0c9970aab537f30f93d0776d'}

def serialize_polynomial(p):return [[list(m),c]for m,c in sorted(p.items())]
def closed_ledger(rows,free,roots):
 known=set(free);defs={};counts=Counter()
 for row in rows:
  need(type(row)is list and len(row)==4,'literal row')
  n,op,a,b=row;need(type(n)is str and n not in known and op in('+','-','*'),'fresh operation')
  need(all(type(x)is int or(type(x)is str and x in known)for x in(a,b)),'topological paid source')
  known.add(n);defs[n]=(a,b);counts['M'if op=='*'else'A']+=1
 reached=set();used=set();stack=list(roots)
 while stack:
  n=stack.pop()
  if type(n)is int:continue
  if n not in defs:need(n in free,'known root');used.add(n)
  elif n not in reached:reached.add(n);stack.extend(defs[n])
 need(reached==set(defs)and used==set(free),'all gates and all advertised coordinates live')
 return dict(operations=len(rows),M=counts['M'],A=counts['A'],all_gates_live=True)

def full_source(rows,cmp):
 result=copy.deepcopy(rows)
 for i,(a,b)in enumerate(cmp):result.extend([[f'residual_{i}','-',a,b],[f'square_{i}','*',f'residual_{i}',f'residual_{i}']])
 output='square_0'
 for i in range(1,len(cmp)):
  name=f'sum_{i}';result.append([name,'+',output,f'square_{i}']);output=name
 return result,output

def expansion_lemmas():
 # Complete coefficient proofs in independent variables, not scalar samples.
 x,a,c,g,h,w,k=[V(i)for i in range(7)];one=C(1);sq=lambda p:mul(p,p)
 scale=lambda p,n:mul(p,C(n))
 summ=lambda terms:reduce(add,terms,{})
 main=add(add(sq(summ([x,mul(a,c),g])),mul(add(sq(a),h),sq(c)),-1),one,-1)
 main_expected=summ([sq(x),scale(mul(mul(x,a),c),2),scale(mul(x,g),2),scale(mul(mul(a,c),g),2),sq(g),scale(mul(h,sq(c)),-1),C(-1)])
 need(main==main_expected,'exact main norm expansion')
 # Rename x to rho for the separate independent input identity.
 inp=add(add(sq(summ([w,mul(a,k),mul(x,h)])),mul(add(sq(a),h),sq(k)),-1),one,-1)
 inp_expected=summ([sq(w),scale(mul(mul(w,a),k),2),scale(mul(mul(w,x),h),2),scale(mul(mul(mul(a,k),x),h),2),mul(sq(x),sq(h)),scale(mul(h,sq(k)),-1),C(-1)])
 need(inp==inp_expected,'exact input norm expansion')
 need(add(a,add(x,c),-1)==add(add(a,c,-1),x,-1),'monic residual orientation')
 return dict(main=serialize_polynomial(main),input=serialize_polynomial(inp),monic_orientation=True)

class AffineDAG:
 """Exact affine arithmetic with canonical opaque product nodes.
 Equal normal forms imply polynomial identity; incompleteness cannot certify
 a false identity. Constants and scalar signs are normalized independently.
 """
 def __init__(self):self.keys={};self.next=1
 def atom(self,key):
  if key not in self.keys:self.keys[key]=self.next;self.next+=1
  return ((self.keys[key],1),)
 def constant(self,n):return ((0,n),)if n else()
 def plus(self,a,b,sign=1):
  d=dict(a)
  for k,v in b:d[k]=d.get(k,0)+sign*v
  return tuple((k,v)for k,v in sorted(d.items())if v)
 def times(self,a,b):
  if not a or not b:return()
  if a[0][0]==0 and len(a)==1:return tuple((k,v*a[0][1])for k,v in b)
  if b[0][0]==0 and len(b)==1:return tuple((k,v*b[0][1])for k,v in a)
  sign=1
  if a[0][1]<0:a=tuple((k,-v)for k,v in a);sign=-sign
  if b[0][1]<0:b=tuple((k,-v)for k,v in b);sign=-sign
  key=('product',)+tuple(sorted((a,b)));atom=self.atom(key)
  return tuple((k,sign*v)for k,v in atom)
 def eval(self,rows,free,replace=None):
  e={x:self.atom(('free',x))for x in free};replace=replace or{};e.update(replace)
  val=lambda x:self.constant(x)if type(x)is int else e[x]
  for n,op,a,b in rows:
   if n not in replace:e[n]=self.times(val(a),val(b))if op=='*'else self.plus(val(a),val(b),1 if op=='+'else-1)
  return e

def conditional_proof(mode,asym,flags,packet):
 rows,cmp=emit(mode,asym);oldpoly,out=full_source(rows,cmp);free=parents[mode]['witnesses']+parents[mode]['fixed_numerals']+['x']
 engine=AffineDAG();old=engine.eval(oldpoly,free);new=engine.eval(packet['polynomial_source'],free)
 protected=[]
 if flags.get('E'):protected.append(cmp.index(['a','R12']))
 if flags.get('K'):protected.append(cmp.index(['c','R10a']))
 if flags.get('I'):protected.append(cmp.index(['R10a','pell_gap']))
 if flags.get('U'):protected.append(cmp.index(['H17','aux_u_rhs']))
 if flags.get('T'):protected.append(cmp.index(['ic22','R16']))
 for i in protected:need(old[f'residual_{i}']==new[f'residual_{i}'],'protected residual unchanged before substitutions')
 replace={}
 if flags.get('E'):replace['a']=old['R12']
 if flags.get('K'):replace['c']=old['R10a']
 if flags.get('I'):replace['phi']=engine.plus(old['R10a'],old['index_rhs'],-1)
 defs={n:(a,b)for n,op,a,b in rows}
 def ancestors(root):
  found=set();todo=[root]
  while todo:
   n=todo.pop()
   if type(n)is str and n not in found:found.add(n);todo.extend(defs.get(n,()))
  return found
 # The defining replacements must not refer back to the replaced free ports.
 for n,target in [('a','R12'),('c','R10a')]:
  if n in replace:need(n not in ancestors(target),'monic free-coordinate replacement is acyclic')
 if 'phi'in replace:need('phi'not in ancestors('R10a')|ancestors('index_rhs'),'gap replacement is acyclic')
 oldcut=engine.eval(rows,free,replace)
 need(not {'H17','ic22'}&(ancestors('aux_u_rhs')|ancestors('R16')),'auxiliary RHS independent of both cut ports')
 if flags.get('U'):replace['H17']=oldcut['aux_u_rhs']
 if flags.get('T'):replace['ic22']=oldcut['R16']
 left=engine.eval(oldpoly,free,replace);right=engine.eval(packet['polynomial_source'],free,replace)
 for i in range(len(cmp)):need(left[f'residual_{i}']==right[f'residual_{i}'],'complete conditional residual identity')
 need(left[out]==right[packet['output']],'complete conditional SOS identity')
 need(packet['protected_comparison_indices']==sorted(protected),'exact protected comparisons')
 return dict(protected_before_cuts=len(protected),conditional_residuals=len(cmp),whole_conditional_identity=True)

def proof_shapes(mode,rows,I):
 d={n:(op,a,b)for n,op,a,b in rows}
 if mode=='raw30':return
 need(d['A']==('+','a_square','a4m5')and d['a_square']==('*','R12','R12'),'literal discriminant split')
 need(d['a4']==('*',4,'R12')and d['a4m5']==('+','a4',3),'positive fixed linear discriminant gap')
 need(d['D1']==('+','wn2','cam2')and d['cam2']==('*','R10a','R12')and d['R14']==('+','D1','gam'),'main norm center')
 need(d['L15']==('*','R14','R14')and d['R15']==('+','Ac2',1)and d['Ac2']==('*','A','c2')and d['c2']==('*','R10a','R10a'),'main norm complete cone')
 port='pell_gap'if I else'index_rhs'
 req={'difference_multiple':('*',port,'R12'),'kappa2':('*',port,port),'exponent_partial':('+','W','difference_multiple'),'modulus_multiple':('*','rho','a4m5'),'exponent_rhs':('+','exponent_partial','modulus_multiple'),'norm_rhs':('+','scaled_kappa2',1),'mu2':('*','exponent_rhs','exponent_rhs'),'scaled_kappa2':('*','A','kappa2')}
 need(all(d[n]==v for n,v in req.items()),'input norm complete cone')

def review(root,author_root):
 global parents
 for name,pin in DEPENDENCIES.items():need(sha((root/name).read_bytes())==pin,'dependency pin '+name)
 for name,pin in AUTHOR_PINS.items():need(sha((author_root/name).read_bytes())==pin,'author pin '+name)
 receipt=json.loads((author_root/(AUTHOR+'.json')).read_text())
 need(receipt['pins']==DEPENDENCIES,'literal author dependency manifest')
 need(receipt['source_sha256']==sha((author_root/(AUTHOR+'.py')).read_bytes()),'author source receipt link')
 parents={f['packet']['mode']:f['packet']for f in json.loads((root/(BASE+'.json')).read_text())['forms']}
 asym_parents={f['packet']['mode']:f['packet']for f in json.loads((root/'complete74_asymmetric_scale_transfer.json').read_text())['forms']}
 need(list(parents)==['raw30','positive22','signed20'],'three actual parent interfaces')
 need(len(receipt['forms'])==56,'complete finite inventory')
 rows_out=[];totals=Counter();minima={};hist={};local=expansion_lemmas()
 for expected,saved in zip(all_cases(),receipt['forms']):
  mode=expected['mode'];asym=expected['asym'];flags=expected['flags'];p=saved['packet'];parent=parents[mode]
  rows,cmp=emit(mode,asym,**flags)
  need({r[0]:r[1:]for r in rows}=={r[0]:r[1:]for r in p['source']},'all exact expected producer rows')
  need(p['comparisons']==cmp and p['mode']==mode,'same ordered comparison interface')
  for key in ('witnesses','fixed_numerals','ordinary_input'):need(p[key]==parent[key],'unchanged supplied interface')
  need(parent['fixed_numerals']==['Bm1','Kconstant','twice_cell_bits','inner_bits','MC','MF'],'six symbolic fixed ports')
  of=dict(asymmetric=asym,E_from_a=flags.get('E',False),kY_from_c=flags.get('K',False),kappa_from_gap=flags.get('I',False),aux_root_rhs=flags.get('U',False),aux_coefficient_rhs=flags.get('T',False))
  need(p['orientation']==of,'exact Boolean orientation scope')
  full,out=full_source(p['source'],cmp);need(full==p['polynomial_source']and out==p['output'],'entire literal SOS finalizer')
  free=parent['witnesses']+parent['fixed_numerals']+['x']
  cert=closed_ledger(p['source'],free,[a for pair in cmp for a in pair]);paid=closed_ledger(full,free,[out])
  need(cert==p['certificate_ledger']and paid==p['polynomial_ledger'],'actual complete ledgers')
  need(cert==dict(operations=74,M=40,A=34,all_gates_live=True),'unchanged complete certificate cost')
  need(paid['operations']=={'raw30':130,'positive22':106,'signed20':100}[mode],'complete mode finalizer cost')
  need(digest(full)==saved['source_sha256'],'saved entire source hash')
  if asym:
   rr,cc=emit(mode,True);ap=asym_parents[mode]
   need(rr==ap['source']and cc==ap['comparisons'],'same-scale authenticated asymmetric boundary')
  proof_shapes(mode,p['source'],flags.get('I',False))
  degrees,tops=execute(mode,p['source'],cmp);bounds=upper(mode,p['source'],cmp,flags.get('I',False))
  need(degrees==bounds==expected['residual_degrees'],'exact symbolic residual specialization attains every upper bound')
  need(p['degree']['residual_degree_upper_bounds']==bounds and p['degree']['exact_degree']==expected['degree'],'all saved degree metadata')
  gated={n:1 for n in parent['witnesses']+['x']};gated.update({n:0 for n in parent['fixed_numerals']})
  for n,op,a,b in p['source']:
   aa=gated[a]if type(a)is str else 0;bb=gated[b]if type(b)is str else 0;gated[n]=aa+bb if op=='*'else max(aa,bb)
  need(gated==p['degree']['gate_degree_bounds'],'honest gate-by-gate upper bounds')

  need(p['degree']['dominant_residual_indices']==expected['leader_residuals'],'all ties correctly retained')
  i,terms=expected['uniform_leader_witness'];need(len(terms)==1,'single-monomial uniform witness')
  mon,coefficient=terms[0];need(coefficient!=0 and mon[0]==max(bounds)and all(e==0 for e in mon[2:]),'uniformly nonzero Bm1-only coefficient')
  need(tops[i]=={tuple(mon):coefficient},'exact chosen uniform leading polynomial')
  cp=conditional_proof(mode,asym,flags,p)
  name=mode+('/asymmetric'if asym else'/symmetric');minima[name]=min(minima.get(name,10**9),expected['degree'])
  hist.setdefault(name,Counter())[str(expected['degree'])]+=1
  totals.update(whole_sources=1,certificate_gates=len(p['source']),live_paid_gates=len(full),residual_expansions=len(cmp),full_conditional_identities=1,protected_residuals_before_cuts=cp['protected_before_cuts'],uniform_exact_degrees=1)
  rows_out.append(dict(**expected,source_sha256=digest(full),certificate_ledger=cert,polynomial_ledger=paid,conditional_proof=cp,all_residual_leaders_sha256=digest([serialize_polynomial(t)for t in tops])))
 need(receipt['minima']==minima,'six finite-family minima')
 need(totals['whole_sources']==56 and totals['residual_expansions']==856 and totals['live_paid_gates']==6656,'complete independent totals')
 return dict(status='PASS',review_source_sha256=sha(Path(__file__).read_bytes()),author_pins=AUTHOR_PINS,dependency_pins=DEPENDENCIES,counts=dict(totals),minima=minima,degree_histograms={k:dict(sorted(v.items(),key=lambda kv:int(kv[0])))for k,v in hist.items()},local_expansion_proofs=local,forms=rows_out,scope='Independent complete source reconstruction, exact retained-equation cut proof, and uniform exact degrees on valid fixed compiler slices. No author code executed, no API or unrestricted optimization claim. The full SOS generally changes off the protected equality locus.')

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--author-root',type=Path);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();result=review(a.root,a.author_root or a.root)
 need(exact(result,json.loads(json.dumps(result))),'exact typed JSON roundtrip')
 if a.expect:need(exact(result,json.loads(a.expect.read_text())),'exact saved review receipt')
 if a.output:a.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
 print(json.dumps({k:result[k]for k in('status','counts','minima')}))
if __name__=='__main__':main()
