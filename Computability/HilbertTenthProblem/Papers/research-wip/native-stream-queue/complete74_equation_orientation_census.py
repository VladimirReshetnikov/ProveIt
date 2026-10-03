#!/usr/bin/env python3
"""Finite same-zero equation orientations of the actual complete74 sources.
Standalone JSON reconstruction; no author or historical compiler imports.
"""
import argparse,copy,hashlib,itertools,json
from collections import Counter
from pathlib import Path
if not __debug__:raise RuntimeError('Run without -O')
PINS={'complete74_factored_first_norm.py': '7c4b10fa78a3fa6517083c41fc6228dd403fec5ac87f2ca6b80b45dd60e8b908', 'complete74_factored_first_norm.json': '7ebfa54d3846d1c3a6ff7b8e5cd143f3ac80f8299b51698a9f45681d3524eb28', 'complete74_factored_first_norm.md': '119b51ca9a5d50e0eb998b334af87c1ea3eb0913f956b4f9d7a985f5d1159d9f', 'complete74_asymmetric_scale_transfer.py': 'c0f3852a1d4c50dba3d7aeb6c877290ebcf18b233dbf944d1870780ab942b8d6', 'complete74_asymmetric_scale_transfer.json': '14816c4da8738e3c27cc1ec0217c450075c0e47b20d77ec4c4d8159aac24dc88', 'complete74_asymmetric_scale_transfer.md': '0484dc71131d7d132e12c7961de731ca4c5bb91adc98447f72fed77882461fe3', 'review_complete74_asymmetric_scale_math.py': 'fbefd6b86533634894eb66daf16788a523c15bcfc2cb0fa813b4f91fe140702f', 'review_complete74_asymmetric_scale_math.json': '759a29961791ce779819250b3e54cfc3ae412ec26d7db63c0865705caa297ca3', 'review_complete74_asymmetric_scale_math.md': 'a7f8d64389597c5a8fff93bad1f023dfc440d736bb9d77f2acd549e758aa0b58', 'complete75_auxiliary_degree_tradeoffs.md': '6c56201bff3cfc95eb5677bf24f0ea2c27033995d8753aadeebf99447db36dcc'}
PARENT='complete74_factored_first_norm.json'

def need(c,m):
 if not c:raise ValueError(m)
def sha(x):return hashlib.sha256(x).hexdigest()
def stable(x):return json.dumps(x,sort_keys=True,separators=(',',':'))
def auth(root):
 for n,h in PINS.items():need(sha((root/n).read_bytes())==h,'source pin '+n)
def finalize(rows,pairs):
 out=copy.deepcopy(rows)
 for i,(a,b)in enumerate(pairs):out.extend([[f'residual_{i}','-',a,b],[f'square_{i}','*',f'residual_{i}',f'residual_{i}']])
 name='square_0'
 for i in range(1,len(pairs)):
  z=f'sum_{i}';out.append([z,'+',name,f'square_{i}']);name=z
 return out,name

def topological(rows,free):
 todo=copy.deepcopy(rows);out=[];known=set(free)
 while todo:
  progress=False
  for row in todo[:]:
   n,o,a,b=row
   if all(type(v)is int or v in known for v in(a,b)):
    need(n not in known,'fresh gate');known.add(n);out.append(row);todo.remove(row);progress=True
  need(progress,'acyclic reordered graph')
 return out

def ledger(rows,free,roots,fixed):
 known=set(free);defs={};M=0
 for n,o,a,b in rows:
  need(type(n)is str and n not in known and o in ('+','-','*'),'fresh typed row')
  need(all(type(v)is int or type(v)is str and v in known for v in(a,b)),'closed paid source')
  known.add(n);defs[n]=(a,b);M+=o=='*'
 seen=set();leaves=set();stack=list(roots)
 while stack:
  n=stack.pop()
  if type(n)is int:continue
  if n not in defs:leaves.add(n);continue
  if n not in seen:seen.add(n);stack.extend(defs[n])
 need(seen==set(defs)and leaves==set(free),'all paid gates/coordinates live')
 return dict(operations=len(rows),M=M,A=len(rows)-M,all_gates_live=True)

def guard(p):
 d={n:(o,a,b)for n,o,a,b in p['source']};raw=p['mode']=='raw30';k='k'if raw else'R10b';c='c'if raw else'R10a'
 req={'UM':('*','wn2','sn2'),'ksn2':('*',k,'sn2'),'R12':('+','UM','sn2'),'R10a':('+','ksn2','eta'),'H2':('*','H17','H17'),'L17':('*','ic22','aux_square_gap'),'aux_square_gap':('-','H2','aux_y2'),'P17':('-',1,'aux_y2'),'H17':('-','jc','r'),'aux_u_rhs':('-','of',c),'of':('*','o','f'),'ic22':('*','ic2','ic2'),'R16':('*','A','f_square_minus_one')}
 need(all(d[n]==v for n,v in req.items()),'literal protected definitions')
 need(['ic22','R16']in p['comparisons']and['H17','aux_u_rhs']in p['comparisons'],'both auxiliary equations retained')
 uses=lambda x:[n for n,o,a,b in p['source']if x in(a,b)]
 if raw:
  need(uses('R12')==[]and uses('R10a')==[]and['a','R12']in p['comparisons']and['c','R10a']in p['comparisons'],'private raw definition endpoints')
 if p['mode']=='positive22':
  need(d['pell_gap']==('+','index_rhs','phi')and ['R10a','pell_gap']in p['comparisons'],'retained input gap')
  need(uses('index_rhs')==['pell_gap','difference_multiple','kappa2']and uses('phi')==['pell_gap'],'all kappa/phi consumers')
 poly,out=finalize(p['source'],p['comparisons']);need(poly==p['polynomial_source']and out==p['output'],'full original finalizer')

def build(p,asymmetric,E,C,K,root,coefficient):
 guard(p);q=copy.deepcopy(p);rows=copy.deepcopy(p['source']);pairs=copy.deepcopy(p['comparisons']);d={r[0]:r for r in rows}
 if asymmetric:need(d['wn2']==['wn2','*','w','n2'],'old symmetric X');d['wn2'][3]='q'
 protected=[]
 if E:
  need(p['mode']=='raw30','supplied a required');d['UM'][:]=['UM','-','a','sn2'];d['R12'][:]=['R12','*','wn2','sn2'];i=pairs.index(['a','R12']);pairs[i]=['UM','R12'];protected.append(i)
 if C:
  need(p['mode']=='raw30','supplied c required');d['ksn2'][:]=['ksn2','-','c','eta'];d['R10a'][:]=['R10a','*','k','sn2'];i=pairs.index(['c','R10a']);pairs[i]=['ksn2','R10a'];protected.append(i)
 if K:
  need(p['mode']=='positive22','retained positive phi required');d['pell_gap'][:]=['pell_gap','-','R10a','phi'];i=pairs.index(['R10a','pell_gap']);pairs[i]=['pell_gap','index_rhs'];protected.append(i)
  need(d['difference_multiple']==['difference_multiple','*','index_rhs','R12']and d['kappa2']==['kappa2','*','index_rhs','index_rhs'],'exact remaining kappa consumers')
  d['difference_multiple'][2]='pell_gap';d['kappa2'][2:]=['pell_gap','pell_gap']
 if root:d['H2'][2:]=['aux_u_rhs','aux_u_rhs'];protected.append(pairs.index(['H17','aux_u_rhs']))
 if coefficient:d['L17'][2]='R16';protected.append(pairs.index(['ic22','R16']))
 rows=topological(rows,p['fixed_numerals']+p['witnesses']+[p['ordinary_input']]);poly,out=finalize(rows,pairs)
 q.update(source=rows,comparisons=pairs,polynomial_source=poly,output=out,orientation=dict(asymmetric=asymmetric,E_from_a=E,kY_from_c=C,kappa_from_gap=K,aux_root_rhs=root,aux_coefficient_rhs=coefficient),protected_comparison_indices=sorted(set(protected)))
 return q

class Ring:
 def __init__(self):self.ids={('one',):0}
 def atom(self,key):
  if key not in self.ids:self.ids[key]=len(self.ids)
  return self.ids[key]
 def val(self,x):return ((0,x),)if type(x)is int and x else()if type(x)is int else((self.atom(('var',x)),1),)
 def add(self,a,b,s=1):
  e=dict(a)
  for k,v in b:e[k]=e.get(k,0)+s*v
  return tuple(sorted((k,v)for k,v in e.items()if v))
 def scale(self,a,s):return tuple((k,v*s)for k,v in a)if s else()
 def mul(self,a,b):
  if not a or not b:return()
  if len(a)==1 and a[0][0]==0:return self.scale(b,a[0][1])
  if len(b)==1 and b[0][0]==0:return self.scale(a,b[0][1])
  sa=-1 if a[0][1]<0 else 1;sb=-1 if b[0][1]<0 else 1;a=self.scale(a,sa);b=self.scale(b,sb)
  if a>b:a,b=b,a
  return((self.atom(('product',a,b)),sa*sb),)
 def run(self,rows,free,overrides=None):
  e={n:self.val(n)for n in free};e.update(overrides or{})
  for n,o,a,b in rows:
   if overrides and n in overrides:continue
   a=e[a]if type(a)is str else self.val(a);b=e[b]if type(b)is str else self.val(b)
   e[n]=self.mul(a,b)if o=='*'else self.add(a,b,1 if o=='+'else-1)
  return e

def conditional_identity(parent,q):
 flags=q['orientation'];free=q['fixed_numerals']+q['witnesses']+[q['ordinary_input']];R=Ring();old=R.run(parent['source'],free);sub={}
 original=R.run(parent['polynomial_source'],free);changed=R.run(q['polynomial_source'],free)
 for i in q['protected_comparison_indices']:
  need(original[f'residual_{i}']==changed[f'residual_{i}'],'protected residual identical before any substitution')
 defs={n:(a,b)for n,o,a,b in parent['source']}
 def ancestors(n):
  seen=set();stack=[n]
  while stack:
   v=stack.pop()
   if type(v)is str and v not in seen:seen.add(v);stack.extend(defs.get(v,()))
  return seen
 need(not {'H17','ic22'} & (ancestors('aux_u_rhs')|ancestors('R16')),'auxiliary cut right sides independent of both cuts')
 # Monic defining residuals give exact replacement of these free coordinates.
 if flags['E_from_a']:sub['a']=old['R12']
 if flags['kY_from_c']:sub['c']=old['R10a']
 if flags['kappa_from_gap']:sub['phi']=R.add(old['R10a'],old['index_rhs'],-1)
 old=R.run(parent['source'],free,sub)
 # Each cut is precisely a retained comparison; its RHS is cut-independent.
 if flags['aux_root_rhs']:sub['H17']=old['aux_u_rhs']
 if flags['aux_coefficient_rhs']:sub['ic22']=old['R16']
 a=R.run(parent['polynomial_source'],free,sub);b=R.run(q['polynomial_source'],free,sub)
 for i in range(len(q['comparisons'])):need(a[f'residual_{i}']==b[f'residual_{i}'],'every residual identical on retained equality locus')
 need(a[parent['output']]==b[q['output']],'whole SOS on equality locus')
 # A local independent coefficient calculation for the changed defining row.
 # a-(XY+Y)=(a-Y)-XY; c-(kY+eta)=(c-eta)-kY;
 # c-(kappa+phi)=(c-phi)-kappa, with independent formal atoms.
 aa,bb,cc=[R.val(n)for n in('local_a','local_b','local_c')]
 need(R.add(aa,R.add(bb,cc),-1)==R.add(R.add(aa,cc,-1),bb,-1),'all-value monic residual reorientation')
 return dict(protected_residuals_identical_before_substitution=True,full_conditional_polynomial_identity=True,retained_residual_identities=len(q['comparisons']),protected_comparisons=q['protected_comparison_indices'],same_tuple_zero_equivalence=True,unconditional_polynomial_identity_claimed=not any(v for k,v in flags.items()if k!='asymmetric'))

def degree_proof(q):
 rows=q['source'];d={n:0 for n in q['fixed_numerals']};d.update({n:1 for n in q['witnesses']+[q['ordinary_input']]});defs={n:(o,a,b)for n,o,a,b in rows}
 for n,o,a,b in rows:
  da=d[a]if type(a)is str else 0;db=d[b]if type(b)is str else 0;d[n]=da+db if o=='*'else max(da,db)
 at=lambda x:d[x]if type(x)is str else 0
 bounds=[max(at(a),at(b))for a,b in q['comparisons']];first=q['comparisons'].index(['L9','R9']);need(bounds[first]==2*d['first_root_base']and defs['first_root_base']==('*','UM','ksn2')and defs['first_next']==('+','first_root_base','k'if q['mode']=='raw30'else'R10b')and defs['L9']==('*','first_root_base','first_next')and defs['tau_square']==('*','tau','tau')and defs['R9']==('-','tau_square',1),'literal first norm leader')
 if q['mode']!='raw30':
  need(defs['R14']==('+','D1','gam')and defs['D1']==('+','wn2','cam2')and defs['cam2']==('*','R10a','R12')and defs['A']==('+','a_square','a4m5')and defs['gam']==('*','ga'if q['mode']=='positive22'else'gamma_sum','a4m5')and defs['L15']==('*','R14','R14')and defs['Ac2']==('*','A','c2')and defs['c2']==('*','R10a','R10a')and defs['R15']==('+','Ac2',1),'literal main cancellation')
  main=q['comparisons'].index(['L15','R15']);X,a,c,G,H=[d[x]for x in('wn2','R12','R10a','gam','a4m5')]
  bounds[main]=max(2*X,X+a+c,X+G,a+c+G,2*G,H+2*c)
  kport='pell_gap'if q['orientation']['kappa_from_gap']else'index_rhs';a=d['R12'];k=d[kport];W=d['W'];rho=d['rho'];H=d['a4m5']
  terms=[2*W,a+W+k,rho+W+H,a+rho+k+H,2*rho+2*H,H+2*k,0]
  need(defs['difference_multiple']==('*',kport,'R12')and defs['kappa2']==('*',kport,kport)and defs['exponent_partial']==('+','W','difference_multiple')and defs['modulus_multiple']==('*','rho','a4m5')and defs['exponent_rhs']==('+','exponent_partial','modulus_multiple')and defs['norm_rhs']==('+','scaled_kappa2',1)and defs['mu2']==('*','exponent_rhs','exponent_rhs')and defs['scaled_kappa2']==('*','A','kappa2')and defs['a_square']==('*','R12','R12')and defs['a4']==('*',4,'R12')and defs['a4m5']==('+','a4',3),'entire input cancellation cone')
  inp=q['comparisons'].index(['mu2','norm_rhs']);bounds[inp]=max(terms)
 else:terms=None
 maximum=max(bounds);leaders=[i for i,v in enumerate(bounds)if v==maximum]
 # Each maximal residual is among these explicit nonzero leading templates.
 recognized={first:'(UM*ksn2)^2; nonzero by actual scale/monic difference leaders',q['comparisons'].index(['L17','P17']):'chosen auxiliary coefficient times square of chosen auxiliary root',q['comparisons'].index(['ic22','R16']):'i^2*c^4'}
 if q['mode']!='raw30':recognized[inp]='-4*delta^2*a^5 (old kappa), or 8*rho*a^2*kappa (reversed kappa)'
 need(all(i in recognized for i in leaders),'all dominant residuals have uniform nonzero leaders')
 return dict(exact_degree=2*maximum,residual_degree_upper_bounds=bounds,dominant_residual_indices=leaders,dominant_leading_templates={str(i):recognized[i]for i in leaders},input_expanded_term_bounds=terms,gate_degree_bounds=d,scope='All supplied positive witnesses and ordinary input degree1, fixed numeral ports degree0. Nonzero residual leaders and real sum of squares prove uniform exact degree.')

def local_identities():
 # Sparse integer coefficients in independent atoms; no numerical sampling.
 def var(n):return {(n,):1}
 def add(a,b,s=1):
  z=dict(a)
  for m,c in b.items():z[m]=z.get(m,0)+s*c
  return {m:c for m,c in z.items()if c}
 def mul(a,b):
  z={}
  for m,c in a.items():
   for n,d in b.items():k=tuple(sorted(m+n));z[k]=z.get(k,0)+c*d
  return {m:c for m,c in z.items()if c}
 def scale(a,k):return {m:c*k for m,c in a.items()if c*k}
 def total(*terms):
  z={}
  for a in terms:z=add(z,a)
  return z
 sq=lambda a:mul(a,a);one={():1}
 X,a,c,G,H,W,k,rho,U,V,T,K,y=[var(n)for n in ('X','a','c','G','H','W','k','rho','U','V','T','K','y')]
 main=add(add(sq(total(X,mul(a,c),G)),mul(add(sq(a),H),sq(c)),-1),one,-1)
 want=total(sq(X),scale(mul(mul(X,a),c),2),scale(mul(X,G),2),scale(mul(mul(a,c),G),2),sq(G),scale(mul(H,sq(c)),-1),scale(one,-1))
 need(main==want,'entire main cancellation identity')
 inp=add(add(sq(total(W,mul(a,k),mul(rho,H))),mul(add(sq(a),H),sq(k)),-1),one,-1)
 want=total(sq(W),scale(mul(mul(a,W),k),2),scale(mul(mul(rho,W),H),2),scale(mul(mul(mul(a,rho),k),H),2),mul(sq(rho),sq(H)),scale(mul(H,sq(k)),-1),scale(one,-1))
 need(inp==want,'entire input cancellation identity')
 old=add(mul(T,add(sq(U),sq(y),-1)),add(one,sq(y),-1),-1);corrections=[]
 for root,coef in ((True,False),(False,True),(True,True)):
  new=add(mul(K if coef else T,add(sq(V if root else U),sq(y),-1)),add(one,sq(y),-1),-1)
  change={}
  if coef:change=add(change,mul(add(T,K,-1),add(sq(V if root else U),sq(y),-1)),-1)
  if root:change=add(change,mul(mul(T,add(U,V,-1)),add(U,V)),-1)
  need(add(new,old,-1)==change,'exact protected auxiliary residual correction')
  need(add(sq(new),sq(old),-1)==mul(change,add(scale(old,2),change)),'exact changed SOS correction')
  corrections.append(dict(root=root,coefficient=coef,terms=[[list(m),c]for m,c in sorted(change.items())]))
 return dict(main=[[list(m),c]for m,c in sorted(main.items())],input=[[list(m),c]for m,c in sorted(inp.items())],auxiliary_corrections=corrections)

def full_coefficients(q):
 prime=1000000007;fixed={n:15 if n=='Bm1'else 3 for n in q['fixed_numerals']};v={n:2+(i%7)for i,n in enumerate(q['witnesses']+[q['ordinary_input']])}
 if 'c'in v:v['c']=v['eta']+3
 def trim(a):
  while len(a)>1 and a[-1]==0:a.pop()
  return a
 def add(a,b,s):
  z=[0]*max(len(a),len(b))
  for i,x in enumerate(a):z[i]=x
  for i,x in enumerate(b):z[i]=(z[i]+s*x)%prime
  return trim(z)
 def mul(a,b):
  z=[0]*(len(a)+len(b)-1)
  for i,x in enumerate(a):
   for j,y in enumerate(b):z[i+j]+=x*y
  return trim([x%prime for x in z])
 e={n:[x]for n,x in fixed.items()};e.update({n:[0,x]for n,x in v.items()})
 for n,o,a,b in q['polynomial_source']:
  a=e[a]if type(a)is str else[a];b=e[b]if type(b)is str else[b];e[n]=mul(a,b)if o=='*'else add(a,b,1 if o=='+'else-1)
 value=e[q['output']];need(len(value)-1==q['degree']['exact_degree'],'entire diagnostic polynomial attains proven degree')
 return dict(prime=prime,degree=len(value)-1,top_coefficient=value[-1],all_coefficients_sha256=sha(stable(value).encode()))

def verify(root):
 auth(root);original=json.loads((root/PARENT).read_text())['forms'];asymmetric_forms={f['packet']['mode']:f['packet']for f in json.loads((root/'complete74_asymmetric_scale_transfer.json').read_text())['forms']};forms=[];counts=Counter();minima={};local=local_identities()
 for item in original:
  p=item['packet'];mode=p['mode'];free=p['fixed_numerals']+p['witnesses']+[p['ordinary_input']]
  for asym in(False,True):
   parent=copy.deepcopy(p)
   if asym:
    for row in parent['source']:
     if row[0]=='wn2':row[3]='q'
    parent['polynomial_source'],parent['output']=finalize(parent['source'],parent['comparisons'])
    saved=asymmetric_forms[mode]
    need(all(parent[k]==saved[k]for k in ('source','comparisons','polynomial_source','output','witnesses','ordinary_input','fixed_numerals')),'exact proved asymmetric source boundary')
   bits=4 if mode=='raw30'else 3 if mode=='positive22'else 2
   for choice in itertools.product((False,True),repeat=bits):
    E,C,K=False,False,False
    if mode=='raw30':E,C,ar,ac=choice
    elif mode=='positive22':K,ar,ac=choice
    else:ar,ac=choice
    q=build(p,asym,E,C,K,ar,ac);proof=conditional_identity(parent,q)
    cl=ledger(q['source'],free,[x for pair in q['comparisons']for x in pair],q['fixed_numerals']);pl=ledger(q['polynomial_source'],free,[q['output']],q['fixed_numerals'])
    need(cl['operations']==74 and cl['M']==40 and cl['A']==34 and pl['operations']=={'raw30':130,'positive22':106,'signed20':100}[mode],'unchanged whole paid costs')
    q['certificate_ledger']=cl;q['polynomial_ledger']=pl;q['degree']=degree_proof(q)
    # Remove old parent-only metadata rather than presenting it as active.
    for key in('exact_polynomial_degree','original_comparison_indices','transformation'):q.pop(key,None)
    expansion=full_coefficients(q);counts['whole_sources']+=1;counts['live_paid_gates']+=pl['operations'];counts['retained_residual_identities']+=len(q['comparisons']);counts['full_coefficient_expansions']+=1
    name=mode+('/asymmetric'if asym else'/symmetric');minima[name]=min(minima.get(name,10**9),q['degree']['exact_degree'])
    forms.append(dict(packet=q,conditional_proof=proof,full_coefficient_check=expansion,source_sha256=sha(stable(q['polynomial_source']).encode())))
 need(len(forms)==56 and minima=={'raw30/symmetric':20,'raw30/asymmetric':20,'positive22/symmetric':56,'positive22/asymmetric':48,'signed20/symmetric':84,'signed20/asymmetric':64},'finite family inventory and minima')
 return dict(status='PASS',source_sha256=sha(Path(__file__).read_bytes()),pins=PINS,scope='56 explicitly enumerated same-zero equation orientations, all comparisons and supplied coordinates retained. Every full source saved. Exact degrees from nonzero residual leaders, not unconditional full polynomial identity. No arbitrary circuit optimality or new operation bound.',minima=minima,counts=dict(counts),local_coefficient_identities=local,forms=forms)

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();r=verify(a.root)
 if a.expect:need(stable(r)==stable(json.loads(a.expect.read_text())),'exact saved receipt')
 if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 print(json.dumps(dict(status=r['status'],counts=r['counts'],minima=r['minima'])))
if __name__=='__main__':main()
