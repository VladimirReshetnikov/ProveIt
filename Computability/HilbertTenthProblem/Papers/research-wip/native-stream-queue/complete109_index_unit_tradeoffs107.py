#!/usr/bin/env python3
"""Two complete index-unit tradeoffs:109/32 and107/42,24 positive witnesses.

Exact same-coordinate integer zero sets as the frozen asymmetric113 parent.
Only two fully emitted partitions; no general grouping or optimality claim.
"""
from __future__ import annotations
import argparse,copy,hashlib,json,random,subprocess,sys,tempfile
from pathlib import Path
from fractions import Fraction
from functools import reduce
if not __debug__:raise RuntimeError('run without -O')
PINS={'complete74_gap_selective_projection113.py': '573f1e8b0c89ef039a2a7fc40bad959cf7e362bcec4c96b3536974e7b71316c4', 'complete74_gap_selective_projection113.json': '2636f00a9e67f53a144986382442f456427257d498e33960e023e9c986b6b9c3', 'complete74_gap_selective_projection113.md': '3539d2fa0721eb8448409d075261a6508cc7adc1d887e3905cfeaed737396afa', 'complete74_factored_first_norm.py': '7c4b10fa78a3fa6517083c41fc6228dd403fec5ac87f2ca6b80b45dd60e8b908', 'complete74_factored_first_norm.json': '7ebfa54d3846d1c3a6ff7b8e5cd143f3ac80f8299b51698a9f45681d3524eb28', 'complete74_factored_first_norm.md': '119b51ca9a5d50e0eb998b334af87c1ea3eb0913f956b4f9d7a985f5d1159d9f', 'complete75_positive_elimination.py': '70123af4f0787b38271f7c4f0fa60e4235cd2f1964ee1b0ad345fe0e3bb82749', 'complete75_positive_elimination.json': '03743efca27972fd97667501af214626481acb4993ed006b9d4033766c0ec703', 'complete75_positive_elimination.md': '59cc280280bb8ab74318f648da56aabf31317f42a8a08d01851c5f8db0232d6b', 'complete75_positive_root89.py': 'f850ee8cd5e00b9235a8f192d2f95f6b27cf72a40c3f6b6e3fa054700d793c72', 'complete75_positive_root89.md': '7b85195a800b909e3bf6e55fa85decfaa08299cf1e100efa866659571d192085', 'complete86_first_root_partitions.json': '7535a1b2d36f802d6d72bab5c7cfe807c90b802398ed817ea990b76240b7cdc5', 'complete113_main_input_units111.py': '152905dd07e507289fe9f321982f5e680ec34b6a3ef23f7205bd370ad6623d16', 'complete113_main_input_units111.json': 'b9702ea066114aec3aef374a480fb2049f47a47d1daf580ea42e595107ebee87', 'complete113_main_input_units111.md': '9f73c0d51f5e1fe9237b0ffc3cbbba49f93b08a0b6242693425f0e086897905f', '../../1980/FIXED_RAW_UNIVERSAL_75_PROOF.md': 'e381124c969087ffa867448177a9df693d81e7bd85dd3a8489d443220fba053d', '../../1980/PELL_RELAXED_AUXILIARY_PROOF.md': '9849260ea2776d26e9b615e0e1ed6fcd9b1c9e0e4cedb6cd8aaa2c0346ecbc90', '../../1980/HALF_PARAMETER_PELL_92_PROOF.md': 'c1132ffe3610ff4132ca0a82312e24774328f4e9b3ed3b6f641055a7f29bfa7b', 'pell_kernel_half_binomial42.md': '0df596859d84aa1cf1d4636457937274e8fdac0c1f8da3196962d911be232992', 'complete113_asymmetric_retained109.py': '5017530a67107651cbde1cbfd81e4a2cf0aad294bb81997789e8e749a1ea2368', 'complete113_asymmetric_retained109.json': '8a037d2830ef3cbbfe7f0b02b71b5337ffac8a3e34cf8391c09257d0babb9f24', 'complete113_asymmetric_retained109.md': 'cee18b24b50fcea5f3cd6fa9fb20f8dbdd5ae9f5e99107e24ffff4e66b3305f0'}
def need(ok,msg):
 if not ok:raise ValueError(msg)

def sha(b):return hashlib.sha256(b).hexdigest()

def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys()and all(exact(a[k],b[k])for k in a)
 if type(a)in(list,tuple):return len(a)==len(b)and all(exact(x,y)for x,y in zip(a,b))
 return a==b

def execute(rows,values):
 d=dict(values)
 for n,op,a,b in rows:
  a=a if type(a)is int else d[a];b=b if type(b)is int else d[b]
  d[n]=a*b if op=='*'else a+b if op=='+'else a-b
 return d

def inspect(rows,free,roots):
 ready=set(free);deps={};m=0;deg={v:1 for v in free}
 for v in ['Bm1','Kconstant','twice_cell_bits','inner_bits','MC','MF']:deg[v]=0
 for n,op,a,b in rows:
  need(type(n)is str and n not in ready and op in('+','-','*'),'typed fresh gate')
  need(all(type(v)is int or type(v)is str and v in ready for v in(a,b)),'exact closed operands')
  da=0 if type(a)is int else deg[a];db=0 if type(b)is int else deg[b];deg[n]=da+db if op=='*'else max(da,db)
  ready.add(n);deps[n]=(a,b);m+=op=='*'
 live=set();stack=list(roots)
 while stack:
  v=stack.pop()
  if type(v)is str and v not in live:live.add(v);stack.extend(deps.get(v,()))
 need(set(deps)<=live and set(free)<=live,'all gates and supplied fields live')
 return {'operations':len(rows),'M':m,'A':len(rows)-m,'all_gates_live':True,'free':sorted(free),'literal_degree_upper_bound':max(0 if type(v)is int else deg[v]for v in roots)}

def finalizer(rows,pairs):
 out=copy.deepcopy(rows)
 for i,(a,b)in enumerate(pairs):out += [[f'residual_{i}','-',a,b],[f'square_{i}','*',f'residual_{i}',f'residual_{i}']]
 name='square_0'
 for i in range(1,len(pairs)):
  nextname=f'sum_{i}';out.append([nextname,'+',name,f'square_{i}']);name=nextname
 return out,name

class Interner:
 def __init__(self):self.nodes={}
 def node(self,v):
  if v not in self.nodes:self.nodes[v]=len(self.nodes)
  return self.nodes[v]
 def atom(self,v):return self.node(('atom',type(v).__name__,v))
 def op(self,op,a,b):return self.node((op,a,b))
 def run(self,rows,free):
  d={v:self.atom(v)for v in free}
  for n,op,a,b in rows:d[n]=self.op(op,self.atom(a)if type(a)is int else d[a],self.atom(b)if type(b)is int else d[b])
  return d

def authenticated(root=None):
 root=Path(root)if root is not None else Path(__file__).resolve().parent;blobs={}
 for name,pin in PINS.items():
  paths=[root/name,root/Path(name).name,Path(__file__).resolve().parent/name,Path(__file__).resolve().parent/Path(name).name]
  path=next((p for p in paths if p.exists()),paths[0]);data=path.read_bytes()
  need(sha(data)==pin,'parent pin '+name);blobs[name]=data
 return blobs

def padd(a,b,sign=1):
 c=dict(a)
 for m,v in b.items():c[m]=c.get(m,0)+sign*v
 return{m:v for m,v in c.items()if v}

def pmul(a,b):
 c={}
 for m,v in a.items():
  for n,w in b.items():
   key=tuple(x+y for x,y in zip(m,n));c[key]=c.get(key,0)+v*w
 return{k:v for k,v in c.items()if v}

def ppow(p,k,one):
 r=one
 for _ in range(k):r=pmul(r,p)
 return r

def expanded(rows,free):
 z=(0,)*len(free);d={v:{tuple(int(i==j)for i in range(len(free))):1}for j,v in enumerate(free)}
 const=lambda n:{z:n}if n else{}
 for n,op,a,b in rows:
  a=const(a)if type(a)is int else d[a];b=const(b)if type(b)is int else d[b];d[n]=pmul(a,b)if op=='*'else padd(a,b,1 if op=='+'else-1)
 return d,const

VARIANTS=('degree32','degree42')
UNITS={3:'first_unit',7:'main_unit',12:'input_unit',9:'aux_unit',5:'index_unit'}
GROUPS={'degree32':[[3,7],[5,12],[9]],'degree42':[[3,12],[5,7,9]]}
SPECS={'degree32':(109,53,56,11,32),'degree42':(107,53,54,10,42)}

def canonical_parent(*,root=None):
 receipt=json.loads(authenticated(root)['complete113_asymmetric_retained109.json']);matches=[f['packet']for f in receipt['forms']if f['packet']['variant']=='sos']
 need(len(matches)==1,'unique complete asymmetric sos parent');p=matches[0]
 need((p['polynomial_ledger']['operations'],len(p['comparisons']),len(p['witnesses']),p['exact_polynomial_degree'])==(113,13,24,24),'selected source scope')
 return p

def _rewrite(p,variant):
 need(type(variant)is str and variant in VARIANTS,'exact two-variant selector')
 by={r[0]:r for r in p['source']};pairs=p['comparisons']
 expected={'r1':['r1','+','r',1],'R11':['R11','+','r1','hpm1'],'hpm1':['hpm1','*','h','UM'],'R10b':['R10b','+','eta','zeta'],
  'R9':['R9','-',1,'tau_square'],'R15':['R15','+','Ac2',1],'norm_rhs':['norm_rhs','+','scaled_kappa2',1],'P17':['P17','-',1,'aux_y2'],
  'wn2':['wn2','*','w','q'],'sn2':['sn2','*','s','n2'],'ic2':['ic2','*','i','c2'],'ic22':['ic22','*','ic2','ic2']}
 need(all(by[n]==v for n,v in expected.items()),'literal frozen arithmetic cones')
 need([r for r in p['source']if 'r1'in r[2:]]==[by['R11']]and all('r1'not in c for c in pairs),'r1 has only R11 consumer')
 for n in('R11','R9','R15','norm_rhs','P17'):
  need(not any(n in r[2:]for r in p['source'])and sum(n in c for c in pairs)==1,'private old comparison side '+n)
 for idx,pair in{3:['R9','L9'],5:['R10b','R11'],7:['L15','R15'],9:['L17','P17'],12:['mu2','norm_rhs']}.items():need(pairs[idx]==pair,'exact original comparison index')
 rows=[]
 for n,o,a,b in p['source']:
  if n=='R9':continue
  if n=='R15':n,o,a,b='main_unit','-','L15','Ac2'
  elif n=='norm_rhs':n,o,a,b='input_unit','-','mu2','scaled_kappa2'
  elif n=='P17':n,o,a,b='aux_unit','+','L17','aux_y2'
  elif n=='r1':n,o,a,b='index_partial','-','R10b','r'
  elif n=='R11':n,o,a,b='index_unit','-','index_partial','hpm1'
  rows.append([n,o,a,b])
  if n=='L9':rows.append(['first_unit','+','tau_square','L9'])
 need(len(rows)==75,'unit-core schedule still75 gates')
 newpairs=[];mapping=[None]*len(pairs)
 for i,pair in enumerate(pairs):
  if i not in UNITS:
   mapping[i]={'parent_index':i,'new_index':len(newpairs),'role':'same_residual'};newpairs.append(copy.deepcopy(pair))
 groupmeta=[]
 for gi,group in enumerate(GROUPS[variant]):
  port=UNITS[group[0]]
  for j,index in enumerate(group[1:]):
   n=f'unit_product_{gi}_{j}';rows.append([n,'*',port,UNITS[index]]);port=n
  j=len(newpairs);newpairs.append([port,1]);groupmeta.append({'parent_indices':group,'unit_ports':[UNITS[i]for i in group],'product_port':port,'comparison_index':j})
  for i in group:mapping[i]={'parent_index':i,'new_index':j,'role':'unit_group_member','old_residual_sign':-1 if i==3 else 1}
 poly,output=finalizer(rows,newpairs);free=p['polynomial_ledger']['free'];cert=inspect(rows,free,[v for pair in newpairs for v in pair]);led=inspect(poly,free,[output])
 ops,m,a,eq,degree=SPECS[variant];need((led['operations'],led['M'],led['A'],len(newpairs))==(ops,m,a,eq),'whole paid finalizer counts')
 raw=[]
 for old in p['original_raw_comparison_map']:
  r=copy.deepcopy(old)
  if r['new_index']is not None:
   current=mapping[r['new_index']];r['new_index']=current['new_index'];r['role']=current['role']
  else:r['role']='historical_positive_definition'
  raw.append(r)
 return {'variant':variant,'parameters':copy.deepcopy(p['parameters']),'fixed_numerals':copy.deepcopy(p['fixed_numerals']),'witnesses':copy.deepcopy(p['witnesses']),'domains':p['domains'],
  'source':rows,'comparisons':newpairs,'polynomial_source':poly,'output':output,'certificate_ledger':cert,'polynomial_ledger':led,'exact_polynomial_degree':degree,
  'unit_interfaces':dict((name,port)for name,port in [('first','first_unit'),('main','main_unit'),('input','input_unit'),('auxiliary','aux_unit'),('index','index_unit')]),
  'unit_groups':groupmeta,'parent_comparison_map':mapping,'original_raw_comparison_map':raw,'same_supplied_coordinates':True,
  'integer_zero_relation':'Exactly the same entire integer zero set as the selected asymmetric sos113 parent; each group has at most one unprotected factor.',
  'positive_theorem':'Inherits the full ordinary-input positive-integer relation and unbounded duration, with all24 witnesses unchanged.',
  'offzero_relation':'Eight unchanged residual squares plus the specified product residual squares. Full correction to the13-row parent is recorded separately; not the same polynomial off zero.',
  'index_identity':'index_unit-1=R10b-(r+1+hpm1), with index_unit=(R10b-r)-hpm1',
  'active_interfaces':dict(p['active_interfaces'],index='index_unit'),
  'historical_provenance':{'parent_variant':p['variant'],'parent_exact_degree':p['exact_polynomial_degree'],'parent_ledger':p['polynomial_ledger'],'parent_scale':p['scale'],'parent_coordinate_relation':p['coordinate_relation'],'parent_historical_definitions':p['historical_parent'],'parent_original_raw_comparison_map':p['original_raw_comparison_map']},
  'scope':'Exactly these two complete fixed-program forms; all ordinary strong/input equations retained. Same coordinates as the asymmetric parent; no new coordinate projection or general grouping census.'}

def build(variant='degree42',*,root=None):return _rewrite(canonical_parent(root=root),variant)
def rewrite(parent,variant='degree42',*,root=None):
 p=canonical_parent(root=root);need(exact(parent,p),'entire canonical selected parent');return _rewrite(p,variant)
def checked(packet,*,root=None):
 need(type(packet)is dict,'exact packet');p=build(packet.get('variant'),root=root);need(exact(packet,p),'entire canonical child');return p

def polynomial_source(packet,*,root=None):return checked(packet,root=root)['polynomial_source']
def evaluate(packet,values,*,signed=False,root=None):
 p=checked(packet,root=root);need(type(signed)is bool and type(values)is dict and set(values)==set(p['polynomial_ledger']['free']),'exact full values and mode')
 need(all(type(n)is str and type(v)is int for n,v in values.items()),'exact integer values')
 if not signed:need(all(v>0 for v in values.values()),'strict positive coordinates and numeral ports')
 return execute(p['polynomial_source'],values)[p['output']]

def source_proof(p,c):
 I=Interner();a=I.run(p['source'],p['polynomial_ledger']['free']);b=I.run(c['source'],c['polynomial_ledger']['free']);common=set(a)&set(b)
 need(all(a[n]==b[n]for n in common),'all common source expressions identical')
 need(b['index_partial']==I.op('-',a['R10b'],a['r'])and b['index_unit']==I.op('-',b['index_partial'],a['hpm1']),'literal index expression')
 need(b['first_unit']==I.op('+',a['tau_square'],a['L9'])and b['main_unit']==I.op('-',a['L15'],a['Ac2'])and b['input_unit']==I.op('-',a['mu2'],a['scaled_kappa2'])and b['aux_unit']==I.op('+',a['L17'],a['aux_y2']),'actual four norm expressions')
 get=lambda env,v:I.atom(v)if type(v)is int else env[v]
 count=0
 for m in c['parent_comparison_map']:
  if m['role']=='same_residual':
   old=p['comparisons'][m['parent_index']];new=c['comparisons'][m['new_index']];need(all(get(a,x)==get(b,y)for x,y in zip(old,new)),'unchanged complete residual');count+=1
 # Exact affine identity expanded with independent k,r,hE; no typing is used.
 d,co=expanded([],['k','r','hE']);k,r,he=d.values();left=padd(padd(padd(k,r,-1),he,-1),co(1),-1);right=padd(k,padd(padd(r,co(1)),he),-1);need(left==right,'all-value index residual equality')
 # Every final product is checked against the advertised group, including singles.
 for group in c['unit_groups']:
  port=b[group['unit_ports'][0]]
  for name in group['unit_ports'][1:]:port=I.op('*',port,b[name])
  need(port==b[group['product_port']]and c['comparisons'][group['comparison_index']]==[group['product_port'],1],'complete literal product group')
 return {'common_computed_gate_identities':sum(n in {r[0]for r in p['source']}for n in common),'unchanged_supplied_leaves':len(p['polynomial_ledger']['free']),'unchanged_residuals':count,'index_residual_identity':[[list(m),v]for m,v in sorted(left.items())],'literal_unit_groups':copy.deepcopy(c['unit_groups'])}

UNIT_ORDER=['first','main','input','auxiliary','index']
def full_correction(c):
 d,co=expanded([],UNIT_ORDER);units=list(d.values());one=co(1);square=lambda x:pmul(x,x);old={}
 for p in units:old=padd(old,square(padd(p,one,-1)))
 order={3:0,7:1,12:2,9:3,5:4};new={}
 for group in c['unit_groups']:
  product=one
  for i in group['parent_indices']:product=pmul(product,units[order[i]])
  new=padd(new,square(padd(product,one,-1)))
 diff=padd(new,old,-1)
 return {'unit_order':UNIT_ORDER,'coefficients':[[list(m),v]for m,v in sorted(diff.items())],'meaning':'Complete child SOS minus complete selected parent SOS; unchanged ordinary squares cancel exactly.'}

def degree_proof(c):
 free=c['polynomial_ledger']['free'];d,co=expanded(c['source'],free);weights=[int(v not in c['fixed_numerals'])for v in free]
 degree=lambda p:max((sum(x*w for x,w in zip(m,weights))for m in p),default=-1)
 top=lambda p:{m:v for m,v in p.items()if sum(x*w for x,w in zip(m,weights))==degree(p)}
 one=co(1);M=lambda *ps:reduce(pmul,ps,one);power=lambda p,n:ppow(p,n,one)
 k=padd(d['eta'],d['zeta']);first=M(power(d['Bm1'],7),d['w'],power(d['s'],2),k,power(d['Jrep'],7),padd(pmul(co(2),d['tau_gap']),k,-1))
 dt=padd(M(d['Bm1'],d['w'],d['Jrep']),M(co(4),d['ga'],d['a']));main=padd(power(dt,2),M(co(2),d['a'],d['c'],dt));inp=M(co(-4),power(d['delta'],2),power(d['a'],5));aux=M(power(d['i'],2),power(d['j'],2),power(d['c'],6));index=M(co(-1),d['h'],d['w'],d['s'],power(d['Bm1'],4),power(d['Jrep'],4))
 expected=[first,main,inp,aux,index];ns=[12,4,7,10,7]
 for name,leader,n in zip(UNIT_ORDER,expected,ns):
  p=d[c['unit_interfaces'][name]];need(degree(p)==n and top(p)==leader,'actual multivariate unit leader '+name)
 residuals=[padd(co(a)if type(a)is int else d[a],co(b)if type(b)is int else d[b],-1)for a,b in c['comparisons']];ds=[degree(p)for p in residuals];D=max(ds);ix=[i for i,n in enumerate(ds)if n==D]
 need(len(ix)==1,'unique complete leading residual');lead=power(top(residuals[ix[0]]),2)
 want=power(M(first,main),2)if c['variant']=='degree32'else power(M(index,main,aux),2)
 need(lead==want and 2*D==c['exact_polynomial_degree'],'uniform complete exact degree')
 return {'exact_degree':2*D,'unit_order':UNIT_ORDER,'unit_degrees':ns,'residual_exact_degrees':ds,'unique_leading_residual':ix[0],'variables':free,'degree_weights':weights,
  'highest_homogeneous_polynomial':[[list(m),v]for m,v in sorted(lead.items())],'fixed_parameter_dependencies':sorted({free[j]for m in lead for j,e in enumerate(m)if e and not weights[j]}),
  'uniformity':'Closed multivariate leaders agree exactly with source expansion; nonzero for every admissible Bm1>0, and independent of all other fixed program numerals.',
  'literal_propagated_upper':c['polynomial_ledger']['literal_degree_upper_bound']}

def degree_certificate(packet,*,root=None):return degree_proof(checked(packet,root=root))

def signed_unit_cases():
 # Finite exhaustive integer-factor census including zero and nonunits. The
 # general implication is the integer-unit theorem, not this finite sample.
 import itertools
 cases=0;protected=0
 for a in range(4):
  D=a*a+4*a+3
  for x in range(4):
   for y in range(4):need((x*x-D*y*y)%4!=3,'main/input sign');protected+=1
 for t in range(4):
  for H in range(4):
   for y in range(4):need((t*t*(H*H-y*y)+y*y)%4!=3,'auxiliary sign');protected+=1
 for first,main,inp,aux,index in itertools.product(range(-2,3),repeat=5):
  if -1 in(main,inp,aux):continue
  ordinary=(first,main,inp,aux,index)==(1,1,1,1,1)
  need((first*main==1 and index*inp==1 and aux==1)==ordinary,'degree32 grouped unit equivalence')
  need((first*inp==1 and index*main*aux==1)==ordinary,'degree42 grouped unit equivalence');cases+=1
 return {'protected_mod4_cases':protected,'integer_factor_census':cases}

def verify(root=None):
 p=canonical_parent(root=root);rng=random.Random(1073242);counts={'complete_corrections':0,'signed_cases':0,'rational_cases':0,'individual_residual_values':0,'public_evaluations':0,'guards':0,'copies':0};forms=[]
 for variant in VARIANTS:
  c=_rewrite(p,variant);proof=source_proof(p,c);correction=full_correction(c);degree=degree_proof(c)
  for case in range(96):
   values={n:rng.randint(-4,5)if case<48 else rng.randint(1,5)for n in c['polynomial_ledger']['free']};values.update(Bm1=15,Kconstant=163,twice_cell_bits=8,inner_bits=3,MC=2,MF=19)
   if case>=80:values={n:Fraction(v,3)if n not in c['fixed_numerals']else v for n,v in values.items()}
   old=execute(p['polynomial_source'],values);new=execute(c['polynomial_source'],values)
   N=[new[c['unit_interfaces'][name]]for name in UNIT_ORDER];diff=0
   for mon,v in correction['coefficients']:
    for x,e in zip(N,mon):v*=x**e
    diff+=v
   need(new[c['output']]-old[p['output']]==diff,'complete all-value SOS correction')
   for m in c['parent_comparison_map']:
    i=m['parent_index'];aa,bb=p['comparisons'][i];get=lambda env,x:x if type(x)is int else env[x]
    if m['role']=='same_residual':
     a,b=c['comparisons'][m['new_index']];need(get(old,aa)-get(old,bb)==get(new,a)-get(new,b),'full retained residual')
    else:need(get(old,aa)-get(old,bb)==m['old_residual_sign']*(new[UNITS[i]]-1),'actual unit versus parent residual')
    counts['individual_residual_values']+=1
   counts['complete_corrections']+=1;counts['signed_cases']+=case<48;counts['rational_cases']+=case>=80
   if case in(0,48):need(evaluate(c,values,signed=case==0,root=root)==new[c['output']],'public full evaluation');counts['public_evaluations']+=1
  bad=[]
  for field in('source','polynomial_source','comparisons','witnesses','unit_groups'):
   q=copy.deepcopy(c);q[field]=tuple(q[field]);bad.append(q)
  for field in('source','polynomial_source'):
   for i,row in enumerate(c[field]):
    for j in(2,3):
     if type(row[j])is int:
      for v in(float(row[j]),bool(row[j])):
       q=copy.deepcopy(c);q[field][i][j]=v;bad.append(q)
  q=copy.deepcopy(c);q['exact_polynomial_degree']=float(q['exact_polynomial_degree']);bad.append(q)
  q=copy.deepcopy(c);q['parent_comparison_map'][5]['new_index']=999;bad.append(q)
  q=copy.deepcopy(c);q['source'].append(['unused','+',1,0]);bad.append(q)
  q=copy.deepcopy(c);q['unit_groups'][0]['unit_ports'].reverse();bad.append(q)
  for q in bad:
   try:checked(q,root=root)
   except ValueError:counts['guards']+=1
   else:raise AssertionError('malformed child accepted')
  for field in('source','comparisons','witnesses'):
   q=copy.deepcopy(p);q[field]=tuple(q[field])
   try:rewrite(q,variant,root=root)
   except ValueError:counts['guards']+=1
   else:raise AssertionError('malformed parent accepted')
  for q in(c,dict(p,variant='pair')):
   try:rewrite(q,variant,root=root)
   except ValueError:counts['guards']+=1
   else:raise AssertionError('wrong or no-op parent accepted')
  one={v:1 for v in c['polynomial_ledger']['free']}
  for name,value in [('x',0),('a',True),('r',1.0),('eta',-1)]:
   values=dict(one);values[name]=value
   try:evaluate(c,values,root=root)
   except ValueError:counts['guards']+=1
   else:raise AssertionError('invalid domain accepted')
  for call in(lambda:evaluate(c,one,signed=1,root=root),lambda:degree_certificate(bad[-1],root=root)):
   try:call()
   except ValueError:counts['guards']+=1
   else:raise AssertionError('invalid mode/degree accepted')
  for field in('source','polynomial_source','unit_groups','parent_comparison_map','historical_provenance'):
   q=build(variant,root=root);q[field].clear();need(exact(build(variant,root=root),c),'defensive copies');counts['copies']+=1
  forms.append({'packet':c,'source_proof':proof,'complete_correction':correction,'degree_certificate':degree})
 counts.update(signed_unit_cases())
 for variant in(None,True,1,'unknown'):
  try:build(variant,root=root)
  except ValueError:counts['guards']+=1
  else:raise AssertionError('invalid variant accepted')
 blobs=authenticated(root)
 with tempfile.TemporaryDirectory(prefix='index_unit107_')as tmp:
  path=Path(tmp)
  for name,data in blobs.items():(path/Path(name).name).write_bytes(data)
  build(root=path);counts['warm_pin_rejections']=0
  for name,data in blobs.items():
   q=path/Path(name).name;q.write_bytes(data+b'\n')
   try:build(root=path)
   except ValueError:counts['warm_pin_rejections']+=1
   else:raise AssertionError('changed parent/proof bytes accepted')
   q.write_bytes(data)
 proc=subprocess.run([sys.executable,'-O',str(Path(__file__).resolve()),'--root',str(root)],capture_output=True,text=True);need(proc.returncode!=0 and 'run without -O'in proc.stderr,'optimized Python rejected');counts['optimized_mode_rejections']=1
 prior=json.loads(blobs['complete113_asymmetric_retained109.json'])['known_union_frontier'];points=[tuple(p)for p in prior]+[(f['packet']['polynomial_ledger']['operations'],f['packet']['exact_polynomial_degree'])for f in forms]
 frontier=sorted({p for p in points if not any(q[0]<=p[0]and q[1]<=p[1]and q!=p for q in points)})
 return {'status':'PASS_COMPLETE_INDEX_UNIT_TRADEOFFS107','source_sha256':sha(Path(__file__).read_bytes()),'parent_pins':PINS,'canonical_parent':p,'counts':counts,'forms':forms,'known_union_frontier':[list(p)for p in frontier],
  'scope':'Exactly two complete source rewrites:109/32 and107/42, same24coordinates and entire integer zero set as authenticated asymmetric113 parent. Universal semantics use its positive-input fixed-program slice. No grouping census or optimality claim.'}

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();r=verify(a.root)
 if a.expect:need(exact(r,json.loads(a.expect.read_text())),'typed saved receipt mismatch')
 if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 print(json.dumps({'status':r['status'],'counts':r['counts'],'known_union_frontier':r['known_union_frontier']},sort_keys=True))
if __name__=='__main__':main()
