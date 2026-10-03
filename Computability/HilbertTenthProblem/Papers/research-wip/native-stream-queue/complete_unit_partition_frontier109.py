#!/usr/bin/env python3
"""Complete37-partition protected-unit family; new109-operation degree28 form.

Same24coordinates and entire integer zero sets as asymmetric113. This finite
family separates the two units without an unconditional sign exclusion.
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


PINS.update({'complete109_index_unit_tradeoffs107.py':'d255896294684f8d6411d992f5f0ba60a7f4051aa841d7e325f5347d64c23600','complete109_index_unit_tradeoffs107.json':'3d8d8d473cc866ebd585ac5605648839cfe014e98b5be2a10938cc0dfcfe12b3','complete109_index_unit_tradeoffs107.md':'928f760d73a7da081eace63cfcb144f41cd4271fcd92fbc3860d482738b16b9b'})

UNIT_ORDER=['first','main','input','auxiliary','index']
UNIT_DEGREES=[12,4,7,10,7]
INDICES=[3,7,12,9,5]
UNITS=dict(zip(INDICES,['first_unit','main_unit','input_unit','aux_unit','index_unit']))
DEFAULT=[[0],[1,3],[2,4]]

def partitions():
 out=[]
 def walk(i,groups):
  if i==5:out.append(copy.deepcopy(groups));return
  for j in range(len(groups)):
   groups[j].append(i);walk(i+1,groups);groups[j].pop()
  groups.append([i]);walk(i+1,groups);groups.pop()
 walk(0,[]);return out

def admissible(groups):return not any(0 in g and 4 in g for g in groups)
def validate_partition(groups):
 need(type(groups)is list and all(type(g)is list and g for g in groups),'canonical list of nonempty lists')
 need(all(type(i)is int for g in groups for i in g),'exact unit indices')
 need(all(g==sorted(g)for g in groups)and groups==sorted(groups,key=lambda g:g[0]),'canonical unit/group order')
 need(sorted(i for g in groups for i in g)==list(range(5)),'each of five units exactly once')
 need(admissible(groups),'at most one unprotected unit per group')
 return copy.deepcopy(groups)
def canonical_parent(*,root=None):
 receipt=json.loads(authenticated(root)['complete113_asymmetric_retained109.json']);matches=[f['packet']for f in receipt['forms']if f['packet']['variant']=='sos']
 need(len(matches)==1,'unique complete asymmetric sos parent');p=matches[0]
 need((p['polynomial_ledger']['operations'],len(p['comparisons']),len(p['witnesses']),p['exact_polynomial_degree'])==(113,13,24,24),'selected source scope')
 return p

def _rewrite(p,partition):
 partition=validate_partition(partition)
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
 for gi,group in enumerate([[INDICES[i]for i in g]for g in partition]):
  port=UNITS[group[0]]
  for j,index in enumerate(group[1:]):
   n=f'unit_product_{gi}_{j}';rows.append([n,'*',port,UNITS[index]]);port=n
  j=len(newpairs);newpairs.append([port,1]);groupmeta.append({'parent_indices':group,'unit_ports':[UNITS[i]for i in group],'product_port':port,'comparison_index':j})
  for i in group:mapping[i]={'parent_index':i,'new_index':j,'role':'unit_group_member','old_residual_sign':-1 if i==3 else 1}
 poly,output=finalizer(rows,newpairs);free=p['polynomial_ledger']['free'];cert=inspect(rows,free,[v for pair in newpairs for v in pair]);led=inspect(poly,free,[output])
 g=len(partition);ops,m,a,eq,degree=103+2*g,53,50+2*g,8+g,2*max(6,max(sum(UNIT_DEGREES[i]for i in block)for block in partition));need((led['operations'],led['M'],led['A'],len(newpairs))==(ops,m,a,eq),'whole paid finalizer counts')
 raw=[]
 for old in p['original_raw_comparison_map']:
  r=copy.deepcopy(old)
  if r['new_index']is not None:
   current=mapping[r['new_index']];r['new_index']=current['new_index'];r['role']=current['role']
  else:r['role']='historical_positive_definition'
  raw.append(r)
 return {'partition':copy.deepcopy(partition),'parameters':copy.deepcopy(p['parameters']),'fixed_numerals':copy.deepcopy(p['fixed_numerals']),'witnesses':copy.deepcopy(p['witnesses']),'domains':p['domains'],
  'source':rows,'comparisons':newpairs,'polynomial_source':poly,'output':output,'certificate_ledger':cert,'polynomial_ledger':led,'exact_polynomial_degree':degree,
  'unit_interfaces':dict((name,port)for name,port in [('first','first_unit'),('main','main_unit'),('input','input_unit'),('auxiliary','aux_unit'),('index','index_unit')]),
  'unit_groups':groupmeta,'parent_comparison_map':mapping,'original_raw_comparison_map':raw,'same_supplied_coordinates':True,
  'integer_zero_relation':'Exactly the same entire integer zero set as the selected asymmetric sos113 parent; each group has at most one unprotected factor.',
  'positive_theorem':'Inherits the full ordinary-input positive-integer relation and unbounded duration, with all24 witnesses unchanged.',
  'full_polynomial_identity':len(partition)==5,
  'offzero_relation':('The all-singleton partition is the identical complete parent polynomial.'if len(partition)==5 else'Eight unchanged residual squares plus specified product residual squares. The recorded full correction is not the zero polynomial.'),
  'index_identity':'index_unit-1=R10b-(r+1+hpm1), with index_unit=(R10b-r)-hpm1',
  'active_interfaces':dict(p['active_interfaces'],index='index_unit'),
  'historical_provenance':{'parent_variant':p['variant'],'parent_exact_degree':p['exact_polynomial_degree'],'parent_ledger':p['polynomial_ledger'],'parent_scale':p['scale'],'parent_coordinate_relation':p['coordinate_relation'],'parent_historical_definitions':p['historical_parent'],'parent_original_raw_comparison_map':p['original_raw_comparison_map']},
  'scope':'Exactly the37 canonical partitions that separate first/index; the other15 set partitions are outside this criterion, not asserted unsound. Same24coordinates, all ordinary strong/input equations retained. Finite family frontier, no unrestricted arithmetic optimality.'}


def build(partition=None,*,root=None):return _rewrite(canonical_parent(root=root),DEFAULT if partition is None else partition)
def rewrite(parent,partition=None,*,root=None):
 p=canonical_parent(root=root);need(exact(parent,p),'entire canonical selected parent');return _rewrite(p,DEFAULT if partition is None else partition)
def checked(packet,*,root=None):
 need(type(packet)is dict and 'partition'in packet,'exact full packet');p=build(packet['partition'],root=root);need(exact(packet,p),'entire canonical child');return p

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

def _unit_expansion(c):
 free=c['polynomial_ledger']['free'];d,co=expanded(c['source'][:75],free);weights=[int(v not in c['fixed_numerals'])for v in free]
 degree=lambda p:max((sum(x*w for x,w in zip(m,weights))for m in p),default=-1)
 top=lambda p:{m:v for m,v in p.items()if sum(x*w for x,w in zip(m,weights))==degree(p)}
 one=co(1);M=lambda *ps:reduce(pmul,ps,one);power=lambda p,n:ppow(p,n,one)
 k=padd(d['eta'],d['zeta']);first=M(power(d['Bm1'],7),d['w'],power(d['s'],2),k,power(d['Jrep'],7),padd(pmul(co(2),d['tau_gap']),k,-1))
 dt=padd(M(d['Bm1'],d['w'],d['Jrep']),M(co(4),d['ga'],d['a']));main=padd(power(dt,2),M(co(2),d['a'],d['c'],dt));inp=M(co(-4),power(d['delta'],2),power(d['a'],5));aux=M(power(d['i'],2),power(d['j'],2),power(d['c'],6));index=M(co(-1),d['h'],d['w'],d['s'],power(d['Bm1'],4),power(d['Jrep'],4))
 expected=[first,main,inp,aux,index];ns=[12,4,7,10,7]
 for name,leader,n in zip(UNIT_ORDER,expected,ns):
  p=d[c['unit_interfaces'][name]];need(degree(p)==n and top(p)==leader,'actual multivariate unit leader '+name)

 return free,d,co,weights,expected

def degree_proof(c,prepared=None):
 free,d,co,weights,expected=prepared if prepared is not None else _unit_expansion(c)
 degree=lambda p:max((sum(x*w for x,w in zip(m,weights))for m in p),default=-1)
 top=lambda p:{m:v for m,v in p.items()if sum(x*w for x,w in zip(m,weights))==degree(p)}
 one=co(1);mul=lambda ps:reduce(pmul,ps,one)
 residuals=[];tops=[];ds=[]
 for a,b in c['comparisons'][:8]:
  r=padd(co(a)if type(a)is int else d[a],co(b)if type(b)is int else d[b],-1);residuals.append(r);ds.append(degree(r));tops.append(top(r))
 need(ds==[1,3,4,5,6,6,2,3],'all eight nongrouped exact residual degrees')
 for group in c['partition']:
  lead=mul([expected[i]for i in group]);D=sum(UNIT_DEGREES[i]for i in group)
  need(degree(lead)==D,'nonzero exact product leader');ds.append(D);tops.append(lead)
 D=max(ds);indices=[i for i,n in enumerate(ds)if n==D];lead={}
 for i in indices:lead=padd(lead,pmul(tops[i],tops[i]))
 need(lead and degree(lead)==2*D==c['exact_polynomial_degree'],'sum of all maximal residual squares')
 fixeddeps=sorted({free[j]for m in lead for j,e in enumerate(m)if e and not weights[j]});need(set(fixeddeps)<={'Bm1'},'all other program numerals absent from leader')
 # All variable coordinates set to1 except gap=2; leave Bm1 indeterminate.
 # Every unit leader is nonzero for b>0, and squared sums below have positive coefficients.
 sample={}
 for mon,v in lead.items():
  value=v;exponent=0
  for n,e in zip(free,mon):
   if n=='Bm1':exponent=e
   elif n=='tau_gap':value*=2**e
  sample[exponent]=sample.get(exponent,0)+value
 sample={e:v for e,v in sample.items()if v}
 need(sample and all(v>0 for v in sample.values()),'uniform nonzero Q[Bm1] witness on every positive fixed slice')
 special=None
 if c['partition']==DEFAULT:
  mon=tuple({'ga':4,'a':4,'i':4,'j':4,'c':12}.get(n,0)for n in free)
  need(lead.get(mon)==256,'two-square109/28 fixed-parameter-independent coefficient');special={'powers':{'ga':4,'a':4,'i':4,'j':4,'c':12},'coefficient':256}
 return {'exact_degree':2*D,'unit_order':UNIT_ORDER,'unit_degrees':UNIT_DEGREES,'residual_exact_degrees':ds,'maximal_residual_indices':indices,'variables':free,'degree_weights':weights,
  'highest_homogeneous_polynomial':[[list(m),v]for m,v in sorted(lead.items())],'fixed_parameter_dependencies':fixeddeps,'positive_Bm1_witness':[[e,v]for e,v in sorted(sample.items())],
  'special_default_coefficient':special,'uniformity':'All complete maximal residual squares included. Exact source unit leaders, positive polynomial witness after tau_gap=2 and remaining variable coordinates1; nonzero for all admissible Bm1>0 independently of other fixed numerals.',
  'literal_propagated_upper':c['polynomial_ledger']['literal_degree_upper_bound']}

def degree_certificate(packet,*,root=None):return degree_proof(checked(packet,root=root))

def finite_unit_checks(groups):
 import itertools
 modcases=0
 for a,x,y in itertools.product(range(4),repeat=3):
  D=a*a+4*a+3;need((x*x-D*y*y)%4!=3,'main/input cannot be -1');modcases+=1
 for t,u,y in itertools.product(range(4),repeat=3):
  need((t*t*(u*u-y*y)+y*y)%4!=3,'auxiliary cannot be -1');modcases+=1
 n=0
 for units in itertools.product(range(-2,3),repeat=5):
  if -1 in(units[1],units[2],units[3]):continue
  want=units==(1,1,1,1,1)
  for partition in groups:
   got=all(reduce(lambda x,y:x*y,(units[i]for i in group),1)==1 for group in partition)
   need(got==want,'integer factor implication in admitted partition');n+=1
 return dict(mod4_residue_checks=modcases,finite_factor_partition_checks=n)

def verify(root=None):
 p=canonical_parent(root=root);allpart=partitions();groups=[g for g in allpart if admissible(g)]
 need(len(allpart)==52 and len({json.dumps(g)for g in allpart})==52 and len(groups)==37,'complete canonical five-element partition census')
 hist={k:sum(len(g)==k for g in groups)for k in range(2,6)};need(hist=={2:8,3:19,4:9,5:1},'admissible group-count census')
 base=_rewrite(p,DEFAULT);prepared=_unit_expansion(base);rng=random.Random(10928537);forms=[];counts={'forms':0,'all_value_corrections':0,'signed_cases':0,'rational_cases':0,'parent_residual_values':0,'complete_gates':0,'M':0,'A':0,'certificate_gates':0,'comparisons':0,'guards':0,'copies':0}
 for partition in groups:
  c=_rewrite(p,partition);proof=source_proof(p,c);correction=full_correction(c);degree=degree_proof(c,prepared)
  need(c['source'][:75]==base['source'][:75],'identical complete75-gate unit core')
  need((not correction['coefficients'])==c['full_polynomial_identity']==(len(partition)==5),'exact singleton polynomial identity exception')
  need(c['parameters']==p['parameters']and c['fixed_numerals']==p['fixed_numerals']and c['witnesses']==p['witnesses']and len(c['witnesses'])==24,'entire supplied interface conserved')
  for case in range(8):
   values={n:rng.randint(-4,5)if case<4 else rng.randint(1,6)for n in c['polynomial_ledger']['free']};values.update(Bm1=15,Kconstant=163,twice_cell_bits=8,inner_bits=3,MC=2,MF=19)
   if case in(2,6):values={n:Fraction(v,3)if n not in c['fixed_numerals']else v for n,v in values.items()}
   old=execute(p['polynomial_source'],values);new=execute(c['polynomial_source'],values);N=[new[c['unit_interfaces'][name]]for name in UNIT_ORDER];diff=0
   for mon,v in correction['coefficients']:
    for x,e in zip(N,mon):v*=x**e
    diff+=v
   need(new[c['output']]-old[p['output']]==diff,'entire literal SOS correction')
   get=lambda d,n:n if type(n)is int else d[n]
   for mapping in c['parent_comparison_map']:
    i=mapping['parent_index'];a,b=p['comparisons'][i];res=get(old,a)-get(old,b)
    if mapping['role']=='same_residual':
     aa,bb=c['comparisons'][mapping['new_index']];need(res==get(new,aa)-get(new,bb),'all ordinary residuals retained')
    else:need(res==mapping['old_residual_sign']*(new[UNITS[i]]-1),'each exact unit residual sign')
    counts['parent_residual_values']+=1
   counts['all_value_corrections']+=1;counts['signed_cases']+=case<4;counts['rational_cases']+=case in(2,6)
   if case==4:need(evaluate(c,values,root=root)==new[c['output']],'public positive evaluation')
  for field in('source','polynomial_source','partition','unit_groups','parent_comparison_map'):
   q=copy.deepcopy(c);q[field]=tuple(q[field])
   try:checked(q,root=root)
   except ValueError:counts['guards']+=1
   else:raise AssertionError('noncanonical container accepted')
  for field in('operations','M','A'):
   q=copy.deepcopy(c);q['polynomial_ledger'][field]=float(q['polynomial_ledger'][field])
   try:checked(q,root=root)
   except ValueError:counts['guards']+=1
   else:raise AssertionError('noncanonical ledger type accepted')
  forms.append(dict(packet=c,source_proof=proof,complete_correction=correction,degree_certificate=degree))
  counts['forms']+=1;counts['complete_gates']+=c['polynomial_ledger']['operations'];counts['M']+=c['polynomial_ledger']['M'];counts['A']+=c['polynomial_ledger']['A'];counts['certificate_gates']+=c['certificate_ledger']['operations'];counts['comparisons']+=len(c['comparisons'])
 need([counts[k]for k in('complete_gates','M','A','certificate_gates','comparisons')]==[4039,1961,2078,2846,410],'actual aggregate complete-source census')
 counts.update(finite_unit_checks(groups))
 def reject(fn):
  try:fn()
  except(ValueError,TypeError,KeyError):counts['guards']+=1
  else:raise AssertionError('malformed call accepted')
 for partition in allpart:
  if not admissible(partition):reject(lambda partition=partition:build(partition,root=root))
 for g in(True,1,'all',(),[],[[0,1,2,3]],[[0],[1],[2],[3],[4],[4]],[[0],[1],[2],[3],[True]],[[1],[0],[2],[3],[4]],[[0],[3,1],[2,4]]):reject(lambda g=g:build(g,root=root))
 c=build(root=root)
 for field in c:
  q=copy.deepcopy(c);q.pop(field);reject(lambda q=q:checked(q,root=root))
 q=copy.deepcopy(c);q['source'].append(['unused','+',1,0]);reject(lambda:checked(q,root=root))
 q=copy.deepcopy(c);q['polynomial_source'][-1]=[q['output'],'-',0,0];reject(lambda:checked(q,root=root))
 for field in('source','comparisons','witnesses'):
  q=copy.deepcopy(p);q[field]=tuple(q[field]);reject(lambda q=q:rewrite(q,root=root))
 one={n:1 for n in c['polynomial_ledger']['free']}
 for n,v in(('x',0),('a',True),('r',1.0),('eta',-1)):
  values=dict(one);values[n]=v;reject(lambda values=values:evaluate(c,values,root=root))
 reject(lambda:evaluate(c,one,signed=1,root=root));reject(lambda:degree_certificate(dict(c,exact_polynomial_degree=28.0),root=root))
 for field in('source','polynomial_source','partition','unit_groups','parent_comparison_map','historical_provenance'):
  q=build(root=root);q[field].clear();need(exact(build(root=root),c),'defensive packet copies');counts['copies']+=1
 blobs=authenticated(root)
 with tempfile.TemporaryDirectory(prefix='unit_partition109_')as tmp:
  path=Path(tmp)/'papers'/'research-wip'/'native-stream-queue';path.mkdir(parents=True)
  for name,data in blobs.items():
   target=path/name;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
   if '/'in name:(path/Path(name).name).write_bytes(data)
  build(root=path);counts['warm_pin_rejections']=0
  for name,data in blobs.items():
   q=path/name;q.write_bytes(data+b'\n');reject(lambda:build(root=path));q.write_bytes(data);counts['warm_pin_rejections']+=1
  counts['actual_relative_proof_pins_with_valid_fallback']=sum('/'in n for n in blobs)
 proc=subprocess.run([sys.executable,'-O',str(Path(__file__).resolve())],capture_output=True,text=True,timeout=30);need(proc.returncode!=0 and 'run without -O'in proc.stderr,'optimized mode rejected');counts['optimized_mode_rejections']=1
 points=[(f['packet']['polynomial_ledger']['operations'],f['packet']['exact_polynomial_degree'])for f in forms]
 frontier=lambda ps:sorted({p for p in ps if not any(q[0]<=p[0]and q[1]<=p[1]and q!=p for q in ps)})
 family=frontier(points);need(family==[(107,42),(109,28),(111,24)],'exact finite-family frontier')
 optimum=[]
 for point in family:
  matches=[f['packet']['partition']for f in forms if(f['packet']['polynomial_ledger']['operations'],f['packet']['exact_polynomial_degree'])==point]
  optimum.append(dict(operations=point[0],degree=point[1],partitions=matches))
 need([len(x['partitions'])for x in optimum]==[1,1,2],'all frontier schedule multiplicities')
 prior=json.loads(blobs['complete109_index_unit_tradeoffs107.json'])['known_union_frontier'];union=frontier(points+[tuple(x)for x in prior])
 return {'status':'PASS_COMPLETE_PROTECTED_UNIT_PARTITION_FRONTIER109','source_sha256':sha(Path(__file__).read_bytes()),'parent_pins':PINS,'canonical_parent':p,'counts':counts,'all_set_partitions':allpart,'admissible_group_histogram':{str(k):v for k,v in hist.items()},'admissible_partitions':groups,'excluded_criterion_only':[g for g in allpart if not admissible(g)],'forms':forms,'default_partition':DEFAULT,'family_frontier':[list(x)for x in family],'frontier_schedules':optimum,'known_union_frontier':[list(x)for x in union],
  'scope':'All37 partitions of five actual units that separate first/index, exact complete emitted sources and ordinary positive inheritance. Other15 partitions outside criterion, not claimed false. Same entire integer zero tuples; corrections not offzero equality; fixed-parameter exact degrees, no unrestricted lower bound or newly materialized universal zero.'}

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();r=verify(a.root)
 if a.expect:need(exact(r,json.loads(a.expect.read_text())),'typed saved receipt mismatch')
 if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 print(json.dumps({'status':r['status'],'counts':r['counts'],'family_frontier':r['family_frontier'],'known_union_frontier':r['known_union_frontier']},sort_keys=True))
if __name__=='__main__':main()
