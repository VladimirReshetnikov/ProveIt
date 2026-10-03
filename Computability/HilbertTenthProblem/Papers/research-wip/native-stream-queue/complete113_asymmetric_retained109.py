#!/usr/bin/env python3
"""Four complete retained-a,c asymmetric positive-integer certificates.

JSON-only parent authentication. No historical Python module is imported.
Finite scope: 113/24,111/24,109/42,109/34, all 24 positive witnesses.
"""
from __future__ import annotations
import argparse,copy,hashlib,json,random,subprocess,sys,tempfile
from fractions import Fraction
from pathlib import Path
if not __debug__:raise RuntimeError('run without -O')
PINS={'complete74_gap_selective_projection113.py': '573f1e8b0c89ef039a2a7fc40bad959cf7e362bcec4c96b3536974e7b71316c4', 'complete74_gap_selective_projection113.json': '2636f00a9e67f53a144986382442f456427257d498e33960e023e9c986b6b9c3', 'complete74_gap_selective_projection113.md': '3539d2fa0721eb8448409d075261a6508cc7adc1d887e3905cfeaed737396afa', 'complete74_factored_first_norm.py': '7c4b10fa78a3fa6517083c41fc6228dd403fec5ac87f2ca6b80b45dd60e8b908', 'complete74_factored_first_norm.json': '7ebfa54d3846d1c3a6ff7b8e5cd143f3ac80f8299b51698a9f45681d3524eb28', 'complete74_factored_first_norm.md': '119b51ca9a5d50e0eb998b334af87c1ea3eb0913f956b4f9d7a985f5d1159d9f', 'complete75_positive_elimination.py': '70123af4f0787b38271f7c4f0fa60e4235cd2f1964ee1b0ad345fe0e3bb82749', 'complete75_positive_elimination.json': '03743efca27972fd97667501af214626481acb4993ed006b9d4033766c0ec703', 'complete75_positive_elimination.md': '59cc280280bb8ab74318f648da56aabf31317f42a8a08d01851c5f8db0232d6b', 'complete75_positive_root89.py': 'f850ee8cd5e00b9235a8f192d2f95f6b27cf72a40c3f6b6e3fa054700d793c72', 'complete75_positive_root89.md': '7b85195a800b909e3bf6e55fa85decfaa08299cf1e100efa866659571d192085', 'complete86_first_root_partitions.json': '7535a1b2d36f802d6d72bab5c7cfe807c90b802398ed817ea990b76240b7cdc5', 'complete113_main_input_units111.py': '152905dd07e507289fe9f321982f5e680ec34b6a3ef23f7205bd370ad6623d16', 'complete113_main_input_units111.json': 'b9702ea066114aec3aef374a480fb2049f47a47d1daf580ea42e595107ebee87', 'complete113_main_input_units111.md': '9f73c0d51f5e1fe9237b0ffc3cbbba49f93b08a0b6242693425f0e086897905f', '../../1980/FIXED_RAW_UNIVERSAL_75_PROOF.md': 'e381124c969087ffa867448177a9df693d81e7bd85dd3a8489d443220fba053d', '../../1980/PELL_RELAXED_AUXILIARY_PROOF.md': '9849260ea2776d26e9b615e0e1ed6fcd9b1c9e0e4cedb6cd8aaa2c0346ecbc90', '../../1980/HALF_PARAMETER_PELL_92_PROOF.md': 'c1132ffe3610ff4132ca0a82312e24774328f4e9b3ed3b6f641055a7f29bfa7b', 'pell_kernel_half_binomial42.md': '0df596859d84aa1cf1d4636457937274e8fdac0c1f8da3196962d911be232992'}
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

VARIANTS=('sos','pair','triple','two_pairs')
SELECTED=['q','C','k','d','kappa','mu']
SPECS={'sos':(113,53,60,13,24),'pair':(111,53,58,12,24),'triple':(109,53,56,11,42),'two_pairs':(109,53,56,11,34)}

def authenticated(root=None):
 root=Path(root)if root is not None else Path(__file__).resolve().parent;blobs={}
 for name,pin in PINS.items():
  paths=[root/name,root/Path(name).name,Path(__file__).resolve().parent/name,Path(__file__).resolve().parent/Path(name).name]
  path=next((p for p in paths if p.exists()),paths[0]);data=path.read_bytes()
  need(sha(data)==pin,'parent pin '+name);blobs[name]=data
 return blobs

def parents(root=None):
 blobs=authenticated(root);r=json.loads(blobs['complete74_gap_selective_projection113.json'])
 ps=[f['packet']for f in r['forms']if f['packet']['eliminated']==SELECTED]
 need(len(ps)==1,'unique selected113');p=ps[0];g=json.loads(blobs['complete113_main_input_units111.json'])['packet']
 need(p['polynomial_ledger']['operations']==113 and g['polynomial_ledger']['operations']==111,'complete parent counts')
 return p,g

def canonical_parent(variant='two_pairs',*,root=None):
 need(type(variant)is str and variant in VARIANTS,'exact variant');p,g=parents(root)
 return p if variant=='sos'else g

def _reference(variant,p,g):
 need(type(variant)is str and variant in VARIANTS,'exact variant')
 base=p if variant=='sos'else g;rows=copy.deepcopy(base['source']);pairs=copy.deepcopy(base['comparisons'])
 by={r[0]:r for r in rows}
 need(by['wn2']==['wn2','*','w','n2'] and by['sn2']==['sn2','*','s','n2'],'actual common q-cube scaling')
 need(sum('w'in r[2:]for r in rows)==1 and all('w'not in c for c in pairs),'w has exactly one source consumer')
 if variant in('triple','two_pairs'):
  need(by['P17']==['P17','-',1,'aux_y2']and not any('P17'in r[2:]for r in rows),'private auxiliary plus-one side')
  need(by['ic2']==['ic2','*','i','c2']and by['ic22']==['ic22','*','ic2','ic2'],'literal square auxiliary coefficient')
  rows=[['aux_unit','+','L17','aux_y2']if r[0]=='P17'else r for r in rows]
  if variant=='triple':
   rows.append(['triple_norm_unit','*','paired_norm_unit','aux_unit'])
   pairs=[['triple_norm_unit',1]if c==['paired_norm_unit',1]else c for c in pairs if c!=['L17','P17']]
  else:
   need(by['R9']==['R9','-',1,'tau_square']and not any('R9'in r[2:]for r in rows),'private first norm side')
   out=[]
   for r in rows:
    if r[0]in('R9','paired_norm_unit'):continue
    out.append(r)
    if r[0]=='L9':out.append(['first_unit','+','tau_square','L9'])
   rows=out+[['first_main_unit','*','first_unit','main_unit'],['input_aux_unit','*','input_unit','aux_unit']]
   pairs=[['first_main_unit',1]if c==['paired_norm_unit',1]else ['input_aux_unit',1]if c==['L17','P17']else c for c in pairs if c!=['R9','L9']]
 poly,out=finalizer(rows,pairs);free=p['polynomial_ledger']['free']
 cert=inspect(rows,free,[v for c in pairs for v in c]);led=inspect(poly,free,[out]);ops,m,a,eq,deg=SPECS[variant]
 need((led['operations'],led['M'],led['A'],len(pairs))==(ops,m,a,eq),'fully paid reference')
 groups={'sos':[],'pair':[[7,12]],'triple':[[7,9,12]],'two_pairs':[[3,7],[9,12]]}[variant]
 mapping=[]
 for old,c in enumerate(p['comparisons']):
  group=next((h for h in groups if old in h),None)
  if group:
   target={'pair':{7:'paired_norm_unit'},'triple':{7:'triple_norm_unit'},'two_pairs':{3:'first_main_unit',9:'input_aux_unit'}}[variant][min(group)]
   new=pairs.index([target,1]);role='unit_group_member'
  else:new=pairs.index(c);role='same_residual'
  mapping.append({'parent113_index':old,'new_index':new,'role':role})
 original=[]
 for r in p['comparison_map']:
  r=copy.deepcopy(r)
  if r['new_index']is None:r['role']='historical_positive_definition'
  else:r.update(new_index=mapping[r['new_index']]['new_index'],role=mapping[r['new_index']]['role'])
  original.append(r)
 return {'variant':variant,'parameters':copy.deepcopy(p['parameters']),'fixed_numerals':copy.deepcopy(p['fixed_numerals']),'witnesses':copy.deepcopy(p['witnesses']),
  'source':rows,'comparisons':pairs,'polynomial_source':poly,'output':out,'certificate_ledger':cert,'polynomial_ledger':led,
  'parent113_comparison_map':mapping,'original_raw_comparison_map':original,'scale':'X=w*q^3; Y=s*q^3',
  'exact_polynomial_degree':{'sos':28,'pair':30,'triple':50,'two_pairs':44}[variant],
  'same_positive_zero_tuples_as_symmetric113':True,'all_integer_zero_equivalence':True,
  'scope':'Fully emitted symmetric reference; protected grouping separate from the asymmetric coordinate transfer.'}

def symmetric_reference(variant='two_pairs',*,root=None):return _reference(variant,*parents(root))

def _build(variant,p,g):
 ref=_reference(variant,p,g);c=copy.deepcopy(ref)
 c['source']=[['wn2','*','w','q']if r[0]=='wn2'else r for r in c['source']]
 c['polynomial_source'],c['output']=finalizer(c['source'],c['comparisons'])
 free=p['polynomial_ledger']['free'];c['certificate_ledger']=inspect(c['source'],free,[v for pair in c['comparisons']for v in pair]);c['polynomial_ledger']=inspect(c['polynomial_source'],free,[c['output']])
 c['scale']='X=w*q; Y=s*q^3';c['exact_polynomial_degree']=SPECS[variant][4]
 del c['same_positive_zero_tuples_as_symmetric113'];del c['all_integer_zero_equivalence']
 c.update(domains=p['domains'],coordinate_relation={'forward':'w_new=q^2*w_old','inverse_on_positive_zeros':'w_old=w_new/q^2','q':'Bm1*Jrep+1','all_other_fields':'unchanged'},
  zero_relation='Complete positive integer zero bijection with symmetric reference, then with selected113 parent; unit grouping itself preserves all integer zeros; asymmetric restoration uses positivity.',
  offzero_relation='Exact full polynomial equality after w_new=q^2*w_old; rational inverse when q!=0. Not equality at the same coordinates.',
  active_interfaces={'X':'wn2','Y':'sn2','E':'UM','k':'R10b','L':'first_root_base','a':'a','c':'c','Delta':'A','main_root':'R14','input_root':'exponent_rhs','ordinary_strong':['ic22','R16']},
  historical_parent={'selected_positive_definitions':p['eliminated'],'restoration_registers':p['restoration_registers'],'first_root_restoration':p['first_root_restoration'],'symmetric_reference_degree':ref['exact_polynomial_degree']},
  scope='Exactly four complete fixed admissible program forms; ordinary input x>0,24 positive witnesses,unbounded duration. Full ordinary strong auxiliary and input equations retained. No wider grouping census or unrestricted real/signed zero theorem.')
 return c

def build(variant='two_pairs',*,root=None):return _build(variant,*parents(root))
def checked(packet,*,root=None):
 need(type(packet)is dict,'exact packet');variant=packet.get('variant');p=build(variant,root=root);need(exact(packet,p),'entire canonical child');return p

def rewrite(parent,variant='two_pairs',*,root=None):
 p,g=parents(root);need(type(variant)is str and variant in VARIANTS,'exact variant');need(exact(parent,p if variant=='sos'else g),'entire selected frozen parent');return _build(variant,p,g)

def polynomial_source(packet,*,root=None):return checked(packet,root=root)['polynomial_source']
def _values(p,values,signed):
 need(type(signed)is bool and type(values)is dict and set(values)==set(p['polynomial_ledger']['free']),'complete values and exact mode')
 need(all(type(k)is str and type(v)is int for k,v in values.items()),'exact integers')
 if not signed:need(all(v>0 for v in values.values()),'strict positive coordinates and numeral ports')
 return dict(values)

def evaluate(packet,values,*,signed=False,root=None):
 p=checked(packet,root=root);v=_values(p,values,signed);return execute(p['polynomial_source'],v)[p['output']]

def forward_assignment(packet,values,*,root=None):
 p=checked(packet,root=root);v=_values(p,values,False);q=v['Bm1']*v['Jrep']+1;v['w']*=q*q;return v

def restore_assignment(packet,values,*,root=None):
 p=checked(packet,root=root);v=_values(p,values,False);q=v['Bm1']*v['Jrep']+1
 need(v['w']%(q*q)==0,'inverse requires integral positive w/q^2; proven on canonical positive zeros');v['w']//=q*q;return v

# Independent small exact sparse-polynomial engine. All leaves, including fixed
# program coefficients, remain formal variables; only the degree weights differ.
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

def degree_proof(c):
 free=c['polynomial_ledger']['free'];d,const=expanded(c['source'],free);weights=[int(v not in c['fixed_numerals'])for v in free]
 deg=lambda p:max((sum(x*w for x,w in zip(m,weights))for m in p),default=-1)
 top=lambda p:{m:v for m,v in p.items()if sum(x*w for x,w in zip(m,weights))==deg(p)}
 v=d;one=const(1);M=lambda *ps:__import__('functools').reduce(pmul,ps,one);power=lambda p,n:ppow(p,n,one)
 k=padd(v['eta'],v['zeta']);gpart=padd(pmul(const(2),v['tau_gap']),k,-1)
 Ltop=M(power(v['Bm1'],7),v['w'],power(v['s'],2),k,power(v['Jrep'],7))
 first=padd(v['tau_square'],v['L9']);main=padd(v['L15'],v['Ac2'],-1);inp=padd(v['mu2'],v['scaled_kappa2'],-1);aux=padd(v['L17'],v['aux_y2'])
 Dtop=padd(M(v['Bm1'],v['w'],v['Jrep']),M(const(4),v['ga'],v['a']))
 Mtop=padd(power(Dtop,2),M(const(2),v['a'],v['c'],Dtop));Itop=M(const(-4),power(v['delta'],2),power(v['a'],5));Atop=M(power(v['i'],2),power(v['j'],2),power(v['c'],6))
 for actual,expected,num in[(first,M(Ltop,gpart),12),(main,Mtop,4),(inp,Itop,7),(aux,Atop,10)]:need(deg(actual)==num and top(actual)==expected,'full symbolic norm leader')
 rs=[]
 for a,b in c['comparisons']:rs.append(padd(const(a)if type(a)is int else d[a],const(b)if type(b)is int else d[b],-1))
 degrees=[deg(r)for r in rs];D=max(degrees);leaders=[i for i,n in enumerate(degrees)if n==D];need(len(leaders)==1,'unique highest-degree residual')
 lead=power(top(rs[leaders[0]]),2)
 expected={'sos':power(M(Ltop,gpart),2),'pair':power(M(Ltop,gpart),2),'triple':power(M(Mtop,Itop,Atop),2),'two_pairs':power(M(Itop,Atop),2)}[c['variant']]
 need(lead==expected and 2*D==c['exact_polynomial_degree'],'complete uniform exact degree')
 encode=lambda p:[[list(m),v]for m,v in sorted(p.items())]
 return {'exact_degree':2*D,'residual_exact_degrees':degrees,'unique_leading_residual':leaders[0],'variables':free,'degree_weights':weights,'full_leading_homogeneous_polynomial':encode(lead),'norm_degrees':[12,4,7,10],
  'fixed_parameter_dependencies':sorted({free[j]for m in lead for j,e in enumerate(m)if e and not weights[j]}),
  'uniformity':'The displayed exact multivariate leader is nonzero for every admissible fixed Bm1>0; all other fixed numerals are absent. No finite specialization is used as a uniform proof.',
  'literal_degree_upper_bound':c['polynomial_ledger']['literal_degree_upper_bound']}

def degree_certificate(packet,*,root=None):return degree_proof(checked(packet,root=root))

def reference_degree_proof(ref):
 free=ref['polynomial_ledger']['free'];d,co=expanded(ref['source'],free);w=[int(n not in ref['fixed_numerals'])for n in free]
 degree=lambda p:max((sum(x*y for x,y in zip(m,w))for m in p),default=-1)
 residuals=[padd(co(a)if type(a)is int else d[a],co(b)if type(b)is int else d[b],-1)for a,b in ref['comparisons']]
 ds=[degree(p)for p in residuals];need(2*max(ds)==ref['exact_polynomial_degree'],'actual complete symmetric reference degree')
 indexes=[i for i,n in enumerate(ds)if n==max(ds)];need(len(indexes)==1,'unique symmetric reference leader')
 top={m:v for m,v in residuals[indexes[0]].items()if sum(x*y for x,y in zip(m,w))==max(ds)}
 # Every fixed-dependent leading monomial has the same Bm1 exponent, so
 # specializing any positive Bm1 preserves the nonzero formal coefficient.
 fixed=[i for i,n in enumerate(free)if n in ref['fixed_numerals']]
 powers={tuple(m[i]for i in fixed)for m in top};need(len(powers)==1,'uniform fixed monomial in symmetric reference leader')
 return {'exact_degree':2*max(ds),'residual_exact_degrees':ds,'unique_leading_residual':indexes[0],'leader_terms':len(top),'fixed_numeral_order':[free[i]for i in fixed],'fixed_exponents_in_free_order':[list(t)for t in sorted(powers)]}

def structural(ref,c):
 a={r[0]:r for r in ref['source']};b={r[0]:r for r in c['source']};need(set(a)==set(b),'same registers')
 need(a['wn2']==['wn2','*','w','n2']and b['wn2']==['wn2','*','w','q'],'literal changed scale')
 need(all(a[n]==b[n]for n in a if n!='wn2'),'only one source row changes')
 # Exact polynomial identity in w,q before using the common X cut.
 v,k=expanded([],['w','q']);q=v['q'];w=v['w'];need(pmul(pmul(w,pmul(q,q)),q)==pmul(w,pmul(pmul(q,q),q)),'paid scale identity')
 I=Interner();free=c['polynomial_ledger']['free']
 def run(rows):
  d={n:I.atom(n)for n in free}
  for n,op,a,b in rows:
   d[n]=I.atom('proven_common_X')if n=='wn2'else I.op(op,I.atom(a)if type(a)is int else d[a],I.atom(b)if type(b)is int else d[b])
  return d
 old=run(ref['polynomial_source']);new=run(c['polynomial_source']);need(all(old[n]==new[n]for n in old if n!='w'),'complete graph identity after proven cut')
 need(exact(ref['comparisons'],c['comparisons']),'all comparison pairs preserved')
 return {'changed_certificate_rows':1,'computed_gate_identities_after_scale_cut':len(c['polynomial_source']),'unchanged_supplied_leaves':len(free)-1,'comparison_identities':len(c['comparisons']),'whole_finalizer_identity':True,'w_private_consumer':'wn2'}

def group_proof(p,ref):
 I=Interner();a=I.run(p['source'],p['polynomial_ledger']['free']);b=I.run(ref['source'],ref['polynomial_ledger']['free']);common=set(a)&set(b)
 need(all(a[n]==b[n]for n in common),'all common grouped-source expressions identical')
 val=lambda d,x:I.atom(x)if type(x)is int else d[x]
 kept=0
 for m in ref['parent113_comparison_map']:
  if m['role']=='same_residual':
   old=p['comparisons'][m['parent113_index']];new=ref['comparisons'][m['new_index']]
   need(all(val(a,x)==val(b,y)for x,y in zip(old,new)),'exact retained grouped comparison');kept+=1
 # Full SOS difference as a polynomial in the four literal units.
 d,co=expanded([],['N0','Nm','Ni','Na']);one=co(1);square=lambda p:pmul(p,p)
 units=list(d.values());base={}
 for n in units:base=padd(base,square(padd(n,one,-1)))
 variant=ref['variant']
 groups={'sos':[[0],[1],[2],[3]],'pair':[[0],[1,2],[3]],'triple':[[0],[1,2,3]],'two_pairs':[[0,1],[2,3]]}[variant]
 changed={}
 for group in groups:
  prod=one
  for i in group:prod=pmul(prod,units[i])
  changed=padd(changed,square(padd(prod,one,-1)))
 correction=padd(changed,base,-1)
 need('first_unit'not in b or b['first_unit']==I.op('+',a['tau_square'],a['L9']),'literal first unit')
 need('main_unit'not in b or b['main_unit']==I.op('-',a['L15'],a['Ac2']),'literal main unit')
 need('input_unit'not in b or b['input_unit']==I.op('-',a['mu2'],a['scaled_kappa2']),'literal input unit')
 need('aux_unit'not in b or b['aux_unit']==I.op('+',a['L17'],a['aux_y2']),'literal aux unit')
 return {'common_register_identities':len(common),'retained_comparison_identities':kept,'unit_order':['N0','Nm','Ni','Na'],'groups':groups,'full_sos_difference_coefficients':[[list(m),v]for m,v in sorted(correction.items())],
  'zero_scope':'all integer tuples','first_residual_orientation':'parent first residual is 1-N0; its square is unchanged by sign'}

def component_checks():
 counts={'raw_packing_cases':0,'shifted_boundary_cases':0,'protected_mod4_cases':0,'first_negative_norm_descent_identities':0,'nearest_multiple_cases':0,'lower_power_bounds':0,'dyadic_divisibility_bounds':0}
 for B in(16,32):
  for J in range(1,5):
   q=(B-1)*J+1
   for MC in range(2,B-1,4):
    for MF in range(4,B-1,8):
     Tp=MC*J+1+q*(MF*J-1);need(3*q+1<=Tp<q*q-1,'raw mask window')
     for F in(1,q//2,q,q+1):
      for Z in(1,2,q-1):
       Sp=Z+q*F-1;R=(q*q-Sp)*(q*q-1)+Tp
       direct=(q*q-Z-q*F)*(q*q-1)+(MC+q*(MF+B-1))*J
       need(R==direct,'literal shifted packing')
       if R>0:need(Sp<=q*q and 3*q+1<=R<q**4,'untyped R bounds')
       if Sp==q*q:need(R==Tp,'G=-1 boundary retained');counts['shifted_boundary_cases']+=1
       counts['raw_packing_cases']+=1
 for a in range(4):
  D=a*a+4*a+3
  for u in range(4):
   for v in range(4):need((u*u-D*v*v)%4!=3,'Delta norm sign');counts['protected_mod4_cases']+=1
 for t in range(4):
  for H in range(4):
   for y in range(4):need((t*t*(H*H-y*y)+y*y)%4!=3,'square-coefficient auxiliary norm sign');counts['protected_mod4_cases']+=1
 # Symbolic Lorentz transformation preserving T^2-V(V+1)k^2.
 p,co=expanded([],['V','T','k']);V,T,k=p.values();D=pmul(V,padd(V,co(1)));P=padd(pmul(co(2),V),co(1));Tp=padd(pmul(P,T),pmul(co(2),pmul(D,k)),-1);kp=padd(pmul(P,k),pmul(co(2),T),-1)
 need(padd(pmul(Tp,Tp),pmul(D,pmul(kp,kp)),-1)==padd(pmul(T,T),pmul(D,pmul(k,k)),-1),'exact first-negative-norm descent identity');counts['first_negative_norm_descent_identities']=1
 # Finite checks illustrate, but do not prove, the stated general step-down.
 def pell(A,n):
  x,y=1,0
  for _ in range(n):x,y=A*x+(A*A-1)*y,x+A*y
  return x,y
 for A in range(3,7):
  for pidx in range(1,5):
   for m in range(2*pidx+1,2*pidx+5):
    f=pell(A,m)[0];target=pell(A,2*pidx)[0]
    for ell in range(1,4*m+1):
     if (pell(A,2*ell)[0]-target)%f==0:need(ell%m in(pidx%m,(-pidx)%m),'finite strict step-down')
     counts['nearest_multiple_cases']+=1
 for X in(16,17,32,64):
  for r in range(1,31):need(X**r>6 and X**(r+1)>6*4**r,'strict lower ratio final margins');counts['lower_power_bounds']+=1
 for t in range(4,65):
  q=2**t;need(3*q+1>3*t,'q-cube valuation threshold');counts['dyadic_divisibility_bounds']+=1
 return counts

def verify(root=None):
 p,g=parents(root);rng=random.Random(1092434);forms=[];counts={'whole_coordinate_identities':0,'signed_coordinate_cases':0,'rational_inverse_cases':0,'whole_group_corrections':0,'individual_residual_maps':0,'public_coordinate_roundtrips':0,'guards':0,'copies':0}
 for variant in VARIANTS:
  c=_build(variant,p,g);ref=_reference(variant,p,g);proof=structural(ref,c);group=group_proof(p,ref);degree=degree_proof(c)
  for i in range(48):
   vals={v:rng.randint(-3,5)if i<24 else rng.randint(1,4)for v in c['polynomial_ledger']['free']}
   vals.update(Bm1=15,Kconstant=163,twice_cell_bits=8,inner_bits=3,MC=2,MF=19)
   q=vals['Bm1']*vals['Jrep']+1;newvals=dict(vals);newvals['w']*=q*q
   old=execute(ref['polynomial_source'],vals);new=execute(c['polynomial_source'],newvals)
   need(old[ref['output']]==new[c['output']],'whole polynomial coordinate identity')
   for name in old:
    if name!='w':need(old[name]==new[name],'every corresponding computed register')
   counts['whole_coordinate_identities']+=1;counts['signed_coordinate_cases']+=i<24
   if i>=40:
    vv=dict(vals);vv['w']=Fraction(vv['w'],q*q);rational=execute(ref['polynomial_source'],vv);direct=execute(c['polynomial_source'],vals)
    need(rational[ref['output']]==direct[c['output']],'rational inverse whole polynomial');counts['rational_inverse_cases']+=1
   # Unit correction from complete symmetric113; algebra is valid over integers
   # and rationals even where the positive-zero equivalence is not asserted.
   base=execute(p['polynomial_source'],vals)
   N=[base['tau_square']+base['L9'],base['L15']-base['Ac2'],base['mu2']-base['scaled_kappa2'],base['L17']+base['aux_y2']]
   difference=0
   for mon,coeff in group['full_sos_difference_coefficients']:
    term=coeff
    for x,e in zip(N,mon):term*=x**e
    difference+=term
   need(old[ref['output']]-base[p['output']]==difference,'complete grouping SOS correction');counts['whole_group_corrections']+=1
   for m in c['parent113_comparison_map']:
    if m['role']=='same_residual':
     a,b=p['comparisons'][m['parent113_index']];aa,bb=ref['comparisons'][m['new_index']]
     get=lambda env,z:z if type(z)is int else env[z]
     need(get(base,a)-get(base,b)==get(old,aa)-get(old,bb),'every unchanged residual');counts['individual_residual_maps']+=1
   if i in(24,25):
    fwd=forward_assignment(c,vals,root=root);back=restore_assignment(c,fwd,root=root);need(exact(vals,back)and exact(newvals,fwd),'public graph inverse')
    need(evaluate(c,fwd,root=root)==old[ref['output']],'public positive evaluation');counts['public_coordinate_roundtrips']+=1
  # Full canonical malformed packet tests, including numeric aliases and map drift.
  bad=[]
  for field in('source','polynomial_source','comparisons','witnesses'):
   v=copy.deepcopy(c);v[field]=tuple(v[field]);bad.append(v)
  for field in('source','polynomial_source'):
   for i,row in enumerate(c[field]):
    for j in(2,3):
     if type(row[j])is int:
      for x in(float(row[j]),bool(row[j])):
       v=copy.deepcopy(c);v[field][i][j]=x;bad.append(v)
  for field in('exact_polynomial_degree',):
   v=copy.deepcopy(c);v[field]=float(v[field]);bad.append(v)
  v=copy.deepcopy(c);v['source'][8][3]='n2';bad.append(v)
  v=copy.deepcopy(c);v['parent113_comparison_map'][0]['new_index']=True;bad.append(v)
  v=copy.deepcopy(c);v['source'].append(['dead','+',1,0]);bad.append(v)
  for v in bad:
   try:checked(v,root=root)
   except ValueError:counts['guards']+=1
   else:raise AssertionError('malformed packet accepted')
  par=p if variant=='sos'else g
  for field in('source','comparisons','witnesses'):
   v=copy.deepcopy(par);v[field]=tuple(v[field])
   try:rewrite(v,variant,root=root)
   except ValueError:counts['guards']+=1
   else:raise AssertionError('malformed parent accepted')
  one={v:1 for v in c['polynomial_ledger']['free']}
  for key,value in[('w',0),('a',True),('c',1.0),('eta',-1)]:
   v=dict(one);v[key]=value
   try:evaluate(c,v,root=root)
   except ValueError:counts['guards']+=1
   else:raise AssertionError('invalid domain accepted')
  for call in(lambda:restore_assignment(c,one,root=root),lambda:evaluate(c,one,signed=1,root=root),lambda:degree_certificate(bad[-1],root=root)):
   try:call()
   except ValueError:counts['guards']+=1
   else:raise AssertionError('invalid graph/degree request accepted')
  for field in('source','polynomial_source','parent113_comparison_map','historical_parent'):
   v=build(variant,root=root);v[field].clear();need(exact(build(variant,root=root),c),'defensive complete copies');counts['copies']+=1
  forms.append({'packet':c,'symmetric_reference':ref,'graph_source_proof':proof,'grouping_source_proof':group,'degree_certificate':degree,'symmetric_reference_degree_certificate':reference_degree_proof(ref)})
 component=component_checks()
 counts.update(component)
 for v in(None,True,1,'unknown'):
  try:build(v,root=root)
  except ValueError:counts['guards']+=1
  else:raise AssertionError('invalid variant accepted')
 with tempfile.TemporaryDirectory(prefix='asym_retained_')as tmp:
  dst=Path(tmp);blobs=authenticated(root)
  for name,data in blobs.items():(dst/Path(name).name).write_bytes(data)
  build(root=dst);counts['warm_pin_rejections']=0
  for name,data in blobs.items():
   path=dst/Path(name).name;path.write_bytes(data+b'\n')
   try:build(root=dst)
   except ValueError:counts['warm_pin_rejections']+=1
   else:raise AssertionError('changed inherited bytes accepted')
   path.write_bytes(data)
 proc=subprocess.run([sys.executable,'-O',str(Path(__file__).resolve()),'--root',str(root)],capture_output=True,text=True)
 need(proc.returncode!=0 and 'run without -O'in proc.stderr,'-O module rejection');counts['optimized_mode_rejections']=1
 points=[(f['packet']['polynomial_ledger']['operations'],f['packet']['exact_polynomial_degree'])for f in forms]
 local=sorted({p for p in points if not any(q[0]<=p[0]and q[1]<=p[1]and q!=p for q in points)})
 old=json.loads(authenticated(root)['complete86_first_root_partitions.json'])
 # Authenticate the earlier frontier byte source; state the known explicit union.
 previous=[(r['operations'],r['exact_degree'])for r in old['census']['combined_frontier']]+[(p['polynomial_ledger']['operations'],p['exact_polynomial_degree']),(g['polynomial_ledger']['operations'],g['exact_polynomial_degree'])]
 allpoints=previous+points;union=sorted({p for p in allpoints if not any(q[0]<=p[0]and q[1]<=p[1]and q!=p for q in allpoints)})
 return {'status':'PASS_COMPLETE_ASYMMETRIC_RETAINED109','source_sha256':sha(Path(__file__).read_bytes()),'parent_pins':PINS,'counts':counts,'forms':forms,
  'family_frontier':[list(p)for p in local],'known_union_frontier':[list(p)for p in union],
  'frontier_scope':'Operation/degree projection only; older86..98 points have19 witnesses, these four forms24. No exhaustive search beyond these four complete sources.',
  'proof_scope':'Symbolic circuit identities and exact degrees are verified; general Pell/rank/step-down and positive-coordinate restoration proofs are in the companion note with authenticated references. Finite component fixtures are not universal-zero witnesses.'}

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();r=verify(a.root)
 if a.expect:need(exact(r,json.loads(a.expect.read_text())),'typed saved receipt mismatch')
 if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 print(json.dumps({'status':r['status'],'counts':r['counts'],'family_frontier':r['family_frontier']},sort_keys=True))
if __name__=='__main__':main()
