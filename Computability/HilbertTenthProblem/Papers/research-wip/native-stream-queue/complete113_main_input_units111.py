#!/usr/bin/env python3
"""One guarded complete degree30 successor to the113-operation degree28 SOS.

Only the default24-witness parent is selected. Both main/input norms are
protected against -1 modulo4, so grouping their unit equations is exact
on the full positive integer zero set. No historical Python module executes.
"""
from __future__ import annotations
import argparse,copy,hashlib,json,random,subprocess,sys,tempfile
from fractions import Fraction
from pathlib import Path
if not __debug__:raise RuntimeError('run without -O')
PINS={
 'complete74_gap_selective_projection113.py':'573f1e8b0c89ef039a2a7fc40bad959cf7e362bcec4c96b3536974e7b71316c4',
 'complete74_gap_selective_projection113.json':'2636f00a9e67f53a144986382442f456427257d498e33960e023e9c986b6b9c3',
 'complete74_gap_selective_projection113.md':'3539d2fa0721eb8448409d075261a6508cc7adc1d887e3905cfeaed737396afa',
 'complete74_factored_first_norm.py':'7c4b10fa78a3fa6517083c41fc6228dd403fec5ac87f2ca6b80b45dd60e8b908',
 'complete74_factored_first_norm.json':'7ebfa54d3846d1c3a6ff7b8e5cd143f3ac80f8299b51698a9f45681d3524eb28',
 'complete74_factored_first_norm.md':'119b51ca9a5d50e0eb998b334af87c1ea3eb0913f956b4f9d7a985f5d1159d9f',
 'complete75_positive_elimination.py':'70123af4f0787b38271f7c4f0fa60e4235cd2f1964ee1b0ad345fe0e3bb82749',
 'complete75_positive_elimination.json':'03743efca27972fd97667501af214626481acb4993ed006b9d4033766c0ec703',
 'complete75_positive_elimination.md':'59cc280280bb8ab74318f648da56aabf31317f42a8a08d01851c5f8db0232d6b',
 'complete75_positive_root89.py':'f850ee8cd5e00b9235a8f192d2f95f6b27cf72a40c3f6b6e3fa054700d793c72',
 'complete75_positive_root89.md':'7b85195a800b909e3bf6e55fa85decfaa08299cf1e100efa866659571d192085',
 'complete86_first_root_partitions.json':'7535a1b2d36f802d6d72bab5c7cfe807c90b802398ed817ea990b76240b7cdc5',
}
SELECTED=['q','C','k','d','kappa','mu']
def need(ok,msg):
 if not ok:raise ValueError(msg)
def sha(b):return hashlib.sha256(b).hexdigest()
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys()and all(exact(a[k],b[k])for k in a)
 if type(a)in(list,tuple):return len(a)==len(b)and all(exact(x,y)for x,y in zip(a,b))
 return a==b

def authenticated(root):
 root=Path(root)if root is not None else Path(__file__).resolve().parent;blobs={}
 for name,pin in PINS.items():
  path=root/name
  if not path.exists():path=Path(__file__).resolve().parent/name
  blobs[name]=path.read_bytes();need(sha(blobs[name])==pin,'parent pin '+name)
 return blobs

def canonical_parent(*,root=None):
 r=json.loads(authenticated(root)['complete74_gap_selective_projection113.json'])
 matches=[f['packet']for f in r['forms']if f['packet']['eliminated']==SELECTED]
 need(len(matches)==1,'unique selected113 parent');p=matches[0]
 need(p['polynomial_ledger']['operations']==113 and p['exact_polynomial_degree']==28 and len(p['witnesses'])==24,'full selected parent')
 return p

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

def _rewrite(p):
 rows=p['source'];nodes={r[0]:r for r in rows}
 need(nodes['R15']==['R15','+','Ac2',1]and nodes['norm_rhs']==['norm_rhs','+','scaled_kappa2',1],'literal private plus-one rows')
 for n in ('R15','norm_rhs'):
  need(not any(n in r[2:]for r in rows),'no source consumer of old side-plus-one')
  need(sum(n in c for c in p['comparisons'])==1,'one old comparison consumer')
 need(nodes['a4']==['a4','*',4,'a']and nodes['a4m5']==['a4m5','+','a4',3]and nodes['a_square']==['a_square','*','a','a']and nodes['A']==['A','+','a_square','a4m5'],'actual protected coefficient')
 need(nodes['L15']==['L15','*','R14','R14']and nodes['Ac2']==['Ac2','*','A','c2']and nodes['c2']==['c2','*','c','c'],'actual main norm')
 need(nodes['mu2']==['mu2','*','exponent_rhs','exponent_rhs']and nodes['scaled_kappa2']==['scaled_kappa2','*','A','kappa2']and nodes['kappa2']==['kappa2','*','index_rhs','index_rhs'],'actual input norm')
 main=p['comparisons'].index(['L15','R15']);inp=p['comparisons'].index(['mu2','norm_rhs']);need((main,inp)==(7,12),'selected norm comparison indices')
 out=[]
 for n,op,a,b in rows:
  if n=='R15':out.append(['main_unit','-','L15','Ac2'])
  elif n=='norm_rhs':out.append(['input_unit','-','mu2','scaled_kappa2'])
  else:out.append([n,op,a,b])
 out.append(['paired_norm_unit','*','main_unit','input_unit'])
 pairs=[];mapping=[]
 for i,pair in enumerate(p['comparisons']):
  if i==inp:mapping.append({'parent_index':i,'child_index':main,'role':'restored_unit_member'});continue
  j=len(pairs);pairs.append(['paired_norm_unit',1]if i==main else copy.deepcopy(pair));mapping.append({'parent_index':i,'child_index':j,'role':'restored_unit_member'if i==main else'same_residual'})
 poly,output=finalizer(out,pairs);free=p['polynomial_ledger']['free'];certificate=inspect(out,free,[v for c in pairs for v in c]);ledger=inspect(poly,free,[output])
 need((certificate['operations'],certificate['M'],certificate['A'])==(76,41,35),'full76 comparison schedule')
 need((ledger['operations'],ledger['M'],ledger['A'])==(111,53,58),'full111 polynomial schedule')
 original=[]
 for item in p['comparison_map']:
  item=copy.deepcopy(item)
  if item['new_index']is not None:
   oldindex=item['new_index'];mapped=mapping[oldindex];item['new_index']=mapped['child_index'];item['role']=mapped['role']
  else:item['role']='historical_deleted_positive_definition'
  original.append(item)
 return {'parameters':copy.deepcopy(p['parameters']),'fixed_numerals':copy.deepcopy(p['fixed_numerals']),'witnesses':copy.deepcopy(p['witnesses']),'domains':p['domains'],
  'source':out,'comparisons':pairs,'polynomial_source':poly,'output':output,'certificate_ledger':certificate,'polynomial_ledger':ledger,
  'exact_polynomial_degree':30,'refined_residual_degree_bounds':[1,5,4,14,5,9,8,15,6,10,2,3],
  'norm_interfaces':{'main':'main_unit','input':'input_unit','product':'paired_norm_unit','coefficient':'A'},
  'parent_comparison_map':mapping,'original_comparison_map':original,
  'same_supplied_coordinates':True,'zero_relation':'same full positive integer zero set as selected113 parent',
  'offzero_identity':'F111-F113=(Nmain-1)*(Ninput-1)*(Nmain*Ninput+Nmain+Ninput-1)',
  'historical_provenance':{'parent_eliminated':p['eliminated'],'parent_restoration_registers':p['restoration_registers'],'parent_first_root_restoration':p['first_root_restoration'],'parent_comparison_map':p['comparison_map'],'parent_exact_degree':28,'parent_polynomial_ledger':p['polynomial_ledger']},
  'scope':'Only the selected24-witness113 source. Fixed admissible ordinary-input program and all native conditions retained; unbounded duration; no broader grouping census.'}

def build(*,root=None):return _rewrite(canonical_parent(root=root))
def rewrite(supplied,*,root=None):
 p=canonical_parent(root=root);need(exact(supplied,p),'complete selected113 parent only');return _rewrite(p)
def checked(packet,*,root=None):
 need(type(packet)is dict,'exact packet');p=build(root=root);need(exact(packet,p),'entire canonical child');return p
def polynomial_source(packet,*,root=None):return checked(packet,root=root)['polynomial_source']
def evaluate(packet,values,*,signed=False,root=None):
 p=checked(packet,root=root);need(type(signed)is bool and type(values)is dict and set(values)==set(p['polynomial_ledger']['free']),'exact full values/mode')
 need(all(type(k)is str and type(v)is int for k,v in values.items()),'exact integer values')
 if not signed:need(all(v>0 for v in values.values()),'strictly positive coordinates/numeral ports')
 return execute(p['polynomial_source'],values)[p['output']]

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

def structural(p,c):
 d=Interner();old=d.run(p['source'],p['polynomial_ledger']['free']);new=d.run(c['source'],c['polynomial_ledger']['free'])
 common=set(old)&set(new)
 need(all(old[n]==new[n]for n in common),'every common pre-finalizer register identical')
 need(new['main_unit']==d.op('-',old['L15'],old['Ac2'])and new['input_unit']==d.op('-',old['mu2'],old['scaled_kappa2']),'literal two norm forms')
 count=0
 for m in c['parent_comparison_map']:
  if m['role']=='same_residual':
   a,b=p['comparisons'][m['parent_index']];aa,bb=c['comparisons'][m['child_index']]
   get=lambda e,v:d.atom(v)if type(v)is int else e[v]
   need(get(old,a)==get(new,aa)and get(old,b)==get(new,bb),'unchanged residual');count+=1
 return {'unchanged_source_registers_and_leaves':len(common),'unchanged_residuals':count,'exact_literal_norms':2,'same_supplied_interface':p['witnesses']==c['witnesses']and p['fixed_numerals']==c['fixed_numerals']}

# Exact bivariate source expansion in scaling t and fixed b=Bm1.
def add(a,b,sign=1):
 c=dict(a)
 for k,v in b.items():c[k]=c.get(k,0)+sign*v
 return{k:v for k,v in c.items()if v}
def mul(a,b):
 c={}
 for(i,j),v in a.items():
  for(k,l),w in b.items():c[i+k,j+l]=c.get((i+k,j+l),0)+v*w
 return{k:v for k,v in c.items()if v}
def polyexecute(rows,values):
 d=dict(values)
 for n,op,a,b in rows:
  a={(0,0):a}if type(a)is int else d[a];b={(0,0):b}if type(b)is int else d[b]
  d[n]=mul(a,b)if op=='*'else add(a,b,1 if op=='+'else-1)
 return d

def _degree(c):
 rows={r[0]:r for r in c['source']}
 # These literal definitions establish the general symbolic highest forms,
 # not merely their t-specializations: d=X+ac+gaH, kappa=u+delta*A,
 # mu=W+a*kappa+rhoH, q=bJ+1, X=wq^3; a,c remain free.
 expected={'repunit':['*','Bm1','Jrep'],'q':['+','repunit',1],'Lbig':['*','q','q'],'n2':['*','Lbig','q'],'wn2':['*','w','n2'],
  'cam2':['*','c','a'],'D1':['+','wn2','cam2'],'gam':['*','ga','a4m5'],'R14':['+','D1','gam'],'odd_index':['+','scaled_t','inner_bits'],
  'scaled_t':['*','twice_cell_bits','x'],'index_product':['*','delta','A'],'index_rhs':['+','odd_index','index_product'],
  'difference_multiple':['*','index_rhs','a'],'exponent_partial':['+','W','difference_multiple'],'modulus_multiple':['*','rho','a4m5'],'exponent_rhs':['+','exponent_partial','modulus_multiple']}
 need(all(rows[n][1:]==v for n,v in expected.items()),'all degree-cone identities')
 values={v:{(1,0):1}for v in c['polynomial_ledger']['free']if v not in c['fixed_numerals']};values['tau_gap']={(1,0):3}
 values.update({v:{(0,0):i+2}for i,v in enumerate(c['fixed_numerals'])});values['Bm1']={(0,1):1}
 env=polyexecute(c['polynomial_source'],values)
 leaders={}
 for n,deg,want in [('main_unit',8,{6:1}),('input_unit',7,{0:-4}),('paired_norm_unit',15,{6:-4}),(c['output'],30,{12:16})]:
  need(max(i for i,j in env[n])==deg,'actual source degree attainment')
  got={j:v for(i,j),v in env[n].items()if i==deg};need(got==want,'uniform Bm1 coefficient expansion');leaders[n]={'degree':deg,'t_leading_polynomial_in_Bm1':[[k,v]for k,v in sorted(got.items())]}
 return {'exact_degree':30,'full_uniform_leader':'16*Bm1^12*w^4*Jrep^12*delta^4*a^10','main_degree':8,'input_degree':7,'group_degree':15,'literal_propagated_upper':c['polynomial_ledger']['literal_degree_upper_bound'],'source_expansion_certificates':leaders,'proof':'Guarded full cones plus main/input norm cancellation; all other residuals degree<=14. Leading coefficient nonzero for every fixed Bm1>0.'}

def degree_certificate(packet,*,root=None):return _degree(checked(packet,root=root))
def correction():
 one={(0,0):1};a={(1,0):1};b={(0,1):1};am1=add(a,one,-1);bm1=add(b,one,-1);abm1=add(mul(a,b),one,-1)
 difference=add(add(mul(abm1,abm1),mul(am1,am1),-1),mul(bm1,bm1),-1)
 factor=mul(mul(am1,bm1),add(add(add(mul(a,b),a),b),one,-1));need(difference==factor,'full residual correction identity')
 return[[list(k),v]for k,v in sorted(difference.items())]

def verify(root):
 p=canonical_parent(root=root);c=build(root=root);proof=structural(p,c);degree=_degree(c);rng=random.Random(11130);counts={'full_corrections':0,'signed_cases':0,'rational_cases':0,'residual_values':0,'guards':0,'copies':0,'public_evaluations':0}
 for i in range(96):
  v={n:rng.randint(-4,5)if i<48 else rng.randint(1,5)for n in c['witnesses']+['x']};v.update(Bm1=15,Kconstant=163,twice_cell_bits=8,inner_bits=3,MC=2,MF=19)
  if i>=80:v={n:Fraction(x,3)if n not in c['fixed_numerals']else x for n,x in v.items()}
  old=execute(p['polynomial_source'],v);new=execute(c['polynomial_source'],v);A=new['main_unit'];B=new['input_unit']
  need(new[c['output']]-old[p['output']]==(A-1)*(B-1)*(A*B+A+B-1),'whole all-value correction')
  need(old['L15']-old['R15']==A-1 and old['mu2']-old['norm_rhs']==B-1,'actual old norm residuals')
  for m in c['parent_comparison_map']:
   if m['role']=='same_residual':
    a,b=p['comparisons'][m['parent_index']];aa,bb=c['comparisons'][m['child_index']];need(old[a]-old[b]==new[aa]-new[bb],'retained residual value');counts['residual_values']+=1
  counts['full_corrections']+=1;counts['signed_cases']+=i<48;counts['rational_cases']+=i>=80
  if i in(0,48):need(evaluate(c,v,signed=i==0,root=root)==new[c['output']],'public whole output');counts['public_evaluations']+=1
 residues=[]
 for a in range(4):
  D=a*a+4*a+3
  for r in range(4):
   for z in range(4):need((r*r-D*z*z)%4!=3,'protected norm cannot be -1');residues.append([a,r,z,(r*r-D*z*z)%4])
 counts['mod4_protected_cases']=len(residues)
 # A scalar negative example shows why the sign exclusion is required.
 need((-1)*(-1)==1 and ((-1)-1)**2+((-1)-1)**2==8,'unprotected negative units would be false zeros')
 bads=[]
 for field in('source','polynomial_source','comparisons','witnesses'):
  q=copy.deepcopy(c);q[field]=tuple(q[field]);bads.append(q)
 for field in('source','polynomial_source'):
  for i,row in enumerate(c[field]):
   for j in(2,3):
    if type(row[j])is int:
     for value in(float(row[j]),bool(row[j])):
      q=copy.deepcopy(c);q[field][i][j]=value;bads.append(q)
 q=copy.deepcopy(c);q['exact_polynomial_degree']=30.0;bads.append(q)
 q=copy.deepcopy(c);q['source'].append(['unused','+',1,0]);bads.append(q)
 q=copy.deepcopy(c);q['original_comparison_map'][17]['new_index']=12;bads.append(q)
 for q in bads:
  try:checked(q,root=root)
  except ValueError:counts['guards']+=1
  else:raise AssertionError('malformed child accepted')
 for field in('source','comparisons','witnesses'):
  q=copy.deepcopy(p);q[field]=tuple(q[field])
  try:rewrite(q,root=root)
  except ValueError:counts['guards']+=1
  else:raise AssertionError('malformed parent accepted')
 one={n:1 for n in c['polynomial_ledger']['free']}
 for key,value in[('x',0),('tau_gap',0),('a',True),('c',1.0),('eta',-1)]:
  v=dict(one);v[key]=value
  try:evaluate(c,v,root=root)
  except ValueError:counts['guards']+=1
  else:raise AssertionError('bad domain accepted')
 try:evaluate(c,one,signed=1,root=root)
 except ValueError:counts['guards']+=1
 else:raise AssertionError('bad signed flag accepted')
 for field in('source','polynomial_source','original_comparison_map','historical_provenance'):
  q=build(root=root);q[field].clear();need(exact(build(root=root),c),'fresh nested copies');counts['copies']+=1
 with tempfile.TemporaryDirectory(prefix='group111_guard_')as tmp:
  dest=Path(tmp);blobs=authenticated(root)
  for name,data in blobs.items():(dest/name).write_bytes(data)
  build(root=dest);counts['warm_pins']=0
  for name,data in blobs.items():
   (dest/name).write_bytes(data+b'\n')
   try:build(root=dest)
   except ValueError:counts['warm_pins']+=1
   else:raise AssertionError('changed source accepted')
   (dest/name).write_bytes(data)
 proc=subprocess.run([sys.executable,'-O',str(Path(__file__).resolve()),'--root',str(root)],capture_output=True,text=True);need(proc.returncode!=0 and 'run without -O'in proc.stderr,'-O rejection');counts['optimized_mode_rejections']=1
 return {'status':'PASS_COMPLETE_MAIN_INPUT_UNITS111','source_sha256':sha(Path(__file__).read_bytes()),'parent_pins':PINS,'counts':counts,'packet':c,'source_proof':proof,'degree_certificate':degree,'symbolic_full_correction':correction(),'mod4_table':residues,'scope':'One complete fixed-program ordinary-input universal source,24 positive witnesses,111 operations,exactdegree30; same full positive integer zero tuples as113 parent.'}

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();r=verify(a.root)
 if a.expect:need(exact(r,json.loads(a.expect.read_text())),'typed receipt mismatch')
 if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 print(json.dumps({'status':r['status'],'counts':r['counts'],'ledger':r['packet']['polynomial_ledger']},sort_keys=True))
if __name__=='__main__':main()
