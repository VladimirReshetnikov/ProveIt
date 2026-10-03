#!/usr/bin/env python3
"""Independent complete-source, norm-unit, degree and guarded API review."""
import argparse,ast,copy,hashlib,json,random,subprocess,sys,tempfile,types
from collections import Counter
from fractions import Fraction
from pathlib import Path
if not __debug__:raise RuntimeError('Run without -O')
PINS={'source':'152905dd07e507289fe9f321982f5e680ec34b6a3ef23f7205bd370ad6623d16','receipt':'b9702ea066114aec3aef374a480fb2049f47a47d1daf580ea42e595107ebee87','note':'9f73c0d51f5e1fe9237b0ffc3cbbba49f93b08a0b6242693425f0e086897905f'}
PARENT={'complete74_gap_selective_projection113.py':'573f1e8b0c89ef039a2a7fc40bad959cf7e362bcec4c96b3536974e7b71316c4','complete74_gap_selective_projection113.json':'2636f00a9e67f53a144986382442f456427257d498e33960e023e9c986b6b9c3','complete74_gap_selective_projection113.md':'3539d2fa0721eb8448409d075261a6508cc7adc1d887e3905cfeaed737396afa'}
FIXED=['Bm1','Kconstant','twice_cell_bits','inner_bits','MC','MF']
def sha(b):return hashlib.sha256(b).hexdigest()
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if type(a)in (list,tuple):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b

def add(a,b,s=1):
 c=dict(a)
 for m,v in b.items():c[m]=c.get(m,0)+s*v
 return {m:v for m,v in c.items() if v}
def mul(a,b):
 c={}
 for m,v in a.items():
  for n,w in b.items():
   z=tuple(sorted(m+n));c[z]=c.get(z,0)+v*w
 return {m:v for m,v in c.items() if v}
def constant(v):return {():v} if v else {}
def variable(v):return {(v,):1}
def top(p):
 d=max((sum(v not in FIXED for v in m) for m in p),default=0)
 return d,{m:c for m,c in p.items() if sum(v not in FIXED for v in m)==d}
def serial(p):return [[list(m),v] for m,v in sorted(p.items())]
def cone(rows,free,name):
 by={n:(op,a,b) for n,op,a,b in rows};memo={v:variable(v) for v in free}
 def walk(v):
  if type(v)is int:return constant(v)
  if v not in memo:
   op,a,b=by[v];a,b=walk(a),walk(b)
   memo[v]=mul(a,b) if op=='*' else add(a,b,1 if op=='+' else -1)
  return memo[v]
 return walk(name)
def execute(rows,values):
 d=dict(values)
 for n,op,a,b in rows:
  a=a if type(a)is int else d[a];b=b if type(b)is int else d[b]
  d[n]=a*b if op=='*' else a+b if op=='+' else a-b
 return d

def ledger(rows,free,roots):
 d={v:0 if v in FIXED else 1 for v in free};deps={};M=0
 for n,op,a,b in rows:
  assert type(n)is str and n not in d and op in ('+','-','*')
  assert all(type(v)is int or type(v)is str and v in d for v in (a,b))
  aa=0 if type(a)is int else d[a];bb=0 if type(b)is int else d[b]
  d[n]=aa+bb if op=='*' else max(aa,bb);deps[n]=(a,b);M+=op=='*'
 todo=list(roots);live=set()
 while todo:
  n=todo.pop()
  if type(n)is str and n not in live:live.add(n);todo.extend(deps.get(n,()))
 assert set(deps)|set(free)<=live
 return {'operations':len(rows),'M':M,'A':len(rows)-M,'all_gates_live':True,'free':sorted(free),'literal_degree_upper_bound':max(0 if type(v)is int else d[v] for v in roots)},d

def finalize(rows,pairs):
 out=copy.deepcopy(rows)
 for i,(a,b) in enumerate(pairs):out.extend([[f'residual_{i}','-',a,b],[f'square_{i}','*',f'residual_{i}',f'residual_{i}']])
 output='square_0'
 for i in range(1,len(pairs)):
  out.append([f'sum_{i}','+',output,f'square_{i}']);output=f'sum_{i}'
 return out,output

class DAG:
 def __init__(self):self.nodes={}
 def node(self,key):
  if key not in self.nodes:self.nodes[key]=len(self.nodes)
  return self.nodes[key]
 def atom(self,v):return self.node((type(v).__name__,v))
 def op(self,op,a,b):return self.node((op,a,b))
 def run(self,rows,free):
  d={v:self.atom(v) for v in free}
  for n,op,a,b in rows:d[n]=self.op(op,self.atom(a) if type(a)is int else d[a],self.atom(b) if type(b)is int else d[b])
  return d

def run(source,receipt,note,root):
 for key,path in [('source',source),('receipt',receipt),('note',note)]:assert sha(path.read_bytes())==PINS[key]
 for name,pin in PARENT.items():assert sha((root/name).read_bytes())==pin
 tree=ast.parse(source.read_bytes());pins=next(ast.literal_eval(n.value) for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='PINS' for t in n.targets))
 assert len(pins)==12 and all(pins[n]==v for n,v in PARENT.items())
 for name,pin in pins.items():assert sha((root/name).read_bytes())==pin
 r=json.loads(receipt.read_text());assert r['source_sha256']==PINS['source'];c=r['packet']
 pr=json.loads((root/'complete74_gap_selective_projection113.json').read_text())
 p=next(f['packet'] for f in pr['forms'] if f['packet']['eliminated']==['q','C','k','d','kappa','mu'])
 count=Counter();free=p['polynomial_ledger']['free']
 assert c['parameters']==p['parameters']==['x'] and c['witnesses']==p['witnesses'] and len(c['witnesses'])==24
 assert c['fixed_numerals']==p['fixed_numerals']==FIXED and c['domains']==p['domains']
 oldnodes={row[0]:row for row in p['source']}
 for n in ('R15','norm_rhs'):
  assert not any(n in row[2:] for row in p['source'])
  assert sum(n in pair for pair in p['comparisons'])==1
 assert oldnodes['R15']==['R15','+','Ac2',1] and oldnodes['norm_rhs']==['norm_rhs','+','scaled_kappa2',1]
 rows=[]
 for row in p['source']:
  rows.append(['main_unit','-','L15','Ac2'] if row[0]=='R15' else ['input_unit','-','mu2','scaled_kappa2'] if row[0]=='norm_rhs' else row)
 rows.append(['paired_norm_unit','*','main_unit','input_unit'])
 pairs=[['paired_norm_unit',1] if i==7 else pair for i,pair in enumerate(p['comparisons']) if i!=12]
 assert exact(rows,c['source']) and exact(pairs,c['comparisons'])
 pol,output=finalize(rows,pairs);assert exact(pol,c['polynomial_source']) and output==c['output']
 assert finalize(p['source'],p['comparisons'])==(p['polynomial_source'],p['output'])
 cert,degrees=ledger(rows,free,[v for pair in pairs for v in pair]);full,_=ledger(pol,free,[output])
 assert cert==c['certificate_ledger'] and full==c['polynomial_ledger']
 assert (cert['operations'],cert['M'],cert['A'])==(76,41,35) and (full['operations'],full['M'],full['A'])==(111,53,58)
 assert len(pairs)==12 and full['operations']==len(rows)+3*len(pairs)-1
 count['complete_source_and_finalizer_reconstructions']=2;count['recounted_live_child_gates']=111
 dag=DAG();old=dag.run(p['source'],free);new=dag.run(rows,free)
 for n in old.keys()&new.keys():assert old[n]==new[n];count['unchanged_expression_registers_and_leaves']+=1
 for i,pair in enumerate(p['comparisons']):
  if i in (7,12):continue
  aa,bb=pairs[i];a,b=pair
  assert dag.op('-',old[a],old[b])==dag.op('-',new[aa],new[bb]);count['exact_retained_residuals']+=1
 # Expand actual cones, including computed Delta and graph-defined roots.
 main=cone(rows,free,'main_unit');inp=cone(rows,free,'input_unit')
 D=cone(rows,free,'A');a=variable('a');H=add(mul(constant(4),a),constant(3))
 assert D==add(mul(a,a),H)
 k=cone(rows,free,'index_rhs');v=add(variable('W'),mul(variable('rho'),H))
 input_expansion=add(add(mul(v,v),mul(constant(2),mul(mul(a,k),v))),mul(H,mul(k,k)),-1)
 assert inp==input_expansion;count['exact_input_norm_cancellation']=1
 md,ml=top(main);nd,nl=top(inp)
 wantmain={tuple(sorted(['Bm1']*6+['w']*2+['Jrep']*6)):1}
 wantinput={tuple(sorted(['delta']*2+['a']*5)):-4}
 assert (md,nd)==(8,7) and ml==wantmain and nl==wantinput
 group=mul(ml,nl);leader=mul(group,group)
 assert leader=={tuple(sorted(['Bm1']*12+['w']*4+['Jrep']*12+['delta']*4+['a']*10)):16}
 residual_bounds=[]
 for i,(x,y) in enumerate(pairs):
  bound=15 if i==7 else max(0 if type(z)is int else degrees[z] for z in (x,y))
  residual_bounds.append(bound)
 assert residual_bounds==[1,5,4,14,5,9,8,15,6,10,2,3]==c['refined_residual_degree_bounds']
 assert max(residual_bounds)==15 and residual_bounds.count(15)==1 and c['exact_polynomial_degree']==30
 # Exact full finalizer correction in the two independent norm symbols.
 A=variable('Nmain');B=variable('Ninput');one=constant(1)
 am=add(A,one,-1);bm=add(B,one,-1);abm=add(mul(A,B),one,-1)
 correction=add(add(mul(abm,abm),mul(am,am),-1),mul(bm,bm),-1)
 factored=mul(mul(am,bm),add(add(add(mul(A,B),A),B),one,-1))
 assert correction==factored;count['symbolic_complete_offzero_corrections']=1
 # All residues suffice for the universal integer obstruction to norm=-1.
 mod4=[]
 for a0 in range(4):
  for root0 in range(4):
   for ord0 in range(4):
    delta=(a0*a0+4*a0+3)%4;val=(root0*root0-delta*ord0*ord0)%4
    assert delta in (0,3) and val!=3;mod4.append([a0,root0,ord0,val])
 count['complete_mod4_cases']=len(mod4)
 rng=random.Random(111113)
 for i in range(40):
  values={v:rng.randint(-3,4) if i<24 else rng.randint(1,4) for v in free}
  if i>=32:values={v:Fraction(x,3) for v,x in values.items()};count['rational_cases']+=1
  o=execute(p['polynomial_source'],values);n=execute(pol,values);nm=n['main_unit'];ni=n['input_unit']
  assert n[output]-o[p['output']]==(nm-1)*(ni-1)*(nm*ni+nm+ni-1)
  get=lambda v:v if type(v)is int else n[v]
  assert n[output]==sum((get(a)-get(b))**2 for a,b in pairs)
  assert o['L15']-o['R15']==nm-1 and o['mu2']-o['norm_rhs']==ni-1
  count['full_numeric_correction_and_SOS_cases']+=1;count['signed_cases']+=i<24
 m=types.ModuleType('_authenticated_main_input111');m.__file__=str(source);exec(compile(source.read_bytes(),str(source),'exec'),m.__dict__)
 assert exact(m.build(root=root),c) and exact(m.canonical_parent(root=root),p)
 assert exact(m.rewrite(p,root=root),c) and m.degree_certificate(c,root=root)['exact_degree']==30
 def rejects(fn):
  try:fn()
  except (ValueError,TypeError):count['guard_rejections']+=1
  else:raise AssertionError('malformed value accepted')
 for fn in (m.checked,m.polynomial_source,m.degree_certificate):
  for field in ('source','comparisons','witnesses','polynomial_source'):
   bad=copy.deepcopy(c);bad[field]=tuple(bad[field]);rejects(lambda:fn(bad,root=root))
  for field,val in [('exact_polynomial_degree',30.0),('same_supplied_coordinates',1),('offzero_identity','same polynomial')]:
   bad=copy.deepcopy(c);bad[field]=val;rejects(lambda:fn(bad,root=root))
 for val in (1.0,True):
  bad=copy.deepcopy(c);bad['comparisons'][7][1]=val;rejects(lambda:m.checked(bad,root=root))
  bad=copy.deepcopy(p);bad['source'][5][3]=val;rejects(lambda:m.rewrite(bad,root=root))
 values={v:1 for v in free}
 for key,val in [('x',0),('a',True),('delta',1.0),('Bm1',0),('tau_gap',-1)]:
  bad=dict(values);bad[key]=val;rejects(lambda:m.evaluate(c,bad,root=root))
 rejects(lambda:m.evaluate(c,values,signed=1,root=root))
 for field in ('source','comparisons','historical_provenance','parent_comparison_map'):
  z=m.build(root=root);z[field].clear();assert exact(m.build(root=root),c);count['defensive_child_copies']+=1
 z=m.canonical_parent(root=root);z['source'].clear();assert exact(m.canonical_parent(root=root),p);count['defensive_parent_copies']+=1
 with tempfile.TemporaryDirectory() as temp:
  tr=Path(temp)
  for name in pins:(tr/name).write_bytes((root/name).read_bytes())
  m.build(root=tr)
  for name in pins:
   original=(tr/name).read_bytes();(tr/name).write_bytes(original+b'\n')
   try:m.build(root=tr)
   except ValueError:count['warm_parent_pin_rejections']+=1
   else:raise AssertionError('changed pin accepted')
   (tr/name).write_bytes(original)
 opt=subprocess.run([sys.executable,'-O',str(source),'--root',str(root)],capture_output=True,text=True,timeout=30)
 assert opt.returncode!=0 and 'run without -O' in opt.stderr;count['optimized_mode_rejections']=1
 return {'status':'PASS_INDEPENDENT_COMPLETE111_REVIEW','review_source_sha256':sha(Path(__file__).read_bytes()),'pins':PINS,'authenticated_parent_pins':pins,'counts':dict(count),'certificate_ledger':cert,'polynomial_ledger':full,'degree_proof':{'main_degree':md,'main_full_leader':serial(ml),'input_degree':nd,'input_full_leader':serial(nl),'full_exact_degree':30,'full_unique_leader':serial(leader),'refined_residual_bounds':residual_bounds,'all_fixed_Bm1_positive':True},'whole_offzero_correction':serial(correction),'mod4_exhaustion':mod4,'scope':'One canonical113 parent. Complete integer zero sets identical; same positive witnesses and admissible ordinary-input program theorem. Algebraic correction holds over every commutative ring; no claim of real zero-set equality or unrestricted optimality.'}

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 for n in ('source','receipt','note','root'):ap.add_argument('--'+n,type=Path,required=True)
 ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();r=run(a.source,a.receipt,a.note,a.root)
 if a.expect:assert exact(r,json.loads(a.expect.read_text()))
 if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 print(json.dumps({'status':r['status'],'counts':r['counts']}))
if __name__=='__main__':main()
