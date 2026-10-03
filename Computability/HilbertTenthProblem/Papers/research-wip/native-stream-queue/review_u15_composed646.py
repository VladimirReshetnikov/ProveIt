#!/usr/bin/env python3
"""Independent bounded composition review; no repository writes."""
import argparse,copy,hashlib,importlib.util,json,random,sys,types
from pathlib import Path
if not __debug__:raise RuntimeError('Assertions required')
PINS={'u15_packed_two_tape_history.py':'ada8106314bffe545cc106ca66b737d48398d6288f3d86cfaf602e58d0e1c318',
 'u15_packed_state_relabel652.py':'cd3904fb083d1a254461ffde87636a6b9014bcdecb1db48cfcf2f30f41493879',
 'u15_packed_computed_truth647.py':'c363ea0679825559d5247608f748d877e75146dbb997b159db42294d9d676eb7'}
SOURCE_SHA='d2ec28b859b43e93396f66395866b3f18098a959da22c1a5559fc4c1be2cdeb7'
SWAP=(0,9,2,3,4,5,6,7,8,1,10,11,12,13,14)
REMOVED={'native__input_A','native__shared_sum02','native__bs_Q','native__bs_q','native__input_B'}
PAIRS={('native__bs_q','native__q'),('native__input_A','native__padded_A'),('native__input_B','native__padded_B')}
FIELDS=('native__F0','native__F1','native__F2')
def load(path,name):
 s=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m

def expected_transform(p,computed):
 p=copy.deepcopy(p);r=p['registers'];split=next(i for i,z in enumerate(p['source']) if z[0].startswith('native__'))
 row=next(z for z in p['source'] if z[0]==r['scale']);T=row[3] if row[2]==r['B'] else row[2]
 rows=p['source'][:split]+[('tag_twice_T','*',2,T),('tag_A','+',r['Hjoin'],'tag_twice_T'),('tag_M','+',r['Mjoin'],T)]
 remap=lambda x:{r['Hjoin']:'tag_A',r['Mjoin']:'tag_M'}.get(x,x)
 defs=[('native__F1','-','native__padded_A','native__F3'),('native__F2','-','native__padded_B','native__F3'),
 ('computed_q_minus_A','-','native__q','native__padded_A'),('computed_F0_plus_one','-','computed_q_minus_A','native__F2'),('native__F0','-','computed_F0_plus_one',1)]
 for n,op,a,b in p['source'][split:]:
  if not computed or n not in REMOVED:rows.append((n,op,remap(a),remap(b)))
  if computed and n=='native__F3':rows.extend(defs)
 pairs=[z for z in p['comparisons'] if not computed or z not in PAIRS]
 aux=[n for n in p['auxiliaries'] if not computed or n not in FIELDS]
 full=list(rows);squares=[]
 for i,(a,b) in enumerate(pairs):
  rn=f'poly_res{i}';sn=f'poly_sq{i}';full.extend([(rn,'-',a,b),(sn,'*',rn,rn)]);squares.append(sn)
 out=squares[0]
 for i,n in enumerate(squares[1:],1):
  nxt=f'poly_sum{i}';full.append((nxt,'+',out,n));out=nxt
 return dict(source=rows,comparisons=pairs,parameters=p['parameters'],auxiliaries=aux,polynomial_source=full,output=out)

def execute(rows,v):
 env=dict(v)
 for n,op,a,b in rows:
  x=env[a] if type(a) is str else a;y=env[b] if type(b) is str else b
  env[n]=x+y if op=='+' else x-y if op=='-' else x*y
 return env

def at(env,v):return env[v] if type(v) is str else v

def symbolic_compare(old,new):
 intern={}
 def node(key):
  if key not in intern:intern[key]=len(intern)
  return intern[key]
 def run(p):
  e={}
  def get(x):return node(('c',x)) if type(x) is int else e.get(x,node(('v',x)))
  for n,op,a,b in p['source']:
   a,b=get(a),get(b)
   if op in ('+','*'):a,b=sorted((a,b))
   e[n]=node((op,a,b))
  return e,[(get(a),get(b)) for a,b in p['comparisons']]
 oe,oc=run(old);ne,nc=run(new);index=old.get('loader_comparison_count',0)+2
 assert all(a==b for i,(a,b) in enumerate(zip(oc,nc)) if i!=index)
 for key in ('T','A','M','Z','cap'):assert oe[old['tag_registers'][key]]==ne[new['tag_registers'][key]]
 for key in FIELDS:assert oe[key]==ne[key]
 return len(oc)-1,index

def manual(v,rules):
 E=[v[f'edge{i}']-1 for i in range(29)];J=sum(E);D=v['L0']+v['R0']+v['height'];B=64*D;P=(B-1)*J+1
 H,G,U,ZL,ZR,ZU=(v[n] for n in ('H','G','U','ZL','ZR','ZU'))
 Q,S,N,Dir,W=[sum(t[c]*e for t,e in zip(rules,E)) for c in range(5)];WD=sum(t[3]*t[4]*e for t,e in zip(rules,E))
 T=P**34;K=sum(P**i for i in range(29));Ec=sum(e*P**i for i,e in enumerate(E))
 A=H+P*G+P**2*U+P**3*H+P**4*G+P**5*Ec+2*T
 M=(B-1)*Dir*(1+P)+P**2*Dir+(P**3+P**4)*(D-1)*J+P**5*J*K+T
 Z=ZL+P*ZR+P**2*ZU+P**3*H+P**4*G+P**5*Ec;cap=B*T
 out=[2*(H-v['L0']+P*(v['Lfhat']-1))-B*(4*H-3*ZL+2*W-2*WD-ZU),
  2*(G-v['R0']+P*v['Rf'])-B*(G+3*ZR+2*WD+ZU-U),B*N-Q-P,B*U-S-P,H+G+ZL+ZR+ZU+v['bound']-P]
 q=16*cap;F3=16*Z+8;F1=16*(A-Z)+4;F2=16*(M-Z)+2;F0=16*(cap-A-M+Z)-15
 get=lambda n:v['native__'+n]
 r=F0+q*F1+q*q*F2+q*q*q*F3;s=2*get('odd_half')+1;k=get('eta')+get('zeta')
 X=q*(r+get('bound_beta'));Y=s*q;a=Y*(X+1);c=k*Y+get('eta');d=X+a*c+get('ga')*(4*a+3);delta=a*a+4*a+3
 u=get('j')*c-2*r-1;ic22=(get('i')*c*c)**2;y=get('y_aux')
 out += [((X*Y)**2+X)*(Y*k)**2-get('tau')*(get('tau')+1),k-r-1-get('h')*X*Y,d*d-1-delta*c*c,
  ic22-delta*(get('f')**2-1),ic22*(u*u-y*y)-(1-y*y),u+c-get('o')*get('f')]
 return out

def verify(source,root):
 assert hashlib.sha256(source.read_bytes()).hexdigest()==SOURCE_SHA
 for name,sha in PINS.items():assert hashlib.sha256((root/name).read_bytes()).hexdigest()==sha
 sys.path.insert(0,str(root));m=load(source,'review646');base=load(root/'u15_packed_two_tape_history.py','review_base646')
 rel=load(root/'u15_packed_state_relabel652.py','review_rel646');truth=load(root/'u15_packed_computed_truth647.py','review_truth646')
 counts={};inc=lambda key,n=1:counts.__setitem__(key,counts.get(key,0)+n);rng=random.Random(146403)
 rules=tuple((SWAP[q],s,SWAP[n],d,w) for q,s,n,d,w in base.RULES)
 for ordinary in (False,True):
  p=m.build(ordinary,root=root);tag=m.tagged_parent(ordinary,root=root);old=truth.build(ordinary)
  for actual,computed in ((p,True),(tag,False)):
   exp=expected_transform(rel.build(ordinary,root=root),computed)
   for key,value in exp.items():assert truth.exact(actual[key],value),key
   inc('complete_literal_independent_emissions')
  assert p['rules']==rules and p['parameters']==old['parameters'] and p['auxiliaries']==old['auxiliaries']
  count,index=symbolic_compare(old,p);inc('exact_nonstate_residual_DAGs',count);inc('exact_tag_and_truth_DAGs',8)
  names=p['parameters']+p['auxiliaries'];available=set(names);degrees={n:0 if n in p['fixed_parameters'] else 1 for n in names}
  for n,op,a,b in p['polynomial_source']:
   assert n not in available and op in ('+','-','*') and all(type(x) is int or type(x) is str and x in available for x in (a,b))
   da=degrees[a] if type(a) is str else 0;db=degrees[b] if type(b) is str else 0
   degrees[n]=da+db if op=='*' else max(da,db);available.add(n)
  assert degrees[p['output']]==1936
  live={p['output']}
  for n,op,a,b in reversed(p['polynomial_source']):
   if n in live:live.update(x for x in (a,b) if type(x) is str)
  assert all(n in live for n,op,a,b in p['polynomial_source'])
  for kind in ('source','polynomial_source'):
   part='certificate' if kind=='source' else 'polynomial';ops=p[kind];ledger=p['ledger'][part]
   assert ledger=={'operations':len(ops),'M':sum(op=='*' for n,op,a,b in ops),'A':sum(op!='*' for n,op,a,b in ops)}
  inc('source_closure_liveness_degree_ledgers')
  for case in range(40):
   v={n:rng.randrange(1,6) if case<20 else rng.randrange(-3,5) for n in names}
   env=execute(p['polynomial_source'],v);oe=execute(old['polynomial_source'],v)
   raw={n:v[n] for n in m.build(root=root)['auxiliaries']};raw.update(L0=v['program_L'] if ordinary else v['L0'],R0=v['input_R0'] if ordinary else v['R0'])
   rr=manual(raw,rules)
   if ordinary:
    ld=base.loader.build(False);rename=lambda n:{'x':'x','L0':'program_L','R0':'input_R0',**{x:x for x in ('program_L','program_A','program_B','program_D')}}.get(n,'input__'+n)
    lv={n:v[rename(n)] for n in ld['parameters']+ld['auxiliaries']}
    rr=base.loader.bridge.independent(base.loader.bridge.recoder(32),lv)+[base.loader.DENOM*v['input_R0']+v['program_D']-v['program_A']*lv['q']**32-v['program_B']*lv['z']]+rr
   assert rr==[at(env,a)-at(env,b) for a,b in p['comparisons']]
   assert sum(x*x for x in rr)==env[p['output']]==m.evaluate(p,v,signed=True,root=root)
   B=at(oe,old['registers']['B']);P=at(oe,old['registers']['P']);E=lambda i:v[f'edge{i}']-1
   delta=8*(B*(E(0)+E(23)-E(17))-(E(2)+E(3)-E(18))+P);R=at(oe,old['comparisons'][index][0])-at(oe,old['comparisons'][index][1])
   assert env[p['output']]-oe[old['output']]==2*R*delta+delta*delta
   lifted=m.lift_to_tagged_parent(p,v,signed=True,root=root);te=execute(tag['polynomial_source'],lifted)
   assert te[tag['output']]==env[p['output']] and m.project_from_tagged_parent(p,lifted,signed=True,root=root)==v
   assert all(at(te,a)==at(te,b) for a,b in PAIRS)
   inc('complete_manual_residuals',len(rr));inc('complete_SOS_graph_and_correction_cases');inc('signed_cases',case>=20)
  def reject(f):
   try:f()
   except (ValueError,TypeError):inc('malformed_rejected');return
   raise AssertionError('Malformed object accepted')
  one={n:1 for n in names}
  for n in names[:5]+p['auxiliaries'][-5:]:
   for value in (True,1.0,-1):
    bad=dict(one);bad[n]=value;reject(lambda bad=bad:m.evaluate(p,bad,root=root))
  for packet,check in ((p,m.checked),(tag,m.checked_tagged_parent)):
   for field in ('source','comparisons','parameters','auxiliaries','composition_lineage','state_relabel'):
    bad=copy.deepcopy(packet);bad[field]=None;reject(lambda bad=bad,check=check:check(bad,root=root))
   bad=copy.deepcopy(packet);bad['ledger']['positive_witnesses']=float(bad['ledger']['positive_witnesses']);reject(lambda bad=bad,check=check:check(bad,root=root))
   ix=next(i for i,(n,op,a,b) in enumerate(packet['source']) if type(a) is int)
   bad=copy.deepcopy(packet);n,op,a,b=bad['source'][ix];bad['source'][ix]=(n,op,float(a),b);reject(lambda bad=bad,check=check:check(bad,root=root))
  for badflag in (0,1,None,'False'):
   reject(lambda badflag=badflag:m.build(badflag,root=root));reject(lambda badflag=badflag:m.evaluate(p,one,signed=badflag,root=root))
  reject(lambda:m.lift_to_tagged_parent(p,one,root=root))
  lifted=m.lift_to_tagged_parent(p,one,signed=True,root=root);lifted['native__F0']+=1
  reject(lambda:m.project_from_tagged_parent(p,lifted,signed=True,root=root))
  for getter in (m.build,m.tagged_parent):
   wanted=getter(ordinary,root=root);bad=getter(ordinary,root=root);bad['source'].clear();bad['composition_lineage'].clear()
   assert truth.exact(getter(ordinary,root=root),wanted);inc('nested_defensive_copies')
 for L,R in ((6,0),(6,4),(14,0),(22,0)):
  oldv,meta=base.outer_fixture(L,R,100);p=m.build(root=root);v={n:oldv[n] for n in p['parameters']+p['auxiliaries']}
  env=execute(p['source'],v);assert all(at(env,a)==at(env,b) for a,b in p['comparisons'][:5])
  w=m.lift_to_tagged_parent(p,v,root=root);assert min(w[n] for n in FIELDS)>0 and m.project_from_tagged_parent(p,w,root=root)==v
  inc('positive_outer_graph_cases')
 # Cold foreign/no-file siblings must be ignored and restored exactly.
 lname='u15_raw_half_tape_loader';prior=sys.modules.get(lname)
 poisoned=base.loader.build(False);ix=next(i for i,z in enumerate(poisoned['source']) if z[0]=='raw_Q_term');row=list(poisoned['source'][ix]);row[2]='program_B';poisoned['source'][ix]=tuple(row)
 canonical=m.build(True,root=root)
 for foreign in (None,'/foreign/u15_raw_half_tape_loader.py'):
  fake=types.ModuleType(lname)
  if foreign:fake.__file__=foreign
  fake.build=lambda *a,**k:copy.deepcopy(poisoned)
  sys.modules[lname]=fake;m._bundle.cache_clear()
  try:
   assert truth.exact(m.build(True,root=root),canonical) and sys.modules[lname] is fake;inc('cold_loader_isolation_checks')
  finally:
   if prior is None:sys.modules.pop(lname,None)
   else:sys.modules[lname]=prior
   m._bundle.cache_clear()
 return dict(status='PASS',source_sha256=SOURCE_SHA,parent_sha256=PINS,counts=counts,
  raw_ledger=m.build(root=root)['ledger'],ordinary_ledger=m.build(True,root=root)['ledger'],
  scope='Complete literal composition, exact55 unchanged residual DAGs, independent11/46 residuals and full SOS corrections, public guards and positive graph helpers. No full Pell witness materialization;1936 remains an upper bound.')
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--source',type=Path,required=True);ap.add_argument('--root',type=Path,required=True);ap.add_argument('--receipt',type=Path,required=True);a=ap.parse_args();r=verify(a.source.resolve(),a.root.resolve());a.receipt.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
