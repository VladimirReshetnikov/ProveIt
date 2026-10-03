#!/usr/bin/env python3
"""Independent literal-table, complete-source and API review of U15 consumed505."""
if not __debug__:raise RuntimeError('Run the authenticated historical chain without -O')
import argparse,ast,copy,hashlib,json,random,shutil,subprocess,sys,tempfile,types
from collections import Counter
from fractions import Fraction
from pathlib import Path
PIN='a8716b7ca82f703944993a247da89fa2a9a70ccfb5db11521161014edc4a3533'
RECEIPT_PIN='6376193a420efc81cffbd7becd51d7b2f84d4d44fa3706e5996e06920e06bca5'
PARENT='u15_packed_loader_offset506.py'
PARENT_PIN='b8c2af63e5b102685944e5e18e31f037a257df2abb0fcbf8efbf0824a1685a9a'
PARENT_RECEIPT='u15_packed_loader_offset506.json'
PARENT_RECEIPT_PIN='8337d0ec9ddf7d5857e1d64bf33798e7ae149494346855120e7c8346b129800e'
BASELINE='u15_packed_two_tape_history.py'
BASELINE_PIN='ada8106314bffe545cc106ca66b737d48398d6288f3d86cfaf602e58d0e1c318'
NESTED='u15_packed_cross_projection507.py'
NESTED_PIN='dc89cc030610a719b6f270ddfe9dbc5b75b1d7675bb9d13a223db160b23469a4'
TABLE='0RB1RA_1RC1RA_0LG0LE_0LF1LE_1RA1LD_1LD1LD_0LH1LG_1LI1LG_0RA1LJ_1LK---_0RL1RN_0RM1RL_0LB1RL_0LC0RO_0RN1RN'
PERM=[0,9,2,3,4,5,6,7,8,1,10,11,12,13,14]
PORTS=('binary75','binary76','binary77','binary79','cross_write_only','v131','v140','v156','binary89')
EXPECTED={'base:0:0':(320,116,204,51,11,1936),'base:0:1':(318,116,202,51,10,3464),
 'base:1:0':(517,209,308,87,31,1936),'base:1:1':(505,209,296,87,25,4881),
 'frontier:0':(505,209,296,87,25,4881),'frontier:1':(507,209,298,87,26,3120),
 'frontier:2':(509,209,300,87,27,2116),'frontier:3':(511,209,302,87,28,1936)}
def need(v,s):
 if not v:raise ValueError(s)
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if type(a)in(list,tuple):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b
def norm(x):return json.loads(json.dumps(x))
def pin(p,h):need(p.is_file() and hashlib.sha256(p.read_bytes()).hexdigest()==h,'Pin mismatch '+p.name)
def locate(source,root,name):return source.parent/name if (source.parent/name).is_file() else root/name
def load(p):
 m=types.ModuleType('_independent_consumed505');m.__file__=str(p)
 exec(compile(p.read_bytes(),str(p),'exec'),m.__dict__);return m
def execute(rows,values):
 e=dict(values)
 for n,o,a,b in rows:
  a=e[a] if type(a)is str else a;b=e[b] if type(b)is str else b;e[n]=a*b if o=='*' else a+b if o=='+' else a-b
 return e
def at(e,n):return e[n] if type(n)is str else n
def rule_vectors(p):
 # Parse the literal original 15x2 table independently, then apply the sole
 # recorded bijective renaming. In particular the rule order is not sorted.
 rules=[]
 for q,row in enumerate(TABLE.split('_')):
  for s in (0,1):
   word=row[3*s:3*s+3]
   if word=='---':continue
   rules.append([PERM[q],s,PERM[ord(word[2])-65],int(word[1]=='L'),int(word[0])])
 need(p['rules']==rules and p['table']==TABLE and p['state_relabel']==PERM and p['state_center']==7,'Literal machine or center differs')
 selectors=[[int(i==j) for i in range(29)]+[0] for j in range(29)]
 def vector(col,offset):return [col(r) for r in rules]+[offset]
 want={
 'binary75':vector(lambda r:1,-29),'binary76':vector(lambda r:r[1],-14),'binary77':vector(lambda r:r[3],-15),
 'binary79':vector(lambda r:r[3]*r[4],-9),'cross_write_only':vector(lambda r:(1-r[3])*r[4],-8),
 'v131':vector(lambda r:2*r[3]*r[4],-18),'v140':vector(lambda r:2*(1-r[3])*r[4],-16),
 'v156':vector(lambda r:r[0]-7,1),'binary89':vector(lambda r:r[2]-7,17)}
 need(sum(r[1] for r in rules)==14 and sum(r[3] for r in rules)==15,'Read/direction count')
 need(sum(r[3]*r[4] for r in rules)==9 and sum((1-r[3])*r[4] for r in rules)==8,'Write partition count')
 # Source/source-code sum offsets: centered Q +7 is +1 after shifting all hats.
 need(sum(r[0]-7 for r in rules)==6 and sum(r[2]-7 for r in rules)==-17,'State offsets')
 rows={n:(o,a,b) for n,o,a,b in p['source']};env={'edge'+str(i):v for i,v in enumerate(selectors)};used=set()
 def get(v):
  if type(v)is int:return [0]*29+[v]
  if v in env:return env[v]
  need(v in rows,'Affine proof escapes source');used.add(v);o,a,b=rows[v];a=get(a);b=get(b)
  if o=='*':
   need(not any(a[:-1]) or not any(b[:-1]),'Nonlinear affine gate')
   z=[a[-1]*x for x in b] if not any(a[:-1]) else [b[-1]*x for x in a]
  else:z=[x+y if o=='+' else x-y for x,y in zip(a,b)]
  env[v]=z;return z
 for n in PORTS:need(get(n)==want[n],'Literal rule vector mismatch '+n)
 return want,used

def proof(old,new):
 va,ca=rule_vectors(old);vb,cb=rule_vectors(new);need(va==vb,'Independent affine vectors disagree')
 need(len(ca)==91 and len(cb)==90,'Actual transitive closure size')
 for p,closure in ((old,ca),(new,cb)):
  rows=[r for r in p['source'] if r[0] in closure]
  need(sum(o=='*' for n,o,a,b in rows)==6,'Actual closure multiplication count')
  for n,o,a,b in p['polynomial_source']:
   if n not in closure:need(all(type(x)is int or x not in closure or x in PORTS for x in (a,b)),'Private affine value escapes')
 nodes={}
 def intern(v):
  if v not in nodes:nodes[v]=len(nodes)
  return nodes[v]
 def signatures(p):
  e={n:intern(('coordinate',n)) for n in p['parameters']+p['auxiliaries']}
  def get(n):return e[n] if type(n)is str else intern(('integer',n))
  for n,o,a,b in p['polynomial_source']:
   e[n]=intern(('proved_affine_port',n)) if n in PORTS else intern((o,get(a),get(b)))
  return e,get
 a,aa=signatures(old);b,bb=signatures(new)
 need(old['comparisons']==new['comparisons'],'Changed comparison list')
 for x,y in old['comparisons']:need(aa(x)==bb(x) and aa(y)==bb(y),'Changed residual operand')
 need(a[old['output']]==b[new['output']],'Changed full output')
 for field in ('registers','tag_registers','computed_loader_fields'):
  need(old.get(field)==new.get(field),'Changed export metadata')
  for n in new.get(field,{}).values():need(aa(n)==bb(n),'Changed exported semantic value '+n)
 for f in old.get('unit_factors',[]):need(aa(f['factor'])==bb(f['factor']),'Changed protected/checksum factor')
 tail=old['polynomial_source'][len(old['source']):]
 need(tail==new['polynomial_source'][len(new['source']):],'Changed literal finalizer')
 # Every retained source row is literally preserved in order; no hidden
 # downstream rewrite is obscured by the expression-DAG equivalence.
 need([r for r in old['source'] if r[0] not in ca]==[r for r in new['source'] if r[0] not in cb],'Changed retained source rows')
 return {'rule_vectors':va,'old_closure_gates':91,'new_closure_gates':90,'closure_multiplications':6,
  'comparison_identities':len(old['comparisons']),'unit_factor_identities':len(old.get('unit_factors',[])),
  'exact_whole_polynomial_identity':True,'literal_finalizer_gates':len(tail),'expression_nodes':len(nodes)}

def source_audit(p):
 known=set(p['parameters']+p['auxiliaries']);need(len(known)==len(p['parameters'])+len(p['auxiliaries']),'Duplicate coordinates')
 deg={n:0 if n in p['fixed_parameters'] else 1 for n in known}
 for n,o,a,b in p['polynomial_source']:
  need(type(n)is str and n not in known and o in ('+','-','*'),'Duplicate/invalid source gate')
  need(all(type(x)is int or type(x)is str and x in known for x in (a,b)),'Unbound/noninteger operand')
  da=deg[a] if type(a)is str else 0;db=deg[b] if type(b)is str else 0;deg[n]=da+db if o=='*' else max(da,db);known.add(n)
 live={p['output']}
 for n,o,a,b in reversed(p['polynomial_source']):
  need(n in live,'Dead paid gate');live.update(x for x in (a,b) if type(x)is str)
 need(p['polynomial_source'][:len(p['source'])]==p['source'],'Certificate prefix changed')
 for field,ledger in (('source','certificate'),('polynomial_source','polynomial')):
  rows=p[field];m=sum(o=='*' for n,o,a,b in rows)
  need(p['ledger'][ledger]==dict(operations=len(rows),M=m,A=len(rows)-m),'Incorrect actual ledger')
 need(p['ledger']['formal_degree_upper_bound']==deg[p['output']],'Incorrect formal degree')
 need(all(n in live for field in ('registers','tag_registers','computed_loader_fields') for n in p.get(field,{}).values()),'Inactive semantic alias')
 return deg[p['output']]

def manual_finalizer(p,e):
 rs=[at(e,a)-at(e,b) for a,b in p['comparisons']]
 if p['cross_parent_form'] in ('base:1:1','frontier:0'):
  need(p['comparisons'][-1][1]==1,'Anchor factor comparison')
  return (rs[-1]+1)*(1+sum(x*x for x in rs[:-1]))-1
 return sum(x*x for x in rs)

def run(source,root):
 pin(source,PIN);pin(source.with_suffix('.json'),RECEIPT_PIN)
 baseline=root/BASELINE;pin(baseline,BASELINE_PIN)
 table=[ast.literal_eval(n.value) for n in ast.parse(baseline.read_bytes()).body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='TABLE' for t in n.targets)]
 need(table==[TABLE],'Authenticated original literal U15 table differs')
 parent_path=locate(source,root,PARENT);pin(parent_path,PARENT_PIN)
 oldpath=locate(source,root,PARENT_RECEIPT);pin(oldpath,PARENT_RECEIPT_PIN)
 old={f['form']:f['compiler'] for f in json.loads(oldpath.read_text())['forms']}
 saved={f['form']:f['compiler'] for f in json.loads(source.with_suffix('.json').read_text())['forms']}
 m=load(source);counts=Counter();records=[];rng=random.Random(5051821)
 def reject(fn):
  try:fn()
  except (ValueError,TypeError,KeyError):counts['malformed_rejected']+=1;return
  raise ValueError('Invalid public call accepted')
 for key,expected in EXPECTED.items():
  def build():
   if key.startswith('base:'):
    _,o,g=key.split(':');return m.build(bool(int(o)),grouped=bool(int(g)),root=root)
   return m.build_frontier(int(key.split(':')[1]),root=root)
  p=build();q=old[key];pp=norm(p)
  need(exact(pp,saved[key]),'Fresh source differs from frozen receipt')
  need(exact(norm(m.canonical_parent(p,root=root)),q),'Actual parent differs from independently authenticated receipt')
  pr=proof(q,pp);formal=source_audit(pp)
  counts['literal_rule_vector_identities']+=len(PORTS);counts['full_DAG_identities']+=1
  counts['residual_identities']+=len(p['comparisons']);counts['native_factor_identities']+=len(p.get('unit_factors',[]))
  counts['all_live_gates']+=len(p['polynomial_source'])
  for f in ('parameters','auxiliaries','fixed_parameters','rules','comparisons','output','unit_factors','unit_retained_comparison_map','unit_group_factors','unit_groups','group_anchor','graph_ancestor','removed_comparisons','tagged_ports','computed_loader_field_formulas','ancestor_comparison_map'):
   need(q.get(f)==pp.get(f),'Changed interface/theorem field '+f)
  for part in ('certificate','polynomial'):
   need(q['ledger'][part]['operations']==pp['ledger'][part]['operations']+1 and q['ledger'][part]['A']==pp['ledger'][part]['A']+1 and q['ledger'][part]['M']==pp['ledger'][part]['M'],'Not a fully paid one-addition saving')
  got=(len(p['polynomial_source']),p['ledger']['polynomial']['M'],p['ledger']['polynomial']['A'],len(p['auxiliaries']),len(p['comparisons']),p['exact_degree_certificate']['exact_degree'])
  need(got==expected,'Complete frontier mismatch')
  need(pp['exact_degree_certificate']['parent_certificate']==q['exact_degree_certificate'],'Degree certificate not inherited exactly')
  need(pp['exact_degree_certificate']['exact_degree']==q['exact_degree_certificate']['exact_degree'],'Changed exact degree')
  for field in ('positive_witnesses','equations'):need(pp['ledger'][field]==q['ledger'][field],'Changed coordinate/equation count')
  archived=('loader_offset_rewrite','cross_projection','canonical_parent','ancestor_canonical_parent')
  need(pp['parent_transform_provenance']=={k:q[k] for k in archived if k in q},'Historical provenance incorrect')
  need(all(k not in pp for k in archived if k!='canonical_parent'),'Stale top-level transform assertion')
  need(pp['canonical_parent']==dict(file=PARENT,sha256=PARENT_PIN,form=key),'Current parent metadata')
  for j in range(10):
   signed=j>=5;v={n:rng.randrange(-3,4) if signed else rng.randrange(1,5) for n in p['parameters']+p['auxiliaries']}
   if not p['ordinary'] and not signed:v.update(L0=j%2,R0=(j//2)%2)
   a,b=execute(q['polynomial_source'],v),execute(pp['polynomial_source'],v)
   rr=[at(a,x)-at(a,y) for x,y in q['comparisons']];ss=[at(b,x)-at(b,y) for x,y in pp['comparisons']]
   need(rr==ss and a[q['output']]==b[pp['output']],'Full numeric identity')
   need(manual_finalizer(pp,b)==b[pp['output']],'Manual complete finalizer mismatch')
   need(m.evaluate(p,v,signed=signed,root=root)==b[pp['output']],'Public evaluator mismatch')
   ident=m.identity(p,v,signed=signed,root=root);need(ident==dict(output=b[pp['output']],residuals=ss),'Public identity mismatch')
   counts['complete_integer_evaluations']+=1;counts['signed_integer_evaluations']+=signed;counts['numeric_residual_identities']+=len(ss)
  for j in range(2):
   v={n:Fraction(rng.randrange(-2,3),rng.randrange(1,3)) for n in p['parameters']+p['auxiliaries']}
   a,b=execute(q['polynomial_source'],v),execute(pp['polynomial_source'],v)
   need(a[q['output']]==b[pp['output']]==manual_finalizer(pp,b),'Full rational/finalizer identity');counts['rational_evaluations']+=1
  v={n:1 for n in p['parameters']+p['auxiliaries']}
  for n in list(v)[::13]:
   for bad in (True,1.0,None,0,-1):
    if type(bad)is int and bad==0 and not p['ordinary'] and n in ('L0','R0'):continue
    vv=dict(v);vv[n]=bad;reject(lambda vv=vv:m.evaluate(p,vv,root=root))
  for field in ('source','polynomial_source','ledger','consumed_affine_rewrite','exact_degree_certificate','parent_transform_provenance','canonical_parent','cross_parent_form'):
   bad=copy.deepcopy(p);bad[field]=None;reject(lambda bad=bad:m.checked(bad,root=root))
  for badflag in (0,1,None):reject(lambda badflag=badflag:m.identity(p,v,signed=badflag,root=root))
  for value in (1.0,True):
   bad=copy.deepcopy(p);bad['ledger']['polynomial']['A']=value;reject(lambda bad=bad:m.checked(bad,root=root))
  row_index=next(i for i,r in enumerate(p['source']) if any(type(x)is int for x in r[2:]))
  for conversion in (float,lambda x:bool(x),lambda x:x+1):
   bad=copy.deepcopy(p);row=list(bad['source'][row_index]);index=next(i for i in (2,3) if type(row[i])is int);row[index]=conversion(row[index]);bad['source'][row_index]=tuple(row);reject(lambda bad=bad:m.checked(bad,root=root))
  bad=copy.deepcopy(p);bad['source']=tuple(bad['source']);reject(lambda:m.checked(bad,root=root))
  for vv in (dict(v,unexpected=1),{n:x for n,x in v.items() if n!=next(iter(v))}):reject(lambda vv=vv:m.evaluate(p,vv,root=root))
  for getter in (build,lambda:m.canonical_parent(p,root=root),lambda:m.polynomial_source(p,root=root),m.replacement):
   x=getter();before=copy.deepcopy(x)
   if type(x)is dict:x['source'].clear()
   else:x.clear()
   need(exact(getter(),before),'Public cache copy escaped');counts['defensive_copy_checks']+=1
  if not p['ordinary']:m.identity(p,dict(v,L0=0,R0=0),root=root);counts['raw_zero_tape_cases']+=1
  records.append(dict(form=key,independent_proof=pr,ledger=p['ledger'],exact_degree=expected[-1],syntactic_degree=formal))
 for bad in (0,1,None,0.0,'yes'):
  reject(lambda bad=bad:m.build(bad,root=root));reject(lambda bad=bad:m.build(grouped=bad,root=root))
 for bad in (True,False,-1,4,0.0,None):reject(lambda bad=bad:m.build_frontier(bad,root=root))
 with tempfile.TemporaryDirectory(prefix='independent-consumed505-warm-') as d:
  d=Path(d);shutil.copyfile(source,d/source.name);shutil.copyfile(parent_path,d/PARENT)
  nested=locate(parent_path,root,NESTED);pin(nested,NESTED_PIN);shutil.copyfile(nested,d/NESTED)
  warm=load(d/source.name);original=warm.build(root=root)
  for name in (PARENT,NESTED):
   path=d/name;data=path.read_bytes()
   try:path.write_bytes(data+b'\n# private warm guard perturbation\n');reject(lambda:warm.build(root=root));counts['warm_source_pin_rejections']+=1
   finally:path.write_bytes(data)
   need(exact(warm.build(root=root),original),'Warm restoration changed canonical packet')
 optimized=subprocess.run([sys.executable,'-O',str(source),'--root',str(root)],capture_output=True,text=True,timeout=15)
 need(optimized.returncode!=0 and 'normal Python' in optimized.stderr,'Optimized mode not rejected');counts['optimized_execution_rejection']+=1
 return dict(status='PASS',source_sha256=PIN,receipt_sha256=RECEIPT_PIN,parent_source_sha256=PARENT_PIN,parent_receipt_sha256=PARENT_RECEIPT_PIN,
  baseline_source_sha256=BASELINE_PIN,counts=dict(counts),forms=records,scope='Independent literal U15 table parsing and exact affine vectors, complete all-value DAG/finalizer equality for eight schedules, ledger/liveness, canonical metadata and API guards. Exact degree and computational domain transfer through the proved identical polynomial; no universal witness construction, search optimality or all-partition rerun claimed.')

if __name__=='__main__':
 ap=argparse.ArgumentParser(description=__doc__)
 for arg in ('source','root'):ap.add_argument('--'+arg,type=Path,required=True)
 ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();result=run(a.source.resolve(),a.root.resolve())
 if a.expect:need(exact(result,json.loads(a.expect.read_text())),'Independent saved receipt mismatch')
 if a.output:a.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
 print(json.dumps({'status':result['status'],'counts':result['counts']},indent=2))
