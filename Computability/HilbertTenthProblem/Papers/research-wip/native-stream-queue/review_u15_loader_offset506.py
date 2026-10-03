#!/usr/bin/env python3
"""Independent bounded all-source review of the frozen U15 loader-offset rewrite."""
if not __debug__:raise RuntimeError('Run this review without -O')
import argparse,copy,hashlib,json,random,shutil,subprocess,tempfile,types
from collections import Counter
from fractions import Fraction
from pathlib import Path
PIN='b8c2af63e5b102685944e5e18e31f037a257df2abb0fcbf8efbf0824a1685a9a'
PARENT='u15_packed_cross_projection507.py'
PARENT_PIN='dc89cc030610a719b6f270ddfe9dbc5b75b1d7675bb9d13a223db160b23469a4'
RECEIPT='u15_packed_cross_projection507.json'
RECEIPT_PIN='9d4cdfb040c756c3d7f11b15cf0a9ad42b8e7dd2571053fa1f5cc1196723332b'
NESTED='u15_packed_composed_units511.py'
NESTED_PIN='234a2fcd12e9049ae8903cb44a5c545a61857eba71e4484a0cf3c572827cfc38'
ATOM='input__congruence_right0';CUT='input__and__F3';REMOVED='input__restored_Ahat';CHANGED='input__and__scaled_Z'
EXPECTED={'base:0:0':(321,116,205,51,11,1936),'base:0:1':(319,116,203,51,10,3464),
 'base:1:0':(518,209,309,87,31,1936),'base:1:1':(506,209,297,87,25,4881),
 'frontier:0':(506,209,297,87,25,4881),'frontier:1':(508,209,299,87,26,3120),
 'frontier:2':(510,209,301,87,27,2116),'frontier:3':(512,209,303,87,28,1936)}
def need(v,s):
 if not v:raise ValueError(s)
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if type(a)in(list,tuple):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b
def normalized(x):return json.loads(json.dumps(x))
def pin(p,h):need(p.is_file() and hashlib.sha256(p.read_bytes()).hexdigest()==h,'Source/receipt mismatch '+p.name)
def load(p):
 m=types.ModuleType('_independent_u15_loader_offset');m.__file__=str(p)
 exec(compile(p.read_bytes(),str(p),'exec'),m.__dict__);return m

def execute(rows,values):
 e=dict(values)
 for n,o,a,b in rows:
  a=e[a] if type(a)is str else a;b=e[b] if type(b)is str else b
  e[n]=a*b if o=='*' else a+b if o=='+' else a-b
 return e
def at(e,v):return e[v] if type(v)is str else v

def local(rows):
 # Independent exact univariate expansion in the already emitted u register.
 table={n:(o,a,b) for n,o,a,b in rows};env={ATOM:{1:1}}
 def value(v):
  if type(v)is int:return {0:v} if v else {}
  if v in env:return env[v]
  need(v in table,'Unbound local proof atom');o,a,b=table[v];a=value(a);b=value(b);c=Counter()
  if o=='*':
   for i,x in a.items():
    for j,y in b.items():c[i+j]+=x*y
  else:
   c.update(a)
   for i,y in b.items():c[i]+=y if o=='+' else -y
  env[v]={i:x for i,x in c.items() if x};return env[v]
 return value(CUT)

def proof(old,new):
 ordinary=new['ordinary'];need(old['ordinary']==ordinary,'Domain changed');cuts={CUT} if ordinary else set()
 if ordinary:
  need(local(old['source'])==local(new['source'])=={1:16,0:8},'Exact local polynomial')
  oldmap={n:(o,a,b) for n,o,a,b in old['source']};newmap={n:(o,a,b) for n,o,a,b in new['source']}
  need(oldmap[REMOVED]==('+',ATOM,1) and oldmap[CHANGED]==('*',16,REMOVED) and oldmap[CUT]==('-',CHANGED,8),'Actual three parent rows')
  need(newmap[CHANGED]==('*',16,ATOM) and newmap[CUT]==('+',CHANGED,8),'Actual two child rows')
  need(set(oldmap)-set(newmap)=={REMOVED} and not set(newmap)-set(oldmap),'Exactly one gate deleted')
  for v,want in ((REMOVED,[CHANGED]),(CHANGED,[CUT])):
   uses=[n for n,o,a,b in old['polynomial_source'] for x in (a,b) if x==v];need(uses==want,'Unexpected actual consumer')
  need(old['computed_loader_fields']['input__Ahat']==REMOVED,'Parent restoration alias')
  want=dict(old['computed_loader_fields']);del want['input__Ahat'];need(new['computed_loader_fields']==want,'Current restoration aliases')
  need(new['computed_loader_field_formulas']=={'input__Ahat':{'operation':'+','arguments':[ATOM,1],'scope':'Historical ancestor-field restoration, not an emitted register or an additional paid gate.'}},'Historical formula wrong')
 else:need(old['source']==new['source'] and old['polynomial_source']==new['polynomial_source'],'Raw arithmetic changed')
 # Exact compositional algebra: shared interning, no hash-equivalence assumption.
 nodes={}
 def node(v):
  if v not in nodes:nodes[v]=len(nodes)
  return nodes[v]
 def evaluate(p):
  env={n:node(('coordinate',n)) for n in p['parameters']+p['auxiliaries']}
  def val(v):return env[v] if type(v)is str else node(('integer',v))
  for n,o,a,b in p['polynomial_source']:
   env[n]=node(('proved_cut',n)) if n in cuts else node((o,val(a),val(b)))
  return env,val
 a,aa=evaluate(old);b,bb=evaluate(new)
 if ordinary:need(a[ATOM]==b[ATOM],'Independent cut atom changed')
 differences=[]
 for n in set(a)&set(b):
  if a[n]!=b[n]:differences.append(n)
 need(set(differences)==({CHANGED} if ordinary else set()),'Unproved change in common register')
 need(old['comparisons']==new['comparisons'],'Comparison list changed')
 for x,y in old['comparisons']:need(aa(x)==bb(x) and aa(y)==bb(y),'Comparison operand changed')
 need(a[old['output']]==b[new['output']],'Entire output changed beyond proved cut')
 for f in old.get('unit_factors',[]):need(a[f['factor']]==b[f['factor']],'Native unit factor changed')
 # Every current arithmetic export stays live and denotes the same polynomial.
 for field in ('registers','tag_registers','computed_loader_fields'):
  for k,v in new.get(field,{}).items():need(v in b and aa(old[field][k])==bb(v),'Current exported value changed '+field+'/'+k)
 need(old['polynomial_source'][len(old['source']):]==new['polynomial_source'][len(new['source']):],'Finalizer rows changed')
 return {'local_identity':'16*(u+1)-8=16*u+8' if ordinary else 'Unchanged raw source','changed_common_registers':sorted(differences),
  'complete_output_identity':True,'identical_residuals':len(old['comparisons']),'identical_native_factors':len(old.get('unit_factors',[])),
  'exact_interned_nodes':len(nodes)}

def audit(p):
 known=set(p['parameters']+p['auxiliaries']);need(len(known)==len(p['parameters'])+len(p['auxiliaries']),'Unique coordinates');live={p['output']}
 deg={n:0 if n in p['fixed_parameters'] else 1 for n in known}
 for n,o,a,b in p['polynomial_source']:
  need(type(n)is str and n not in known and o in ('+','-','*'),'Unique gate')
  need(all(type(v)is int or type(v)is str and v in known for v in (a,b)),'Gate closure')
  da=deg[a] if type(a)is str else 0;db=deg[b] if type(b)is str else 0;deg[n]=da+db if o=='*' else max(da,db);known.add(n)
 for n,o,a,b in reversed(p['polynomial_source']):
  need(n in live,'Uncharged dead gate');live.update(v for v in (a,b) if type(v)is str)
 need(p['polynomial_source'][:len(p['source'])]==p['source'],'Certificate prefix mismatch')
 for label,name in (('certificate','source'),('polynomial','polynomial_source')):
  rows=p[name];ledger={'operations':len(rows),'M':sum(r[1]=='*' for r in rows),'A':sum(r[1]!='*' for r in rows)}
  need(p['ledger'][label]==ledger,'Complete independently recounted ledger')
 need(p['ledger']['formal_degree_upper_bound']==deg[p['output']],'Syntactic degree ledger')
 return {'certificate':p['ledger']['certificate'],'polynomial':p['ledger']['polynomial'],'syntactic_degree_bound':deg[p['output']]}

def run(source,root):
 pin(source,PIN);parent_path=source.parent/PARENT if (source.parent/PARENT).is_file() else root/PARENT;pin(parent_path,PARENT_PIN)
 pin(root/RECEIPT,RECEIPT_PIN)
 saved=json.loads((root/RECEIPT).read_text());old={f['form']:f['compiler'] for f in saved['forms']}
 m=load(source);rng=random.Random(506991);counts=Counter();records=[]
 def reject(fn):
  try:fn()
  except (ValueError,TypeError,KeyError):counts['malformed_rejected']+=1;return
  raise ValueError('Invalid call accepted')
 for key,expected in EXPECTED.items():
  def get():
   if key.startswith('base:'):
    _,o,g=key.split(':');return m.build(bool(int(o)),grouped=bool(int(g)),root=root)
   return m.build_frontier(int(key.split(':')[1]),root=root)
  p=get();q=old[key];need(normalized(m.canonical_parent(p,root=root))==q,'Actual parent differs from frozen independently reviewed receipt')
  pp=normalized(p);pr=proof(q,pp);led=audit(pp);counts['complete_source_polynomial_identities']+=1;counts['residual_identities']+=len(p['comparisons']);counts['local_offset_identities']+=p['ordinary']
  for f in ('parameters','auxiliaries','fixed_parameters','rules','comparisons','output','unit_factors','unit_retained_comparison_map','unit_group_factors','unit_groups','group_anchor','graph_ancestor','removed_comparisons','tagged_ports'):
   need(q.get(f)==pp.get(f),'Changed semantic/interface field '+f)
  for k in ('positive_witnesses','equations'):need(q['ledger'][k]==pp['ledger'][k],'Witness or equation change')
  for part in ('certificate','polynomial'):
   for k,want in (('operations',int(p['ordinary'])),('A',int(p['ordinary'])),('M',0)):
    need(q['ledger'][part][k]-pp['ledger'][part][k]==want,'Paid complete saving')
  values=(pp['ledger']['polynomial']['operations'],pp['ledger']['polynomial']['M'],pp['ledger']['polynomial']['A'],len(pp['auxiliaries']),len(pp['comparisons']),pp['exact_degree_certificate']['exact_degree'])
  need(values==expected,'Expected complete table')
  need(pp['exact_degree_certificate']['parent_certificate']==q['exact_degree_certificate'],'Parent exact degree certificate not preserved')
  need(pp['exact_degree_certificate']['exact_degree']==q['exact_degree_certificate']['exact_degree'],'Degree transfer target')
  counts['exact_degree_certificate_transfers']+=1
  for j in range(10):
   signed=j>=4;v={n:rng.randrange(-3,4) if signed else rng.randrange(1,4) for n in p['parameters']+p['auxiliaries']}
   if not p['ordinary'] and not signed:v.update(L0=j%2,R0=(j//2)%2)
   a,b=execute(q['polynomial_source'],v),execute(pp['polynomial_source'],v)
   rr=[at(a,x)-at(a,y) for x,y in q['comparisons']];ss=[at(b,x)-at(b,y) for x,y in pp['comparisons']]
   need(rr==ss and a[q['output']]==b[pp['output']],'Unfiltered full numeric identity')
   need(m.evaluate(p,v,signed=signed,root=root)==b[pp['output']],'Public evaluator')
   counts['complete_integer_evaluations']+=1;counts['signed_evaluations']+=signed
  for j in range(2):
   v={n:Fraction(rng.randrange(-2,3),rng.randrange(1,3)) for n in p['parameters']+p['auxiliaries']}
   a,b=execute(q['polynomial_source'],v),execute(pp['polynomial_source'],v)
   need(a[q['output']]==b[pp['output']],'Full rational identity');counts['complete_rational_evaluations']+=1
  v={n:1 for n in p['parameters']+p['auxiliaries']}
  for n in list(v)[::13]:
   for bad in (True,1.0,0,-1):
    if type(bad)is int and bad==0 and not p['ordinary'] and n in ('L0','R0'):continue
    vv=dict(v);vv[n]=bad;reject(lambda vv=vv:m.evaluate(p,vv,root=root))
  for field in ('source','polynomial_source','ledger','loader_offset_rewrite','exact_degree_certificate','computed_loader_fields','cross_parent_form','canonical_parent'):
   bad=copy.deepcopy(p);bad[field]=None;reject(lambda bad=bad:m.checked(bad,root=root))
  for badflag in (1,0,None):reject(lambda badflag=badflag:m.evaluate(p,v,signed=badflag,root=root))
  bad=copy.deepcopy(p);j=next(j for j,r in enumerate(bad['polynomial_source']) if any(type(x)is int for x in r[2:]));row=list(bad['polynomial_source'][j]);i=next(i for i in (2,3) if type(row[i])is int);row[i]=float(row[i]);bad['polynomial_source'][j]=tuple(row)
  reject(lambda:m.evaluate(bad,{n:10**200 for n in v},root=root))
  for vv in ({k:x for k,x in v.items() if k!=next(iter(v))},dict(v,extra=1)):reject(lambda vv=vv:m.evaluate(p,vv,root=root))
  getters=(get,lambda:m.canonical_parent(p,root=root),lambda:m.polynomial_source(p,root=root))
  for getter in getters:
   a=getter();prior=copy.deepcopy(a)
   if type(a)is dict:a['source'].clear()
   else:a.clear()
   need(exact(getter(),prior),'Public copy aliases nested cached source');counts['defensive_copy_checks']+=1
  records.append({'form':key,'independent_full_proof':pr,'ledger':led,'exact_degree':expected[-1],'witnesses':expected[3],'comparisons':expected[4]})
 for bad in (0,1,None,0.0,'yes'):
  reject(lambda bad=bad:m.build(bad,root=root));reject(lambda bad=bad:m.build(grouped=bad,root=root))
 for bad in (True,False,-1,4,0.0,None):reject(lambda bad=bad:m.build_frontier(bad,root=root))
 # Both direct and inherited source pins must stay active after cache population.
 with tempfile.TemporaryDirectory(prefix='review-u15-offset506-') as d:
  d=Path(d);shutil.copyfile(source,d/source.name);shutil.copyfile(parent_path,d/PARENT)
  nested=parent_path.parent/NESTED if (parent_path.parent/NESTED).is_file() else root/NESTED;pin(nested,NESTED_PIN);shutil.copyfile(nested,d/NESTED)
  warm=load(d/source.name);original=warm.build(root=root)
  for name in (PARENT,NESTED):
   path=d/name;data=path.read_bytes()
   try:path.write_bytes(data+b'\n# private guard mutation\n');reject(lambda:warm.build(root=root));counts['warm_source_pin_rejections']+=1
   finally:path.write_bytes(data)
   need(exact(warm.build(root=root),original),'Restored warm canonical packet changed')
 optimized=subprocess.run(['python','-O',str(source),'--root',str(root)],capture_output=True,text=True,timeout=15)
 need(optimized.returncode!=0 and 'omit -O' in optimized.stderr,'Optimized mode not rejected');counts['optimized_execution_rejection']+=1
 return {'status':'PASS','source_sha256':PIN,'parent_source_sha256':PARENT_PIN,'parent_receipt_sha256':RECEIPT_PIN,'counts':dict(counts),'forms':records,
  'scope':'Independent exact local expansion plus all-live full expression-DAG proof on all eight sources; complete ledger/interface/degrees transfer audited against frozen507 receipts. No parent universal witness rematerialization or whole partition search rerun.'}

if __name__=='__main__':
 p=argparse.ArgumentParser(description=__doc__)
 for name in ('source','root','output'):p.add_argument('--'+name,type=Path,required=True)
 p.add_argument('--expect',type=Path);a=p.parse_args();r=run(a.source.resolve(),a.root.resolve())
 if a.expect:need(exact(r,json.loads(a.expect.read_text())),'Independent saved receipt mismatch')
 a.output.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n');print(json.dumps({'status':r['status'],'counts':r['counts']},indent=2))
