#!/usr/bin/env python3
"""Independent complete-circuit review of the natural endpoint-penalty rewrite."""
import argparse,hashlib,itertools,json,random,subprocess,types
from collections import Counter
from fractions import Fraction
from pathlib import Path
PIN='7010ab32c2ac44a84ea61f4393b826cdc1401c654f20364dbad7f694e3eb605c'
RECEIPT_PIN='10cbe0a62be35c03da5e9902e88c55b457c28b3c7295026fb6f33472dbdc82c8'
PARENT_COMMIT='c5b680b90f74a792c713d5213d97a06c2b582590'
PARENT_PATH='Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/three_mass_arithmetic.py'
PARENT_PIN='d5607c6cd780d2110491171ec8aeca69e8b92dcff0f2f13eb614ed9ebaa6c7a0'
SOURCE_PINS={'certificate':'fed96578694af665258fca9eeab14fa94d8a56e810de8f684a2c9fdcd9d751e8','clean_targets':'a79405023df5a1038a69bc947314979093df39be8da7abcdf5588f77da848315'}
def need(v,s):
 if not v:raise ValueError(s)
def sha(b):return hashlib.sha256(b).hexdigest()
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if type(a)in(list,tuple):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b
def plus(a,b,sign=1):
 c=dict(a)
 for m,v in b.items():c[m]=c.get(m,0)+sign*v
 return {m:v for m,v in c.items() if v}
def times(a,b):
 c={}
 for m,v in a.items():
  for n,w in b.items():
   mon=tuple(sorted(m+n));need(len(mon)<=2,'Source exceeds quadratic intermediate degree');c[mon]=c.get(mon,0)+v*w
 return {m:v for m,v in c.items() if v}
def sum_poly(ps):
 out={}
 for p in ps:out=plus(out,p)
 return out
def const(x):return {():x} if x else {}
def coordinate(x):return {(x,):1}
def value(p,a):
 z=0
 for mon,c in p.items():
  for n in mon:c*=a[n]
  z+=c
 return z

def imported(path):
 data=path.read_bytes();need(sha(data)==PIN,'Frozen candidate source pin')
 m=types.ModuleType('_independent_endpoint_subject');m.__file__=str(path);exec(compile(data,str(path),'exec'),m.__dict__);return m

def derive(cert):
 f=cert.get('forward_certificate',cert);states=f['machine']['states'];need(len(states)==len(set(states)),'Distinct numerical state codes')
 pairs={r['u']:(r['e'],'v'+r['u'][1:]) for step in f['steps'] for r in step}
 def affine(form):
  out={}
  for name,c in form.items():
   need(type(c)is int,'Exact original affine coefficient')
   if not name:p=const(c)
   elif name in pairs:
    e,v=pairs[name];p={(v,):c,(e,):-c}
   else:p={(name,):c}
   out=plus(out,p)
  return out
 rows={r['label']:affine(r['affine']) for r in cert['squares']};need(len(rows)==len(cert['squares']),'Distinct source residual labels')
 B=len(f['branches']);h=f['horizon'];groups=[]
 for t,step in enumerate(f['steps']):
  need(len(step)==B and [r['branch'] for r in step]==list(range(B)),'Actual branch order')
  E=sum_poly(coordinate(r['e']) for r in step)
  need(rows[f'step-{t}:one-hot']==plus(E,const(1),-1),'Retained one-hot equation')
  group={}
  for j,r in enumerate(step):
   source=cert['products'][t*B+j];left=plus(E,coordinate(r['e']),-1);right=coordinate('v'+r['u'][1:])
   need(affine(source['left'])==left and affine(source['right'])==right,'Actual inactive row is not (E-e)v')
   group=plus(group,times(left,right))
  groups.append(group)
 need(len(cert['products'])==B*h,'No omitted product row')
 removed={};penalties={}
 if h:
  for name,t,key,q in [('step-0:control',0,'source',f['initial_state']),('terminal:halt',h-1,'target',f['machine']['halt'])]:
   old=const(-states.index(q));new={}
   for r,b in zip(f['steps'][t],f['branches']):
    old=plus(old,{(r['e'],):states.index(b[key])})
    if b[key]!=q:new=plus(new,coordinate(r['e']))
   need(rows[name]==old,'Literal endpoint control row');removed[name]=old;penalties[name]=new
 baseline=sum_poly([times(p,p) for p in rows.values()]+groups)
 correction=sum_poly(list(penalties.values()))
 for p in removed.values():correction=plus(correction,times(p,p),-1)
 reduced=plus(baseline,correction)
 need(reduced.get(('T','T'))==1,'Exact quadratic T^2 leader')
 need(max(map(len,reduced),default=0)==2,'Exact complete degree two')
 return dict(forward=f,affine=affine,rows=rows,groups=groups,removed=removed,penalties=penalties,baseline=baseline,correction=correction,reduced=reduced)

def check_packet(cert,p,d,new):
 names=p['variables'];need(len(names)==len(set(names)),'Unique supplied coordinates')
 need(names==[('v'+n[1:]) if n.startswith('u_') else n for n in cert['variables']],'Complete natural witness interface')
 env={n:coordinate(n) for n in names};deps={};count=Counter()
 def atom(x):
  if type(x)is str:need(x in env,'Topological source closure');return env[x]
  need(type(x)is int,'Strict source constant');return const(x)
 for row in p['source']:
  need(type(row)is list and len(row)==4,'Literal binary gate');n,o,a,b=row
  need(type(n)is str and n not in env and o in ('+','-','*'),'Fresh legal gate')
  aa,bb=atom(a),atom(b);env[n]=times(aa,bb) if o=='*' else plus(aa,bb,1 if o=='+' else -1)
  deps[n]=[v for v in (a,b) if type(v)is str and v in deps];count[o]+=1
 want=d['reduced'] if new else d['baseline'];need(atom(p['output'])==want,'Complete coefficient identity')
 expected_rows={n:v for n,v in d['rows'].items() if not(new and n in d['removed'])}
 need([x[0] for x in p['ports']['squares']]==list(expected_rows),'Residual row order/count')
 for label,port in p['ports']['squares']:need(atom(port)==expected_rows[label],'Actual affine residual port')
 need(len(p['ports']['inactive_sums'])==len(d['groups']),'All step sums paid')
 for port,poly in zip(p['ports']['inactive_sums'],d['groups']):need(atom(port)==poly,'Actual inactive group port')
 need(atom(p['ports']['N0'])=={('x',):1,():1},'Paid raw x+1 loader')
 need(atom(p['ports']['endpoint_penalty'])==(sum_poly(d['penalties'].values()) if new else {}),'Exact literal forbidden-support masks')
 live=set()
 def visit(n):
  if n in deps and n not in live:
   live.add(n)
   for k in deps[n]:visit(k)
 visit(p['output']);need(live==set(deps),'Every charged gate live')
 ledger=dict(M=count['*'],A=count['+']+count['-'],total=len(deps));need(exact(ledger,p['ledger']),'Complete ledger mismatch')
 used={v for row in p['source'] for v in row[2:] if type(v)is str and v in names}
 if type(p['output'])is str and p['output']in names:used.add(p['output'])
 need(sorted(used)==p['used_free_coordinates'] and sorted(set(names)-used)==p['unused_declared_coordinates'],'Coordinate metadata')
 f=d['forward'];need(p['natural_witnesses']==2*len(f['branches'])*f['horizon'],'All2Bh coordinate count')
 return dict(ledger=ledger,squared_rows=len(expected_rows),product_groups=len(d['groups']),polynomial_terms=len(want),paid_gates=len(deps))

def fixture(C,CT,name,h,clean,scale=1):
 I=C.Instruction;M=C.Machine
 if name=='incdec':m=M(('s','q','h'),'h',(I('s','q','inc',0),I('q','h','dec',0)));start='s'
 elif name.startswith('incchain'):
  k=int(name[8:]);states=tuple('q'+str(i) for i in range(k+1));m=M(states,states[-1],tuple(I(states[i],states[i+1],'inc',0) for i in range(k)));start=states[0]
 elif name in ('dec2','zero3','test3'):
  op='dec' if name=='dec2' else 'zero';counter=0 if name=='dec2' else 1;ins=[I('s','h',op,counter)]
  if name=='test3':ins.append(I('s','h','positive',1))
  m=M(('s','h'),'h',tuple(ins));start='s'
 elif name in ('empty','empty-not-halted'):
  m=M(('s',),'s',()) if name=='empty' else M(('s','h'),'h',());start='s'
 elif name=='interior-labels':
  m=M(('z','halt','start','mid'),'halt',(I('start','mid','inc',0),I('mid','halt','dec',0),I('z','z','nop',0)));start='start'
 else:
  _,op,counter=name.split(':');m=M(('pre','halt','start','post'),'halt',(I('start','halt',op,int(counter)),));start='start'
 if clean:return CT.export_clean_certificate(m,start,h,{'mode':'free_raw','name':'x'},{'mode':'free','name':'T'},model='phase-radius-one' if scale==4 else 'native')
 return C.export_certificate(m,start,h,{'mode':'free_raw','name':'x'},{'mode':'free','name':'y'},{'mode':'free','name':'T'},clock_scale=scale)

def run(source,receipt,repo):
 S=imported(source);rb=receipt.read_bytes();need(sha(rb)==RECEIPT_PIN,'Frozen author receipt pin');saved=json.loads(rb)
 parentbytes=subprocess.check_output(['git','-C',str(repo),'show',PARENT_COMMIT+':'+PARENT_PATH],timeout=60);need(sha(parentbytes)==PARENT_PIN,'Committed baseline source pin')
 P=S.parent(repo);sources,archives=P.source_bytes(repo)
 need({k:sha(v) for k,v in sources.items()}==SOURCE_PINS,'Original producer byte pins')
 counts=Counter();records=[];rng=random.Random(508731)
 def reject(fn):
  try:fn()
  except (ValueError,TypeError,KeyError):counts['unsupported_or_invalid_calls_rejected']+=1;return
  raise ValueError('Unexpected accepted call')
 with P.subjects(sources) as(C,CT):
  # Reuse only the authenticated source loader/context, not any polynomial or
  # endpoint mathematics from the subject. Fixtures are rebuilt independently.
  cases=[(r['fixture'],r['horizon'],r['clean'],1,r) for r in saved['cases']]
  cases += [('primitive:'+op+':'+str(c),1,clean,4,None) for op,c,clean in itertools.product(('inc','dec','nop','zero','positive'),(0,1),(False,True))]
  cases += [('empty-not-halted',h,clean,1,None) for h,clean in itertools.product((0,1),(False,True))]
  for name,h,clean,scale,reference in cases:
   cert=fixture(C,CT,name,h,clean,scale);d=derive(cert);packets={};ledgers={}
   if reference is not None:need(sha(json.dumps(cert,sort_keys=True,separators=(',',':')).encode())==reference['certificate_sha256'],'Fresh actual certificate receipt identity')
   for inactive in ('direct','factored'):
    old=S.emit(P,cert,inactive,False);new=S.emit(P,cert,inactive,True);baseline=P.emit(cert,'mass',inactive)
    need(old['source']==baseline['source'] and old['output']==baseline['output'] and old['ledger']==baseline['ledger'],'Fair baseline literal identity')
    a,b=check_packet(cert,old,d,False),check_packet(cert,new,d,True);packets[inactive]=(old,new);ledgers[inactive]={'old':a['ledger'],'new':b['ledger']}
    need(old['variables']==new['variables'],'Same complete tuple interface')
    if not h:need(old['source']==new['source'] and old['output']==new['output'],'h0 must be literally unchanged')
    if reference is not None:
     need(exact(ledgers[inactive],reference['all_ledgers'][inactive]),'Saved actual ledgers')
     if reference['full_packets'] is not None:
      need(exact(old,reference['full_packets'][inactive]['old']) and exact(new,reference['full_packets'][inactive]['new']),'Saved entire circuits')
    counts['whole_coefficient_correction_pairs']+=1;counts['literal_fair_baselines']+=1;counts['complete_live_gate_counts']+=a['paid_gates']+b['paid_gates'];counts['exact_quadratic_T_leaders']+=2
   for label,oldf in d['removed'].items():
    t=0 if label.startswith('step') else h-1;local=d['forward']['steps'][t]
    for j in range(len(local)):
     assignment={r['e']:int(i==j) for i,r in enumerate(local)}
     need((value(oldf,assignment)==0)==(value(d['penalties'][label],assignment)==0),'All-branch endpoint equivalence')
     counts['all_branch_one_hot_endpoint_cases']+=1
   for j in range(8):
    values={n:rng.randrange(-2,4) for n in packets['direct'][0]['variables']}
    diff=value(d['correction'],values)
    for old,new in packets.values():
     # Subject evaluator is compared with independently expanded coefficients.
     F,G=value(d['baseline'],values),value(d['reduced'],values)
     need(P.evaluate(old,values)==F and P.evaluate(new,values)==G and G-F==diff,'Complete signed correction')
     counts['full_signed_correction_evaluations']+=1
   for x in (0,1,4,17):
    try:a=CT.make_clean_witness(cert,{'x':x}) if clean else C.make_witness(cert,{'x':x})
    except ValueError:counts['source_guard_or_horizon_rejections']+=1;continue
    a=dict(a)
    for step in d['forward']['steps']:
     for r in step:a['v'+r['u'][1:]]=a.pop(r['u'])+a[r['e']]
    need(min(a.values())>=0 and value(d['baseline'],a)==value(d['reduced'],a)==0,'Actual same natural zero fixture')
    counts['actual_natural_zero_fixtures']+=1
   records.append(dict(fixture=name,horizon=h,clean=clean,clock_scale=scale,branch_count=len(d['forward']['branches']),witnesses=2*h*len(d['forward']['branches']),all_ledgers=ledgers,
    literal_mask_forms={k:[dict(monomial=list(m),coefficient=c) for m,c in sorted(f.items())] for k,f in d['penalties'].items()}))
  # Independent complete natural boxes on the two-step packet. Affine endpoints
  # are computed from the actual certificate after inverse mass substitution.
  cert=fixture(C,CT,'incdec',2,False);d=derive(cert);old,new=packets0=(S.emit(P,cert,penalties=False),S.emit(P,cert))
  core=[n for n in new['variables'] if n not in ('x','y','T')]
  for vs in itertools.product(range(2),repeat=len(core)):
   for x in range(3):
    a=dict(zip(core,vs));a['x']=x;a['y']=value(d['affine'](cert['final_N']),a);a['T']=value(d['affine'](cert['physical_time']),a)
    if min(a.values())<0:continue
    F,G=value(d['baseline'],a),value(d['reduced'],a)
    need(F>=0 and G>=0 and (F==0)==(G==0),'Complete natural-zero box')
    need(P.evaluate(old,a)==F and P.evaluate(new,a)==G,'Natural literal output')
    counts['full_natural_box_tuples']+=1;counts['natural_box_zeros']+=int(G==0)
  signed=saved['signed_complete_boundary']['assignment'];F=value(d['baseline'],signed);G=value(d['reduced'],signed)
  need(F==4 and G==0 and P.evaluate(old,signed)==4 and P.evaluate(new,signed)==0,'Complete signed counterexample')
  counts['complete_signed_zero_counterexamples']+=1
  fractions=[Fraction(1,2),Fraction(0),Fraction(1,2)]
  need(sum(fractions)==1 and sum(i*x for i,x in enumerate(fractions))-1==0 and fractions[0]+fractions[2]==1,'Local rational endpoint boundary')
  counts['local_rational_boundaries']+=1
  for inactive in (None,True,0,'no'):
   reject(lambda inactive=inactive:S.emit(P,cert,inactive))
  for penalties in (None,0,1,'yes'):reject(lambda penalties=penalties:S.emit(P,cert,penalties=penalties))
  empty=C.Machine(('s',),'s',())
  excluded=[C.export_certificate(empty,'s',0,{'mode':'free_raw','name':'x'}),CT.export_clean_certificate(empty,'s',0,{'mode':'free_raw','name':'x'}),C.export_certificate(empty,'s',0,{'mode':'free_raw','name':'z'},{'mode':'free','name':'y'},{'mode':'free','name':'T'})]
  for cert in excluded:reject(lambda cert=cert:S.emit(P,cert))
 return dict(status='PASS',candidate_sha256=PIN,author_receipt_sha256=RECEIPT_PIN,parent_commit=PARENT_COMMIT,parent_sha256=PARENT_PIN,original_source_pins=SOURCE_PINS,archive_pins=archives,
  counts=dict(counts),cases=records,signed_counterexample=dict(assignment=signed,old=F,new=G),scope='Independent complete coefficient expansions, literal endpoint masks, fair original schedule comparisons, liveness and exact degree two for64actual certificates/two schedules; general natural-zero proof in companion note. Original authenticated source loading reused only. No new hostile-packet API contract, horizon elimination or universal operation claim.')

if __name__=='__main__':
 ap=argparse.ArgumentParser(description=__doc__)
 for name in ('source','receipt','repo'):ap.add_argument('--'+name,type=Path,required=True)
 ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();r=run(a.source.resolve(),a.receipt.resolve(),a.repo.resolve())
 if a.expect:need(exact(r,json.loads(a.expect.read_text())),'Exact review receipt mismatch')
 if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 print(json.dumps({'status':r['status'],'counts':r['counts']},indent=2))
