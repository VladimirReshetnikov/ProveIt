#!/usr/bin/env python3
"""Independent literal-polynomial, paid-gate, and natural-fiber audit."""
import argparse,hashlib,itertools,json,types
from collections import Counter
from pathlib import Path
SOURCE_PIN='8129ec4da0aded05c98993b7575eb3ccfe42ee908c5d15c18a748a8b53d874b8'
RECEIPT_PIN='c5e8e5c8b0fd5490b4758c892408a6415b1e1fb97718722ba72764942f77d4ef'
PARENT_PIN='d5607c6cd780d2110491171ec8aeca69e8b92dcff0f2f13eb614ed9ebaa6c7a0'
def need(ok,msg):
 if not ok:raise ValueError(msg)
def sha(b):return hashlib.sha256(b).hexdigest()
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if type(a)is list:return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b
def load(path,pin,name):
 p=Path(path);b=p.read_bytes();need(sha(b)==pin,'Executable source pin before import')
 m=types.ModuleType(name);m.__file__=str(p.resolve());exec(compile(b,m.__file__,'exec'),m.__dict__);return m
def add(p,q,sign=1):
 r=p.copy()
 for m,c in q.items():r[m]=r.get(m,0)+sign*c
 return {m:c for m,c in r.items() if c}
def mul(p,q):
 r={}
 for m,c in p.items():
  for n,d in q.items():
   k=tuple(sorted(m+n));r[k]=r.get(k,0)+c*d
 return {m:c for m,c in r.items() if c}
def ev(p,a):
 total=0
 for m,c in p.items():
  for n in m:c*=a[n]
  total+=c
 return total

def literal(cert,removed):
 f=cert.get('forward_certificate',cert)
 urows={r['u']:r for step in f['steps'] for r in step}
 restored={}
 for step in f['steps']:
  chosen=[r for r in step if r['e'] in removed]
  if not step:continue
  need(len(chosen)==1,'One selector removed at every nonempty step')
  restored[chosen[0]['e']]=add({():1},{(r['e'],):1 for r in step if r is not chosen[0]},-1)
 def variable(n):
  if n in restored:return restored[n]
  if n in urows:
   r=urows[n];return add({('v'+n[1:],):1},variable(r['e']),-1)
  return {(n,):1}
 def aff(form):
  out={}
  for n,c in form.items():
   need(type(c)is int,'Exact coefficient')
   t={():1} if not n else variable(n)
   out=add(out,{m:c*v for m,v in t.items()})
  return out
 rows=[(r['label'],aff(r['affine'])) for r in cert['squares']]
 old={}
 for label,p in rows:old=add(old,mul(p,p))
 for product in cert['products']:old=add(old,mul(aff(product['left']),aff(product['right'])))
 gates=[];correction={}
 for step in f['steps']:
  if not step:gates.append({});continue
  k=next(r for r in step if r['e'] in removed)
  others=[r for r in step if r is not k]
  S={(r['e'],):1 for r in others};barrier=mul(S,add(S,{():1},-1));correction=add(correction,barrier)
  G=add(barrier,mul(S,{('v'+k['u'][1:],):1}))
  for r in others:
   e={(r['e'],):1};v={('v'+r['u'][1:],):1};one_minus=add({():1},e,-1)
   G=add(G,mul(mul(one_minus,one_minus),v))
   correction=add(correction,mul(mul(e,add(e,{():1},-1)),v))
  gates.append(G)
 return rows,gates,old,correction,restored

def check(cert,packet):
 names=packet['variables'];need(len(set(names))==len(names),'Unique supplied coordinates')
 oldnames=['v'+n[1:] if n.startswith('u_') else n for n in cert['variables']]
 removed=set(oldnames)-set(names)
 need(set(names)<=set(oldnames),'No added unknown coordinate')
 rows,gates,old,corr,restored=literal(cert,removed)
 need(removed==set(restored),'Only exact selector coordinates removed')
 need(exact(packet['restoration_forms'],{n:{('' if not m else m[0]):c for m,c in p.items()} for n,p in restored.items()}),'Complete affine restoration forms')
 f=cert.get('forward_certificate',cert);B=len(f['branches']);h=f['horizon']
 retained=[(label,p) for label,p in rows if not(B and label.endswith(':one-hot'))]
 for label,p in rows:
  if B and label.endswith(':one-hot'):need(not p,'Removed one-hot polynomial identically zero')
 want={}
 for label,p in retained:want=add(want,mul(p,p))
 for p in gates:want=add(want,p)
 need(want==add(old,corr),'Independent full correction identity')
 env={n:{(n,):1} for n in names};deps={};counts=Counter()
 def atom(x):
  if type(x)is str:need(x in env,'Topological source closure');return env[x]
  need(type(x)is int,'Integer source literal');return {():x} if x else {}
 for gate in packet['source']:
  need(type(gate)is list and len(gate)==4,'Paid binary gate')
  n,op,a,b=gate;need(type(n)is str and n not in env,'Fresh gate register');need(op in ('+','-','*'),'Supported gate')
  pa,pb=atom(a),atom(b);env[n]=mul(pa,pb) if op=='*' else add(pa,pb,1 if op=='+' else -1)
  deps[n]=[v for v in (a,b) if type(v)is str and v in deps];counts[op]+=1
 need(atom(packet['output'])==want,'Full emitted coefficient polynomial')
 need(len(retained)==len(packet['ports']['squares']),'All retained affine rows')
 for (label,p),(seen,n) in zip(retained,packet['ports']['squares']):need(label==seen and atom(n)==p,'Every residual port')
 need(len(gates)==len(packet['ports']['projected_gates']),'All step penalties')
 for g,n in zip(gates,packet['ports']['projected_gates']):need(g==atom(n),'Entire independent cubic penalty')
 need(atom(packet['ports']['N0'])=={('x',):1,():1},'Paid raw input x+1')
 live=set()
 def visit(n):
  if n in deps and n not in live:
   live.add(n)
   for v in deps[n]:visit(v)
 visit(packet['output']);need(live==set(deps),'Every charged gate live')
 ledger={'A':counts['+']+counts['-'],'M':counts['*'],'total':len(deps)}
 need(exact(ledger,packet['ledger']),'Independent full operation count')
 degree=max(map(len,want),default=0);need(degree==(3 if B>=2 and h else 2),'Exact complete degree for these endpoint packets')
 need(packet['natural_witnesses']==2*B*h-(h if B else 0),'Exact witness reduction')
 need(len([n for n in names if n not in ('x','y','T')])==packet['natural_witnesses'],'No omitted additional witnesses')
 return {'ledger':ledger,'degree':degree,'rows':len(retained),'gates':len(gates),'paid':len(deps)},(want,old,corr,restored)

def fixture(C,CT,name,h,clean,clock=False):
 I=C.Instruction;M=C.Machine
 if name=='incdec':m=M(('s','q','h'),'h',(I('s','q','inc',0),I('q','h','dec',0)))
 elif name.startswith('incchain'):
  k=int(name[8:]);qs=tuple('q'+str(i) for i in range(k+1));m=M(qs,qs[-1],tuple(I(qs[i],qs[i+1],'inc',0) for i in range(k)))
 elif name in ('dec2','zero3','test3'):
  ins=[I('s','h','dec' if name=='dec2' else 'zero',0 if name=='dec2' else 1)]
  if name=='test3':ins.append(I('s','h','positive',1))
  m=M(('s','h'),'h',tuple(ins))
 elif name=='empty':m=M(('s',),'s',())
 else:raise ValueError(name)
 if clean:return CT.export_clean_certificate(m,m.states[0],h,{'mode':'free_raw','name':'x'},{'mode':'free','name':'T'},model='phase-radius-one' if clock else 'native')
 return C.export_certificate(m,m.states[0],h,{'mode':'free_raw','name':'x'},{'mode':'free','name':'y'},{'mode':'free','name':'T'},clock_scale=4 if clock else 1)

def run(source,receipt,root,repo):
 S=load(source,SOURCE_PIN,'_selector_projection_subject');P=load(Path(root)/'three_mass_arithmetic.py',PARENT_PIN,'_selector_projection_parent')
 b=Path(receipt).read_bytes();need(sha(b)==RECEIPT_PIN,'Author receipt pin');saved=json.loads(b)
 data,archives=P.source_bytes(repo);counts=Counter();cases=[]
 with P.subjects(data) as(C,CT):
  for r in saved['cases']:
   cert=fixture(C,CT,r['fixture'],r['horizon'],r['clean']);B=len(cert.get('forward_certificate',cert)['branches']);ledgers={}
   # Parent baseline is the committed whole mass schedule, with both options paid.
   for mode in ('direct','factored'):
    old=P.emit(cert,'mass',mode)
    ops=Counter(g[1] for g in old['source'])
    paid={'M':ops['*'],'A':ops['+']+ops['-'],'total':len(old['source'])}
    need(exact(paid,old['ledger']) and exact(paid,r['baseline'][mode]),'Independent actual baseline gate ledger')
    counts['actual_baseline_gate_recounts']+=1
   for index in range(B) if B else (-1,):
    for mode in ('direct','factored','horner'):
     p=S.emit(P,cert,mode,index);info,_=check(cert,p);key=str(index)+':'+mode;ledgers[key]=info['ledger']
     need(exact(info['ledger'],r['ledgers'][key]),'Saved candidate ledger')
     if r['packets']is not None:need(exact(p,r['packets'][key]),'Saved literal packet')
     counts['complete_polynomial_and_correction_identities']+=1;counts['retained_residuals']+=info['rows'];counts['whole_cubic_step_penalties']+=info['gates'];counts['live_paid_gates']+=info['paid']
   best=min(ledgers,key=lambda k:ledgers[k]['total']);need(best==r['best'],'Fair best among literal emitted candidates')
   cases.append({k:r[k] for k in ('fixture','horizon','clean','branches','best','witnesses','old_witnesses','degree') }|{'best_ledger':ledgers[best],'baseline':r['baseline']})
  # Different implicit selectors at different times plus a separately scaled
  # physical-time endpoint; neither was required by the author's fixed-index census.
  for clean in (False,True):
   for clock in (False,True):
    cert=fixture(C,CT,'incdec',2,clean,clock)
    for indices in ([0,1],[1,0]):
     for mode in ('direct','factored','horner'):
      check(cert,S.emit(P,cert,mode,indices));counts['mixed_index_clock_complete_identities']+=1
  # Complete natural tuples with actual endpoint values; coefficients and
  # restoration are evaluated by this reviewer's independent polynomials.
  for name,h,k in [('incdec',1,1),('incdec',2,0),('zero3',1,0),('test3',1,0)]:
   cert=fixture(C,CT,name,h,False);packet=S.emit(P,cert,'horner',k)
   info,(poly,oldpoly,correction,restoration)=check(cert,packet)
   core=[n for n in packet['variables'] if n not in ('x','y','T')]
   for entries in itertools.product(range(3),repeat=len(core)):
    for x in range(3):
     vals=dict(zip(core,entries));vals.update(x=x,y=0,T=0)
     mass=vals|{n:ev(p,vals) for n,p in restoration.items()};original=mass.copy()
     for step in cert['steps']:
      for r in step:original[r['u']]=mass['v'+r['u'][1:]]-mass[r['e']]
     raw_aff=lambda f:sum(c*(1 if not n else original[n]) for n,c in f.items())
     vals['y']=raw_aff(cert['final_N']);vals['T']=raw_aff(cert['physical_time'])
     if min(vals.values())<0:continue
     score=ev(poly,vals);need(score>=0,'Entire natural supplied polynomial nonnegative')
     counts['independent_complete_natural_tuples']+=1
     if score==0:
      need(min(mass.values())>=0,'Restored selector natural at every full zero')
      need(all(original[r['u']]>=0 for step in cert['steps'] for r in step),'Restored original offsets natural')
      need(ev(oldpoly,vals)==0 and ev(correction,vals)==0,'Full zero lifts to original source')
      counts['independent_complete_natural_zeros']+=1
  cert=fixture(C,CT,'incdec',1,False);p=S.emit(P,cert,'horner',1);info,polys=check(cert,p)
  false={'x':4,'e_0_0':2,'v_0_0':5,'v_0_1':0,'y':10,'T':1508}
  need(ev(polys[0],false)==12 and ev(polys[1],false)==0 and ev(polys[2],false)==12,'Independent actual counterfeit values')
  need(ev(polys[3]['e_0_1'],false)==-1,'Non-natural missing selector')
  for invalid in (True,False,[],[0,0],[-1],[2],['0']):
   try:S.emit(P,cert,implicit=invalid)
   except ValueError:counts['bad_implicit_layout_rejections']+=1
   else:raise ValueError('Invalid actual implicit layout accepted')
  m=C.Machine(('s',),'s',());bad=[C.export_certificate(m,'s',0,{'mode':'free_raw','name':'x'}),CT.export_clean_certificate(m,'s',0,{'mode':'free_raw','name':'x'})]
  for name in ('g0','u_7_0'):
   bad.append(C.export_certificate(m,'s',0,{'mode':'free_raw','name':'x'},{'mode':'free','name':name},{'mode':'free','name':'T'}))
  bad.append(C.export_certificate(m,'s',0,{'mode':'free_raw','name':'z'},{'mode':'free','name':'y'},{'mode':'free','name':'T'}))
  for c in bad:
   try:S.emit(P,c)
   except ValueError:counts['unsupported_actual_interfaces_rejected']+=1
   else:raise ValueError('Unsupported interface accepted')
 # A local census independently checks every possible implicit position.
 for B in range(1,5):
  for k in range(B):
   for es in itertools.product(range(3),repeat=B-1):
    sm=sum(es);full_e=list(es);full_e.insert(k,1-sm)
    for vs in itertools.product(range(3),repeat=B):
     G=sm*(sm-1)+sum((1-full_e[j])**2*vs[j] for j in range(B) if j!=k)+sm*vs[k]
     condition=all(e>=0 for e in full_e) and all(v==0 for e,v in zip(full_e,vs) if not e)
     need(G>=0 and (G==0)==condition,'Exact natural local fiber')
     counts['all_positions_natural_local_tuples']+=1;counts['all_positions_natural_local_zeros']+=G==0
 return {'source_sha256':SOURCE_PIN,'author_receipt_sha256':RECEIPT_PIN,'parent_sha256':PARENT_PIN,'archive_pins':archives,'counts':dict(counts),'cases':cases,'counterfeit':{'new':12,'substituted_parent':0,'correction':12,'restored_selector':-1},'scope':'Exact entire emitted polynomial/ledger checks and a separate written general natural-zero proof; no original suite or unrestricted optimizer claim'}
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--source',required=True);ap.add_argument('--receipt',required=True);ap.add_argument('--root',required=True);ap.add_argument('--repo',required=True);ap.add_argument('--output',required=True);ap.add_argument('--expect');a=ap.parse_args();r=run(a.source,a.receipt,a.root,a.repo)
 if a.expect:need(exact(r,json.loads(Path(a.expect).read_text())),'Type-sensitive saved independent receipt')
 Path(a.output).write_text(json.dumps(r,sort_keys=True,indent=2)+'\n');print(json.dumps(r['counts'],sort_keys=True))
