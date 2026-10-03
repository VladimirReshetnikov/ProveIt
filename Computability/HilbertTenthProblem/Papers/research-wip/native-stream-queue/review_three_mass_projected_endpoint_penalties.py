#!/usr/bin/env python3
"""Independent complete-polynomial and natural grouped-barrier audit."""
import argparse,hashlib,itertools,json,types
from collections import Counter
from pathlib import Path
SOURCE='f5fec893112b011564620834e0b76095c1ea53b9545d4fb76ccabb3230bdaaf6'
RECEIPT='998d4852eeefd18d9c5d3aa8a3b82e6af31d5d6b9cc0f0817a1715cf1c24f768'
REVIEW='c519ac0693e4928b64a1fead9ab30212570d50eb63331cf3706d335f20906321'
PARENT='d5607c6cd780d2110491171ec8aeca69e8b92dcff0f2f13eb614ed9ebaa6c7a0'
DEPS={'three_mass_selector_projection.py':'8129ec4da0aded05c98993b7575eb3ccfe42ee908c5d15c18a748a8b53d874b8','three_mass_endpoint_penalties.py':'7010ab32c2ac44a84ea61f4393b826cdc1401c654f20364dbad7f694e3eb605c'}
def need(b,s):
 if not b:raise ValueError(s)
def sha(b):return hashlib.sha256(b).hexdigest()
def load(path,pin,name):
 p=Path(path);b=p.read_bytes();need(sha(b)==pin,'Pin before source execution')
 m=types.ModuleType(name);m.__file__=str(p.resolve());exec(compile(b,m.__file__,'exec'),m.__dict__);return m

def model(A,cert,p):
 f=cert.get('forward_certificate',cert);B=len(f['branches']);h=f['horizon']
 oldnames=['v'+n[1:] if n.startswith('u_') else n for n in cert['variables']]
 removed=set(oldnames)-set(p['variables']);rows,gates,oldmass,oldcorr,restored=A.literal(cert,removed)
 projected=A.add(oldmass,oldcorr);bylabel=dict(rows)
 mask_forms={};masks=[[] for _ in range(h)]
 if h:
  for label,t,field,target in [('step-0:control',0,'source',f['initial_state']),('terminal:halt',h-1,'target',f['machine']['halt'])]:
   if p['endpoints']=='none' or (p['endpoints']=='initial' and t!=0) or (p['endpoints']=='terminal' and label!='terminal:halt') or (p['endpoints']=='initial' and label!='step-0:control'):continue
   form={r['e']:1 for r,b in zip(f['steps'][t],f['branches']) if b[field]!=target}
   mask_forms[label]=form;masks[t].append(form)
 K={};weights=[];negative=[];weighted=[];extra={}
 for t,step in enumerate(f['steps']):
  if not step:weights.append(1);negative.append(0);weighted.append({});continue
  k=next(r for r in step if r['e'] in removed);S={(r['e'],):1 for r in step if r is not k}
  r=sum(k['e'] in mask for mask in masks[t]);w=2 if r==2 else 1;weights.append(w);negative.append(r)
  barrier=A.mul(S,A.add(S,{():1},-1));increment={m:(w-1)*c for m,c in barrier.items() if (w-1)*c}
  extra=A.add(extra,increment);weighted.append(A.add(gates[t],increment))
 for form in mask_forms.values():
  for n,c in form.items():K=A.add(K,{m:c*d for m,d in restored.get(n,{(n,):1}).items()})
 retained=[(label,q) for label,q in rows if label not in mask_forms and not(B and label.endswith(':one-hot'))]
 want={}
 for label,q in retained:want=A.add(want,A.mul(q,q))
 for q in weighted:want=A.add(want,q)
 want=A.add(want,K)
 correction=A.add(extra,K)
 for label in mask_forms:correction=A.add(correction,A.mul(bylabel[label],bylabel[label]),-1)
 need(want==A.add(projected,correction),'Exact complete correction to projected parent')
 need(A.exact(p['barrier_weights'],weights) and A.exact(p['implicit_forbidden_penalty_counts'],negative),'Independent endpoint overlap weights')
 need(A.exact(p['endpoint_penalties'],mask_forms),'Actual branch-label endpoint masks')
 need(set(p['removed_endpoint_squares'])==set(mask_forms),'Exact removed endpoint row labels')
 need(A.exact(p['restoration_forms'],{n:{('' if not m else m[0]):c for m,c in q.items()} for n,q in restored.items()}),'Exact unique restoration')
 return want,projected,correction,retained,weighted,K,restored

def check(A,cert,p):
 want,old,corr,rows,gates,K,restore=model(A,cert,p)
 env={n:{(n,):1} for n in p['variables']};need(len(env)==len(p['variables']),'Unique coordinates');ops=Counter();deps={}
 def atom(x):
  if type(x)is str:need(x in env,'Topological source closure');return env[x]
  need(type(x)is int,'Exact literal type');return {():x} if x else {}
 for item in p['source']:
  need(type(item)is list and len(item)==4,'Binary paid gate');n,op,a,b=item
  need(type(n)is str and n not in env and op in ('+','-','*'),'Fresh exact source gate')
  pa,pb=atom(a),atom(b);env[n]=A.mul(pa,pb) if op=='*' else A.add(pa,pb,1 if op=='+' else -1);ops[op]+=1
  deps[n]=[x for x in (a,b) if type(x)is str and x in deps]
 need(atom(p['output'])==want,'Entire emitted coefficient polynomial')
 need(len(rows)==len(p['ports']['squares']),'All remaining row ports')
 for (label,poly),(seen,reg) in zip(rows,p['ports']['squares']):need(label==seen and atom(reg)==poly,'Every actual residual')
 need(len(gates)==len(p['ports']['projected_gates']),'All grouped step gates')
 for poly,reg in zip(gates,p['ports']['projected_gates']):need(atom(reg)==poly,'Full weighted cubic guard')
 need(atom(p['ports']['endpoint_penalty'])==K,'Full paid endpoint-mask sum')
 need(atom(p['ports']['N0'])=={('x',):1,():1},'Paid ordinary raw input')
 live=set()
 def visit(n):
  if n in deps and n not in live:
   live.add(n)
   for d in deps[n]:visit(d)
 visit(p['output']);need(live==set(deps),'All charged source nodes live')
 ledger={'M':ops['*'],'A':ops['+']+ops['-'],'total':len(deps)};need(A.exact(ledger,p['ledger']),'Independent complete gate ledger')
 f=cert.get('forward_certificate',cert);B=len(f['branches']);h=f['horizon'];degree=max(map(len,want),default=0)
 need(degree==(3 if B>=2 and h else 2),'Exact degree of every complete source')
 need(p['natural_witnesses']==2*B*h-(h if B else 0),'Witness count')
 need(set(p['variables'])==set(['v'+n[1:] if n.startswith('u_') else n for n in cert['variables']])-set(restore),'Only implicit selectors deleted')
 return {'ledger':ledger,'degree':degree,'rows':len(rows),'guards':len(gates),'paid':len(deps)},(want,old,corr,restore)

def run(source,receipt,review,dependencies,parent_root,repo):
 Q=load(source,SOURCE,'_combined_subject');A=load(review,REVIEW,'_own_prior_polynomial_review')
 P=load(Path(parent_root)/'three_mass_arithmetic.py',PARENT,'_mass_parent')
 R=load(Path(dependencies)/'three_mass_selector_projection.py',DEPS['three_mass_selector_projection.py'],'_projection_parent')
 E=load(Path(dependencies)/'three_mass_endpoint_penalties.py',DEPS['three_mass_endpoint_penalties.py'],'_endpoint_parent')
 b=Path(receipt).read_bytes();need(sha(b)==RECEIPT,'Author receipt pin');saved=json.loads(b)
 sources,archives=P.source_bytes(repo);counts=Counter();records=[]
 with P.subjects(sources) as(C,CT):
  trap=C.export_certificate(C.Machine(('s','h','z'),'h',(C.Instruction('s','h','zero',1),C.Instruction('z','z','nop',0))),'s',1,{'mode':'free_raw','name':'x'},{'mode':'free','name':'y'},{'mode':'free','name':'T'})
  for row in saved['cases']:
   name,h,clean=row['fixture'],row['horizon'],row['clean'];cert=trap if name=='double-endpoint-trap' else A.fixture(C,CT,name,h,clean)
   B=len(cert.get('forward_certificate',cert)['branches']);ledgers={};baseline={}
   if row['certificate']is not None:need(A.exact(cert,row['certificate']),'Actual full exporter fixture')
   for k in range(B) if B else (-1,):
    for mode in ('direct','factored','horner'):
     old=R.emit(P,cert,mode,k);none=Q.emit(P,R,E,cert,mode,k,'none');check(A,cert,none)
     need(A.exact(none['source'],old['source']) and none['output']==old['output'] and A.exact(none['ledger'],old['ledger']),'Literal entire no-endpoint baseline')
     key=str(k)+':'+mode;baseline[key]=old['ledger'];counts['literal_baselines_and_complete_polynomials']+=1
     for end in ('initial','terminal','both'):
      p=Q.emit(P,R,E,cert,mode,k,end);info,_=check(A,cert,p);key=str(k)+':'+mode+':'+end;ledgers[key]=info['ledger']
      need(A.exact(info['ledger'],row['all_ledgers'][key]),'All recorded ledgers')
      if key==row['best_new'] and row['complete_best_new']is not None:need(A.exact(p,row['complete_best_new']),'Saved best complete source')
      counts['full_candidate_coefficient_identities_and_degrees']+=1;counts['retained_residuals']+=info['rows'];counts['weighted_guards']+=info['guards'];counts['live_paid_candidate_gates']+=info['paid']
   best=min(ledgers,key=lambda x:ledgers[x]['total']);bestold=min(baseline,key=lambda x:baseline[x]['total'])
   need(best==row['best_new'] and bestold==row['best_baseline'],'Fair common finite schedule search')
   records.append({'fixture':name,'horizon':h,'clean':clean,'old':baseline[bestold],'new':ledgers[best],'best_new':best,'witnesses':row['natural_witnesses']})
  for clean in (False,True):
   cert=A.fixture(C,CT,'incdec',2,clean,True)
   for indices in ([0,1],[1,0]):
    for mode in ('direct','factored','horner'):
     for end in ('initial','terminal','both'):
      check(A,cert,Q.emit(P,R,E,cert,mode,indices,end));counts['mixed_index_scaled_clock_identities']+=1
  false={'x':2,'e_0_0':1,'e_0_1':1,'v_0_0':1,'v_0_1':1,'v_0_2':0,'y':3,'T':584}
  packet=Q.emit(P,R,E,trap,'direct',2,'both');_,(safe,old,corr,restore)=check(A,trap,packet)
  need(A.ev(safe,false)==2 and A.ev(old,false)==7 and A.ev(corr,false)==-5,'Exact full trap values')
  need(A.ev(restore['e_0_2'],false)==-1 and packet['barrier_weights']==[2],'Actual trap implicit selector and weight')
  # Removing the extra S(S-1), here2, makes the complete new polynomial zero.
  need(A.ev(safe,false)-2==0,'Complete unweighted false zero')
  for name,h,k in [('incdec',2,0),('double-endpoint-trap',1,2),('zero3',1,0)]:
   cert=trap if name=='double-endpoint-trap' else A.fixture(C,CT,name,h,False)
   p=Q.emit(P,R,E,cert,'horner',k,'both');_,(poly,old,corr,rest)=check(A,cert,p)
   core=[n for n in p['variables'] if n not in ('x','y','T')]
   for entries in itertools.product(range(3),repeat=len(core)):
    for x in range(3):
     vals=dict(zip(core,entries));vals.update(x=x,y=0,T=0);mass=vals|{n:A.ev(v,vals) for n,v in rest.items()};original=mass.copy()
     for step in cert['steps']:
      for r in step:original[r['u']]=mass['v'+r['u'][1:]]-mass[r['e']]
     aff=lambda f:sum(c*(1 if not n else original[n]) for n,c in f.items())
     vals['y']=aff(cert['final_N']);vals['T']=aff(cert['physical_time'])
     if min(vals.values())<0:continue
     value=A.ev(poly,vals);need(value>=0,'Complete natural polynomial nonnegative');counts['independent_full_natural_tuples']+=1
     if value==0:
      need(min(mass.values())>=0 and A.ev(old,vals)==0,'Natural inverse to projected parent')
      need(all(original[r['u']]>=0 for step in cert['steps'] for r in step),'Natural original offset lift');counts['independent_full_natural_zeros']+=1
  for invalid in (False,1,None,[],{},'wrong'):
   try:Q.emit(P,R,E,trap,endpoints=invalid)
   except ValueError:counts['endpoint_option_rejections']+=1
   else:raise ValueError('Malformed endpoint option accepted')
 # Independently enumerate every implicit position, not merely the last, for
 # all pairs of support masks at B<=3. The proof treats arbitrary B.
 for B in range(1,4):
  for k in range(B):
   for es in itertools.product(range(3),repeat=B-1):
    S=sum(es);full=list(es);full.insert(k,1-S)
    for masks in itertools.product(range(1<<B),repeat=2):
     r=sum((mask>>k)&1 for mask in masks);w=2 if r==2 else 1;K=sum(e for mask in masks for j,e in enumerate(full) if (mask>>j)&1)
     for vs in itertools.product(range(2),repeat=B):
      G=w*S*(S-1)+sum((1-full[j])**2*vs[j] for j in range(B) if j!=k)+S*vs[k];total=G+K
      valid=all(e>=0 for e in full) and all(v==0 for e,v in zip(full,vs) if e==0) and all(not((mask>>j)&1) for mask in masks for j,e in enumerate(full) if e==1)
      need(total>=0 and (total==0)==valid,'Complete arbitrary-mask local zero characterization');counts['all_positions_two_mask_natural_cases']+=1
 return {'source_sha256':SOURCE,'author_receipt_sha256':RECEIPT,'independent_polynomial_helper_sha256':REVIEW,'dependency_pins':DEPS,'parent_sha256':PARENT,'archives':archives,'counts':dict(counts),'cases':records,'actual_trap':{'projected_parent':7,'naive_composition':0,'safe_composition':2,'correction_to_parent':-5,'restored_implicit_selector':-1},'scope':'General grouped natural-zero proof plus exact full emitted-source/correction/degree/ledger audit; no original suites, no unrestricted circuit search'}
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--source',required=True);ap.add_argument('--receipt',required=True);ap.add_argument('--projection-review',required=True);ap.add_argument('--dependencies',required=True);ap.add_argument('--parent-root',required=True);ap.add_argument('--repo',required=True);ap.add_argument('--output',required=True);ap.add_argument('--expect');a=ap.parse_args();r=run(a.source,a.receipt,a.projection_review,a.dependencies,a.parent_root,a.repo)
 if a.expect:
  A=load(a.projection_review,REVIEW,'_review_equality');need(A.exact(r,json.loads(Path(a.expect).read_text())),'Typed saved review receipt')
 Path(a.output).write_text(json.dumps(r,sort_keys=True,indent=2)+'\n');print(json.dumps(r['counts'],sort_keys=True))
