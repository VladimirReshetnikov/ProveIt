#!/usr/bin/env python3
"""Paid natural endpoint-penalty circuits; external horizon, no witness projection."""
import argparse,hashlib,itertools,json,random,subprocess,types
from collections import Counter
from pathlib import Path
COMMIT='c5b680b90f74a792c713d5213d97a06c2b582590'
PARENT_PATH='Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/three_mass_arithmetic.py'
PARENT_SHA='d5607c6cd780d2110491171ec8aeca69e8b92dcff0f2f13eb614ed9ebaa6c7a0'

def need(v,s):
 if not v:raise ValueError(s)
def sha(b):return hashlib.sha256(b).hexdigest()
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if type(a)in(list,tuple):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b

def parent(repo):
 data=subprocess.check_output(['git','-C',str(repo),'show',COMMIT+':'+PARENT_PATH],timeout=60)
 need(sha(data)==PARENT_SHA,'Pinned parent source differs')
 m=types.ModuleType('_three_mass_endpoint_parent');m.__file__=PARENT_PATH
 exec(compile(data,PARENT_PATH,'exec'),m.__dict__)
 return m

def endpoint_forms(P,cert):
 forward=cert.get('forward_certificate',cert)
 if forward['horizon']==0:return {},{}
 states=forward['machine']['states'];codes={q:i for i,q in enumerate(states)}
 start=forward['initial_state'];halt=forward['machine']['halt'];branches=forward['branches']
 first,last=forward['steps'][0],forward['steps'][-1]
 old={'step-0:control':P.addform({r['e']:codes[b['source']] for r,b in zip(first,branches)},{'':-codes[start]}),
      'terminal:halt':P.addform({r['e']:codes[b['target']] for r,b in zip(last,branches)},{'':-codes[halt]})}
 new={'step-0:control':{r['e']:1 for r,b in zip(first,branches) if b['source']!=start},
      'terminal:halt':{r['e']:1 for r,b in zip(last,branches) if b['target']!=halt}}
 rows={r['label']:r['affine'] for r in cert['squares']}
 need(all(P.addform(rows[k])==f for k,f in old.items()),'Literal endpoint source differs')
 return old,new

def emit(P,cert,inactive='direct',penalties=True):
 need(type(penalties)is bool and inactive in ('direct','factored'),'Exact emitter option')
 # Reuse the reviewed interface validation before compiling the new schedule.
 P.emit(cert,'mass',inactive)
 old,replacements=endpoint_forms(P,cert) if penalties else ({},{})
 forward=cert.get('forward_certificate',cert);pairs=P.pairs_for(cert);d=P.DAG();cache={}
 N0=d.op('+','x',1)
 variables=[('v'+x[1:]) if x.startswith('u_') else x for x in cert['variables']]
 def aff(form):
  f=P.transform(form,pairs);key=tuple(f.items())
  if key in cache:return cache[key]
  constant=f.get('',0)-f.get('x',0);groups={}
  for name,c in f.items():
   if name:groups.setdefault(c,[]).append(N0 if name=='x' else name)
  terms=[]
  if constant:terms.append(constant)
  for c,ts in sorted(groups.items(),key=lambda kv:(kv[0]<0,abs(kv[0]))):
   group=d.sum(ts)
   if c==1:terms.append(group)
   elif c==-1:terms.append(('-',group))
   else:terms.append(d.op('*',c,group))
  out=0
  for term in terms:out=d.op('-',out,term[1]) if type(term)is tuple else d.op('+',out,term)
  cache[key]=out;return out
 ports={'N0':N0,'squares':[],'inactive_sums':[],'endpoint_penalty':0};squares=[]
 for row in cert['squares']:
  if row['label'] in replacements:continue
  a=aff(row['affine']);ports['squares'].append([row['label'],a]);squares.append(d.op('*',a,a))
 inactive_values=[]
 for local in forward['steps']:
  Eform=P.addform(*[{r['e']:1} for r in local]);E=aff(Eform)
  sv=[aff({r['e']:1,r['u']:1}) for r in local]
  if inactive=='direct':
   products=[]
   for r,s in zip(local,sv):
    left=aff(P.addform(Eform,{r['e']:-1})) if len(local)<=2 else d.op('-',E,r['e'])
    products.append(d.op('*',left,s))
   term=d.sum(products)
  else:
   S=aff(P.addform(*[{r['e']:1,r['u']:1} for r in local]))
   diagonal=d.sum([d.op('*',r['e'],s) for r,s in zip(local,sv)])
   term=d.op('-',d.op('*',E,S),diagonal)
  inactive_values.append(term);ports['inactive_sums'].append(term)
 penalty_form=P.addform(*replacements.values());linear=aff(penalty_form);ports['endpoint_penalty']=linear
 output=d.sum(squares+inactive_values+[linear])
 packet=d.finish(output,variables,ports)
 packet.update(coordinate='mass',inactive=inactive,endpoint_penalties=penalties,
               horizon=forward['horizon'],branch_count=len(forward['branches']),
               natural_witnesses=2*len(forward['branches'])*forward['horizon'],
               input_coordinates=list(cert['input_variables']),output_coordinates=list(cert['output_variables']),
               removed_squares=old,replacement_linear_forms=replacements)
 return packet

def target_polynomial(P,cert):
 out=P.polynomial(cert,True);old,new=endpoint_forms(P,cert)
 for f in old.values():
  a=P.formpoly(f);out=P.padd(out,P.pmul(a,a),-1)
 for f in new.values():out=P.padd(out,P.formpoly(f))
 return out

def test_cases():
 cases=[('incdec',h,clean) for h in range(4) for clean in (False,True)]
 cases += [('incchain'+str(k),k,clean) for k in (1,2,3,4,5) for clean in (False,True)]
 cases += [('dec2',1,clean) for clean in (False,True)]
 cases += [(name,h,clean) for name in ('zero3','test3','empty') for h in (0,1,2) for clean in (False,True)]
 return cases

def verify(repo):
 P=parent(repo);sources,archives=P.source_bytes(repo);counts=Counter();records=[];rng=random.Random(802206)
 with P.subjects(sources) as(C,CT):
  cases=[(name,h,clean,P.make_case(C,CT,name,h,clean)) for name,h,clean in test_cases()]
  # A nonminimum initial state and nonmaximum halt state test the unweighted
  # support criterion rather than relying on sign of old numerical state codes.
  I=C.Instruction;M=C.Machine
  m=M(('z','halt','start','mid'),'halt',(I('start','mid','inc',0),I('mid','halt','dec',0),I('z','z','nop',0)))
  for clean in (False,True):
   c=CT.export_clean_certificate(m,'start',2,{'mode':'free_raw','name':'x'},{'mode':'free','name':'T'}) if clean else C.export_certificate(m,'start',2,{'mode':'free_raw','name':'x'},{'mode':'free','name':'y'},{'mode':'free','name':'T'})
   cases.append(('interior-labels',2,clean,c))
  for name,h,clean,c in cases:
   old_forms,new_forms=endpoint_forms(P,c);packets={}
   for inactive in ('direct','factored'):
    old=emit(P,c,inactive,False);reference=P.emit(c,'mass',inactive)
    need(old['source']==reference['source'] and old['output']==reference['output'] and old['ledger']==reference['ledger'],'Fair old schedule literal equality')
    new=emit(P,c,inactive,True)
    need(P.sourcepoly(old)==P.polynomial(c,True),'Baseline full polynomial')
    need(P.sourcepoly(new)==target_polynomial(P,c),'New full polynomial correction')
    need(max(map(len,P.sourcepoly(new)),default=0)==2,'Exact complete degree two')
    need(new['variables']==old['variables'] and new['natural_witnesses']==old['natural_witnesses'],'No hidden variable/input deletion')
    counts['complete_symbolic_polynomial_and_ledger_pairs']+=1
    packets[inactive]={'old':old,'new':new}
   for i in range(20):
    a={v:rng.randrange(-3,5) for v in packets['direct']['new']['variables']}
    difference=sum(P.ev(f,a) for f in new_forms.values())-sum(P.ev(f,a)**2 for f in old_forms.values())
    for pair in packets.values():
     need(P.evaluate(pair['new'],a)-P.evaluate(pair['old'],a)==difference,'Full signed endpoint correction')
     counts['signed_full_corrections']+=1
   for x in (0,1,2,4,17,10**30):
    try:old=CT.make_clean_witness(c,{'x':x}) if clean else C.make_witness(c,{'x':x})
    except ValueError:counts['rejected_horizon_or_guard_fixtures']+=1;continue
    a=P.push(c,old)
    for pair in packets.values():
     need(P.evaluate(pair['old'],a)==P.evaluate(pair['new'],a)==0,'Same supplied natural zero')
     counts['complete_natural_zero_pairs']+=1
   # All one-hot endpoint choices, not just the actually reachable selected branch.
   forward=c.get('forward_certificate',c);B=len(forward['branches'])
   if h:
    for label,form in old_forms.items():
     coords=[r['e'] for r in forward['steps'][0 if label.startswith('step') else -1]]
     for j in range(B):
      a=dict.fromkeys(coords,0);a[coords[j]]=1
      need((P.ev(form,a)==0)==(P.ev(new_forms[label],a)==0),'Endpoint condition equivalence for all branches')
      counts['one_hot_boundary_cases']+=1
   keep=(name,h,clean) in [('incdec',2,False),('incdec',2,True),('incchain3',3,False),('incchain3',3,True),('zero3',1,False),('empty',0,True),('interior-labels',2,False)]
   best_old=min((p['old'] for p in packets.values()),key=lambda p:p['ledger']['total']);best_new=min((p['new'] for p in packets.values()),key=lambda p:p['ledger']['total'])
   records.append(dict(fixture=name,horizon=h,clean=clean,branch_count=B,
                       old_ledger=best_old['ledger'],new_ledger=best_new['ledger'],
                       savings=best_old['ledger']['total']-best_new['ledger']['total'],
                       all_ledgers={k:{s:p['ledger'] for s,p in pair.items()} for k,pair in packets.items()},
                       full_packets=packets if keep else None,certificate=c if keep else None,
                       certificate_sha256=sha(json.dumps(c,sort_keys=True,separators=(',',':')).encode())))
  # Complete natural boxes with endpoints evaluated from the actual source forms.
  for name,h in [('incdec',1),('incdec',2),('zero3',1),('empty',0)]:
   c=P.make_case(C,CT,name,h,False);old=emit(P,c,penalties=False);new=emit(P,c)
   witnesses=[v for v in new['variables'] if v not in ('x','y','T')]
   values=range(2) if len(witnesses)>4 else range(3)
   for core in itertools.product(values,repeat=len(witnesses)):
    for x in range(3):
     a=dict(zip(witnesses,core));a['x']=x
     u=P.pull(c,{**a,'y':0,'T':0});a['y']=P.ev(c['final_N'],u);a['T']=P.ev(c['physical_time'],u)
     if min(a.values())<0:continue
     F,G=P.evaluate(old,a),P.evaluate(new,a)
     need(F>=0 and G>=0 and (F==0)==(G==0),'Complete natural zero-set equivalence')
     counts['natural_full_tuple_comparisons']+=1;counts['natural_box_zeros']+=int(G==0)
  # Rational non-one-hot cancellation: old code zero need not mean actual source.
  state_weights=[0,1,2];target=1
  # Record exact fractions as numerator/denominator strings; no float is evaluated.
  from fractions import Fraction
  a=[Fraction(1,2),Fraction(0),Fraction(1,2)]
  need(sum(a)==1 and sum(v*c for v,c in zip(a,state_weights))-target==0 and a[0]+a[2]==1,'Rational endpoint boundary')
  boundary=dict(codes=state_weights,target=target,selectors=['1/2','0','1/2'],old_control_residual=0,new_penalty=1,
                scope='Local endpoint condition over a rational simplex; not a claimed complete packet counterexample')
  c=P.make_case(C,CT,'incdec',2,False)
  signed={'x':0,'e_0_0':-2,'e_0_1':2,'e_1_0':-2,'e_1_1':2,
          'v_0_0':0,'v_0_1':1,'v_1_0':0,'v_1_1':1,'y':1,'T':600}
  need(P.evaluate(emit(P,c),signed)==0 and P.evaluate(emit(P,c,penalties=False),signed)==4,'Complete signed zero-set counterexample')
  signed_boundary=dict(assignment=signed,new_value=0,old_value=4,
                       scope='Ordinary x and endpoints remain natural; negative selectors invalidate extension to all integer witnesses')
  for option in (0,1,None,'yes'):
   try:emit(P,c,penalties=option)
   except ValueError:counts['exact_option_rejections']+=1
   else:raise ValueError('Nonboolean endpoint mode accepted')
  a=P.push(c,C.make_witness(c,{'x':4}));p=emit(P,c)
  need(P.evaluate(p,a)==0 and a['T']==3016 and a['y']==5,'Complete worked boundary fixture')
 return dict(status='PASS_THREE_MASS_ENDPOINT_PENALTIES',parent_commit=COMMIT,parent_sha256=PARENT_SHA,
             archive_pins=archives,source_pins=P.SOURCE_PINS,counts=dict(counts),cases=records,
             worked_natural_fixture=dict(assignment=a,polynomial_value=0),rational_local_boundary=boundary,
             signed_complete_boundary=signed_boundary,
             scope='Same complete natural zero tuples with all2Bh witnesses and paid raw loader/endpoints. Exact full polynomial correction, not off-zero equality. Fixed external horizon; no universal bound or integer/real zero-equivalence claim.')

if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--repo',type=Path,required=True);p.add_argument('--output',type=Path);p.add_argument('--expect',type=Path);a=p.parse_args();r=verify(a.repo)
 if a.expect:need(exact(r,json.loads(a.expect.read_text())),'Typed saved receipt differs')
 if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 print(json.dumps(dict(status=r['status'],counts=r['counts'],cases=[{k:v for k,v in c.items() if k in ('fixture','horizon','clean','old_ledger','new_ledger','savings')} for c in r['cases'] if c['full_packets']]),indent=2))
