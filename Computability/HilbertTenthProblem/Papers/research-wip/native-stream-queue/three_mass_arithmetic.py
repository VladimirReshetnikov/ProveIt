#!/usr/bin/env python3
"""Source-pinned paid quadratic SLPs for external-horizon three-mass certificates.

Research prototype: no fixed-arity or universal operation bound is asserted.
"""
import argparse, contextlib, copy, hashlib, io, itertools, json, random, subprocess, sys, tempfile, types, zipfile
from collections import Counter
from fractions import Fraction
from pathlib import Path, PurePosixPath
COMMIT='4e270aa4648c5fd7e18626507531046715976535'
PINS={
 'Three_Mass_Reversible_Computation.zip':('three-mass-release','fd86a8a6b71735ef08ebd7913498603213244484da8b23d81876b10c40ffd1de'),
 'Exact_Targets_Three_Mass_Units.zip':('clean-target-release','d69d8df9ee3a2074bcff1ef400853724eafb679ada8b287ef397eb8891965dcc')}
SOURCE_PINS={'certificate':'fed96578694af665258fca9eeab14fa94d8a56e810de8f684a2c9fdcd9d751e8',
             'clean_targets':'a79405023df5a1038a69bc947314979093df39be8da7abcdf5588f77da848315'}

def need(v,s):
 if not v:raise ValueError(s)
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys() and all(type(k)is str and exact(a[k],b[k]) for k in a)
 if type(a)in(list,tuple):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b
def sha(b):return hashlib.sha256(b).hexdigest()

def source_bytes(repo):
 files={};archives={}
 for name,(root,pin) in PINS.items():
  data=subprocess.check_output(['git','-C',str(repo),'show',COMMIT+':docs/incoming/'+name],timeout=60)
  need(sha(data)==pin,'Pinned archive');archives[name]=pin
  with zipfile.ZipFile(io.BytesIO(data)) as z:
   infos=z.infolist();need(len({i.filename for i in infos})==len(infos),'Duplicate member')
   members={}
   for i in infos:
    p=PurePosixPath(i.filename)
    need(not p.is_absolute() and '..'not in p.parts and '\\'not in i.filename and p.parts[0]==root,'Unsafe member')
    need((i.external_attr>>16)&0o170000!=0o120000,'Symlink member')
    if not i.is_dir():members[str(PurePosixPath(*p.parts[1:]))]=z.read(i)
  files[name]=members
 sources={'certificate':files['Three_Mass_Reversible_Computation.zip']['code/certificate.py'],
          'clean_targets':files['Exact_Targets_Three_Mass_Units.zip']['clean_targets.py']}
 need(sources['certificate']==files['Exact_Targets_Three_Mass_Units.zip']['vendor/certificate.py'],'Identical vendored core')
 for name,data in sources.items():need(sha(data)==SOURCE_PINS[name],'Pinned executable source')
 return sources,archives

@contextlib.contextmanager
def subjects(sources):
 names=('certificate','clean_targets');absent=object();old={n:sys.modules.get(n,absent) for n in names};path=list(sys.path)
 try:
  for n in names:sys.modules.pop(n,None)
  loaded={}
  with tempfile.TemporaryDirectory(prefix='three-mass-slps-') as tmp:
   for n in names:
    m=types.ModuleType(n);m.__file__=str(Path(tmp)/(n+'.py'));sys.modules[n]=m
    exec(compile(sources[n],m.__file__,'exec'),m.__dict__);loaded[n]=m
   yield loaded['certificate'],loaded['clean_targets']
 finally:
  sys.path[:]=path
  for n in names:
   if old[n]is absent:sys.modules.pop(n,None)
   else:sys.modules[n]=old[n]

def addform(*forms):
 out=Counter()
 for f in forms:
  for x,c in f.items():out[x]+=c
 return {x:c for x,c in sorted(out.items()) if c}
def scaled(f,c):return {x:c*a for x,a in f.items() if c*a}
def transform(form,pairs):
 out=dict(form)
 for e,u,v in pairs:
  c=out.pop(u,0)
  if c:out[v]=out.get(v,0)+c;out[e]=out.get(e,0)-c
 return {k:c for k,c in sorted(out.items()) if c}
def ev(f,a):return sum(c*(a[k] if k else 1) for k,c in f.items())
def oldvalue(cert,a):
 return sum(ev(r['affine'],a)**2 for r in cert['squares'])+sum(ev(r['left'],a)*ev(r['right'],a) for r in cert['products'])
def pairs_for(cert):
 forward=cert.get('forward_certificate',cert)
 return [(r['e'],r['u'],'v'+r['u'][1:]) for local in forward['steps'] for r in local]
def push(cert,old):
 out=dict(old)
 for e,u,v in pairs_for(cert):out[v]=out.pop(u)+out[e]
 return out
def pull(cert,new):
 out=dict(new)
 for e,u,v in pairs_for(cert):out[u]=out.pop(v)-out[e]
 return out

class DAG:
 def __init__(self):self.rows=[];self.memo={}
 def op(self,o,a,b):
  if type(a)is int and type(b)is int:return {'+':lambda:a+b,'-':lambda:a-b,'*':lambda:a*b}[o]()
  if o=='+':
   if a==0:return b
   if b==0:return a
  if o=='-':
   if b==0:return a
   if a==b:return 0
  if o=='*':
   if a==0 or b==0:return 0
   if a==1:return b
   if b==1:return a
  if o in ('+','*') and (type(a).__name__,str(a))>(type(b).__name__,str(b)):a,b=b,a
  key=(o,a,b)
  if key not in self.memo:
   r='g'+str(len(self.rows));self.rows.append([r,o,a,b]);self.memo[key]=r
  return self.memo[key]
 def sum(self,terms):
  out=0
  for t in terms:out=self.op('+',out,t)
  return out
 def finish(self,output,variables,ports):
  by={r[0]:r for r in self.rows};live=set()
  def visit(x):
   if x in by and x not in live:live.add(x);visit(by[x][2]);visit(by[x][3])
  visit(output)
  rows=[r for r in self.rows if r[0]in live];counts=Counter(r[1] for r in rows)
  used={x for r in rows for x in r[2:] if type(x)is str and x not in by}
  if type(output)is str and output not in by:used.add(output)
  need(used<=set(variables),'Source closure')
  def port_atoms(v):
   if type(v)is dict:
    return [a for k,w in v.items() for a in port_atoms(w)]
   if type(v)is list:
    return [a for w in v for a in port_atoms(w)]
   return [v]
  need(all(v not in by or v in live for v in port_atoms(ports) if type(v)is str),'All recorded register ports live')
  return dict(variables=variables,source=rows,output=output,ports=ports,
              ledger=dict(M=counts['*'],A=counts['+']+counts['-'],total=len(rows)),
              used_free_coordinates=sorted(used),unused_declared_coordinates=sorted(set(variables)-used))

# This is a literal affine-expression compiler, not a globally optimal SLP search.
# Equal coefficient groups and exact identical affine ports are shared.
def emit(cert,coordinate='mass',inactive='direct'):
 need(coordinate in ('literal','offset','mass') and inactive in ('direct','factored'),'Compiler mode')
 forward=cert.get('forward_certificate',cert);need(exact(forward['input_spec'],{'mode':'free_raw','name':'x'}),'Paid raw interface')
 # The research emitter intentionally supports these fixed external names only.
 # This prevents internal-register/mass-coordinate aliases and constant h=0
 # packets whose absent endpoints would make the paid N0 port irrelevant.
 need(exact(cert.get('time_spec'),{'mode':'free','name':'T'}),'Prototype requires free time endpoint T')
 if 'forward_certificate' in cert:
  need(exact(cert.get('output_variables'),['T']),'Prototype compact-clean endpoint names')
 else:
  need(exact(cert.get('output_spec'),{'mode':'free','name':'y'}) and
       exact(cert.get('output_variables'),['y','T']),'Prototype requires free output y and time T')
 pairs=pairs_for(cert);d=DAG();tokens={};cache={};N0=d.op('+','x',1)
 for e,u,v in pairs:
  if coordinate!='literal':tokens[v]=v if coordinate=='mass' else d.op('+',e,u)
 variables=[('v'+x[1:]) if x.startswith('u_') else x for x in cert['variables']] if coordinate=='mass' else list(cert['variables'])
 def aff(form):
  f=transform(form,pairs) if coordinate!='literal' else dict(sorted(form.items()));key=tuple(f.items())
  if key in cache:return cache[key]
  # Every appearance of the ordinary x uses the paid N0=x+1 port.
  constant=f.get('',0)-f.get('x',0);groups={}
  for name,c in f.items():
   if not name:continue
   token=N0 if name=='x' else tokens.get(name,name)
   groups.setdefault(c,[]).append(token)
  terms=[]
  if constant:terms.append(constant)
  for c,ts in sorted(groups.items(),key=lambda kv:(kv[0]<0,abs(kv[0]))):
   group=d.sum(ts)
   if c==1:terms.append(group)
   elif c==-1:terms.append(('-',group))
   else:terms.append(d.op('*',c,group))
  out=0
  for term in terms:
   if type(term)is tuple:out=d.op('-',out,term[1])
   else:out=d.op('+',out,term)
  cache[key]=out;return out
 ports={'N0':N0,'squares':[], 'inactive_sums':[]}
 squares=[]
 for row in cert['squares']:
  a=aff(row['affine']);ports['squares'].append([row['label'],a]);squares.append(d.op('*',a,a))
 inactive_values=[]
 for t,local in enumerate(forward['steps']):
  Eform=addform(*[{r['e']:1} for r in local]);E=aff(Eform)
  sv=[aff({r['e']:1,r['u']:1}) for r in local]
  if inactive=='direct':
   products=[]
   for r,s in zip(local,sv):
    # B=2 needs no subtraction. Otherwise E-e is at most one paid subtraction.
    if len(local)<=2:left=aff(addform(Eform,{r['e']:-1}))
    else:left=d.op('-',E,r['e'])
    products.append(d.op('*',left,s))
   term=d.sum(products)
  else:
   S=aff(addform(*[{r['e']:1,r['u']:1} for r in local]))
   diagonal=d.sum([d.op('*',r['e'],s) for r,s in zip(local,sv)])
   term=d.op('-',d.op('*',E,S),diagonal)
  inactive_values.append(term);ports['inactive_sums'].append(term)
 # One total sum, with all affine squares and all products fully paid.
 output=d.sum(squares+inactive_values)
 packet=d.finish(output,variables,ports)
 packet.update(coordinate=coordinate,inactive=inactive,horizon=forward['horizon'],branch_count=len(forward['branches']),
               natural_witnesses=2*len(forward['branches'])*forward['horizon'],
               input_coordinates=list(cert['input_variables']),output_coordinates=list(cert['output_variables']))
 return packet

def evaluate(packet,a):
 need(type(a)is dict and set(a)==set(packet['variables']),'Exact supplied coordinates')
 env=dict(a)
 for r,o,x,y in packet['source']:
  x=env[x] if type(x)is str else x;y=env[y] if type(y)is str else y
  env[r]=x+y if o=='+' else x-y if o=='-' else x*y
 return env[packet['output']] if type(packet['output'])is str else packet['output']

def padd(a,b,c=1):
 out=dict(a)
 for m,k in b.items():out[m]=out.get(m,0)+c*k
 return {m:k for m,k in out.items() if k}
def pmul(a,b):
 out={}
 for x,c in a.items():
  for y,e in b.items():
   m=tuple(sorted(x+y));out[m]=out.get(m,0)+c*e
 return {m:k for m,k in out.items() if k}
def formpoly(f):return {(k,) if k else ():c for k,c in f.items() if c}
def polynomial(cert,mass=False):
 pairs=pairs_for(cert);out={}
 def conv(f):return formpoly(transform(f,pairs) if mass else f)
 for r in cert['squares']:
  p=conv(r['affine']);out=padd(out,pmul(p,p))
 for r in cert['products']:out=padd(out,pmul(conv(r['left']),conv(r['right'])))
 return out
def sourcepoly(packet):
 env={v:{(v,):1} for v in packet['variables']}
 def atom(x):return env[x] if type(x)is str else ({():x} if x else {})
 for r,o,a,b in packet['source']:
  a,b=atom(a),atom(b);env[r]=pmul(a,b) if o=='*' else padd(a,b,1 if o=='+' else -1)
 return atom(packet['output'])

def make_case(C,CT,name,h,clean=False):
 I=C.Instruction;M=C.Machine
 if name=='incdec':m=M(('s','q','h'),'h',(I('s','q','inc',0),I('q','h','dec',0)))
 elif name.startswith('incchain'):
  k=int(name[len('incchain'):]);states=tuple('q'+str(i) for i in range(k+1));m=M(states,states[-1],tuple(I(states[i],states[i+1],'inc',0) for i in range(k)))
 elif name=='dec2':m=M(('s','h'),'h',(I('s','h','dec',0),))
 elif name=='zero3':m=M(('s','h'),'h',(I('s','h','zero',1),))
 elif name=='test3':m=M(('s','h'),'h',(I('s','h','zero',1),I('s','h','positive',1)))
 elif name=='empty':m=M(('s',),'s',())
 else:raise ValueError('Unknown explicit fixture')
 if clean:return CT.export_clean_certificate(m,m.states[0],h,{'mode':'free_raw','name':'x'}, {'mode':'free','name':'T'})
 return C.export_certificate(m,m.states[0],h,{'mode':'free_raw','name':'x'}, {'mode':'free','name':'y'}, {'mode':'free','name':'T'})

def verify(repo):
 sources,archives=source_bytes(repo);counts=Counter();results=[];rng=random.Random(80317)
 with subjects(sources) as (C,CT):
  # Valid producer packets outside the deliberately bounded prototype interface.
  empty=C.Machine(('s',),'s',())
  unsupported=[C.export_certificate(empty,'s',0,{'mode':'free_raw','name':'x'})]
  for name in ('g0','u_7_0'):
   unsupported.append(C.export_certificate(empty,'s',0,{'mode':'free_raw','name':'x'},
                       {'mode':'free','name':name},{'mode':'free','name':'T'}))
  unsupported.append(C.export_certificate(empty,'s',0,{'mode':'free_raw','name':'z'},
                      {'mode':'free','name':'y'},{'mode':'free','name':'T'}))
  unsupported.append(CT.export_clean_certificate(empty,'s',0,{'mode':'free_raw','name':'x'}))
  for cert in unsupported:
   try:emit(cert)
   except ValueError:counts['unsupported_interface_rejections']+=1
   else:raise ValueError('Unsupported prototype interface accepted')
  # Exhaust the eleven literal residue-expanded primitive forms (including both primes).
  for op,counter in itertools.product(('inc','dec','nop','zero','positive'),(0,1)):
   machine=C.Machine(('s','h'),'h',(C.Instruction('s','h',op,counter),))
   for branch in machine.branches():
    prime,r=branch.prime,branch.residue
    old,new,ticks=C.branch_forms(branch,{'e':1},{'u':1})
    a={'v':1};b={'v':prime}
    if op=='dec':a,b=b,a
    elif op=='positive':a=b={'v':prime}
    elif op=='zero':a=b={'v':prime,'e':r-prime}
    elif op=='nop':b=a
    clock=addform(scaled(a,108 if op=='inc' else 96 if op=='dec' else 192),
                  scaled(b,96 if op=='inc' else 108 if op=='dec' else 0),{'e':8})
    need([transform(f,[('e','u','v')]) for f in (old,new,ticks)]==[a,b,clock], 'Literal primitive forms after exact shift')
    need(ev(a,{'e':1,'v':0})<=0,'Selected zero-magnitude branch cannot have positive old raw value')
    counts['literal_primitive_triples']+=1
  cases=[('incdec',h,clean) for h in range(4) for clean in (False,True)]
  cases += [('incchain'+str(k),k,clean) for k in (1,2,3,4,5) for clean in (False,True)]
  cases += [('dec2',1,clean) for clean in (False,True)]
  cases += [(name,h,clean) for name in ('zero3','test3','empty') for h in (0,1,2) for clean in (False,True)]
  for name,h,clean in cases:
   cert=make_case(C,CT,name,h,clean);packets={}
   for coordinate,inactive in itertools.product(('literal','offset','mass'),('direct','factored')):
    p=emit(cert,coordinate,inactive);want=polynomial(cert,coordinate=='mass')
    need(sourcepoly(p)==want,'Whole literal polynomial identity')
    need(max(map(len,want),default=0)==2,'Exact emitted degree two with paid endpoint')
    counts['complete_symbolic_source_equalities']+=1
    packets[coordinate+'_'+inactive]=p
   for sample in range(10):
    a={v:rng.randrange(-3,5) for v in cert['variables']};b=push(cert,a)
    for key,p in packets.items():need(evaluate(p,b if p['coordinate']=='mass' else a)==oldvalue(cert,a),'Signed complete source identity');counts['signed_output_equalities']+=1
   for x in (0,1,2,4,17,10**40):
    try:old=CT.make_clean_witness(cert,{'x':x}) if clean else C.make_witness(cert,{'x':x})
    except ValueError:counts['rejected_horizon_or_guard_fixtures']+=1;continue
    new=push(cert,old);need(exact(pull(cert,new),old),'Zero-fiber graph inverse')
    for key,p in packets.items():need(evaluate(p,new if p['coordinate']=='mass' else old)==0,'Full source natural zero');counts['natural_zero_source_evaluations']+=1
    need(all(type(v)is int and v>=0 for v in new.values()),'Natural forward graph')
    if clean:
     full,forms=CT.affine_full_witness_lift(cert);lifted={v:ev(f,pull(cert,new)) for v,f in forms.items()}
     need(all(v>=0 for v in lifted.values()) and oldvalue(full,lifted)==0,'Actual compact/full natural lift')
     counts['full_cleaned_zero_lifts']+=1
   # Matched factoring schedule saves the actually live e+u additions, no hidden inputs.
   for inactive in ('direct','factored'):
    a,b=packets['offset_'+inactive],packets['mass_'+inactive]
    need(a['ledger']['M']==b['ledger']['M'],'Coordinate shift multiplication count')
    need(a['ledger']['A']-b['ledger']['A']==a['natural_witnesses']//2,'Bh live addition savings')
    counts['matched_Bh_savings']+=1
   keep=(name,h,clean) in [('incdec',2,False),('incdec',2,True),('incchain3',3,False),('incchain3',3,True),('zero3',1,False),('empty',0,True)]
   results.append(dict(fixture=name,horizon=h,cleaned_exact_target=clean,branch_count=len(cert.get('forward_certificate',cert)['branches']),
     full_packets=packets if keep else None,ledgers={k:p['ledger'] for k,p in packets.items()},
     source_sha256={k:sha(json.dumps(p['source'],sort_keys=True,separators=(',',':')).encode()) for k,p in packets.items()},
     certificate=cert if keep else None,certificate_sha256=sha(json.dumps(cert,sort_keys=True,separators=(',',':')).encode())))
  worked=[]
  for clean in (False,True):
   cert=make_case(C,CT,'incdec',2,clean)
   a=CT.make_clean_witness(cert,{'x':4}) if clean else C.make_witness(cert,{'x':4})
   b=push(cert,a);need(b['T']==(7968 if clean else 3016),'Explicit source/clean clock fixture')
   need(evaluate(emit(cert),b)==0,'Explicit complete polynomial boundary fixture')
   worked.append(dict(cleaned_exact_target=clean,old_assignment=a,new_assignment=b,score=0,
                      raw_initial=5,raw_final=5,external_source_horizon=2))
  # Exact natural enumeration verifies reverse graph positivity, including false horizons.
  for name,h in [('zero3',1),('test3',1),('incdec',1),('empty',0)]:
   cert=make_case(C,CT,name,h,False);p=emit(cert);witness=[v for v in p['variables'] if v not in ('x','y','T')]
   # Endpoints are determined affine outputs, so this enumerates every core tuple in the stated box.
   for values in itertools.product(range(3),repeat=len(witness)):
    for x in range(4):
     a=dict(zip(witness,values));a['x']=x;old=pull(cert,{**a,'y':0,'T':0})
     a['y']=ev(cert['final_N'],old);a['T']=ev(cert['physical_time'],old)
     if min(a.values())<0:continue
     F=evaluate(p,a);counts['natural_box_tuples']+=1
     if F==0:
      b=pull(cert,a);need(all(v>=0 for v in b.values()) and oldvalue(cert,b)==0,'Natural inverse at every enumerated zero');counts['natural_box_zeros']+=1
  # Boundary: on the ambient natural orthant inverse offsets need not be natural.
  c=make_case(C,CT,'zero3',1,False);p=emit(c);a=dict.fromkeys(p['variables'],0);a.update(x=0,e_0_1=1,v_0_1=Fraction(2,3),y=1,T=200)
  need(evaluate(p,a)==0 and pull(c,a)['u_0_1']==Fraction(-1,3),'Real/rational inverse domain counterexample')
  counterexample=dict(fixture='zero3',assignment={k:str(v) for k,v in a.items()},score=0,restored_selected_u='-1/3',
   meaning='The mass-coordinate natural-zero proof uses integrality. This rational zero has no nonnegative offset pullback.')
  c=make_case(C,CT,'dec2',1,False);p=emit(c);a={'x':0,'e_0_0':1,'v_0_0':Fraction(1,2),'y':Fraction(1,2),'T':158}
  need(evaluate(p,a)==0 and pull(c,a)['u_0_0']==Fraction(-1,2),'Rational false integer guard')
  false_guard=dict(assignment={k:str(v) for k,v in a.items()},score=0,restored_selected_u='-1/2',
                   meaning='Prime-two decrement at raw N0=1 is impossible on the intended natural domain.')
 return dict(status='PASS_THREE_MASS_ARITHMETIC',source_commit=COMMIT,archive_pins=archives,source_pins=SOURCE_PINS,
  counts=dict(counts),cases=results,worked_natural_fixtures=worked,rational_boundary=counterexample,rational_false_guard=false_guard,
  scope='Complete fixed-external-horizon quadratic circuits for actual source/compact-clean certificates with raw loader N0=x+1 and requested endpoints. Natural-zero coordinate bijection; all-value affine-substitution identity. No universal fixed-arity or global optimality claim.')

if __name__=='__main__':
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--repo',type=Path,required=True);p.add_argument('--output',type=Path);p.add_argument('--expect',type=Path);a=p.parse_args();r=verify(a.repo)
 if a.expect:need(exact(r,json.loads(a.expect.read_text())),'Typed saved receipt')
 if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 print(json.dumps(dict(status=r['status'],counts=r['counts'],frontiers=[{k:v for k,v in row.items() if k in ('fixture','horizon','cleaned_exact_target','branch_count','ledgers')} for row in r['cases'] if row['full_packets']]),indent=2))
