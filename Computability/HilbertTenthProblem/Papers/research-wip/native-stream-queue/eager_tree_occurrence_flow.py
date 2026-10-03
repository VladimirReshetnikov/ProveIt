#!/usr/bin/env python3
"""Fully paid finite eager-Tree certificates using root occurrence flow.

This preserves represented natural input/output triples at each external N;
it does not preserve witness tuples, unique fibers, or fixed-arity universality.
"""
import argparse,copy,hashlib,json,random,subprocess,sys,tempfile,types
from pathlib import Path
if not __debug__:raise RuntimeError('run without -O')
KERNEL='SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/canonical-diophantine-certificates/code/21-eager-tree-tree_kernel.py'
PIN='636ce7feadd65198b59050a7ca799c185fd4845e6d7d3a741a2628e3e4684b52'
SCALARS=['x','y','z','h','a','b','c','u','v','d','e','q','j','k']
def need(x,msg):
 if not x:raise ValueError(msg)
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys()and all(exact(a[k],b[k])for k in a)
 if type(a)in(list,tuple):return len(a)==len(b)and all(exact(x,y)for x,y in zip(a,b))
 return a==b
def parent(repo):
 path=Path(repo)/KERNEL;data=path.read_bytes();need(hashlib.sha256(data).hexdigest()==PIN,'kernel source pin')
 name='_authenticated_eager_tree_flow';m=types.ModuleType(name);m.__file__=str(path);prior=sys.modules.get(name);sys.modules[name]=m
 try:exec(compile(data,str(path),'exec'),m.__dict__)
 finally:
  if prior is None:sys.modules.pop(name,None)
  else:sys.modules[name]=prior
 return m

def fields(N,flow=False):
 names=[]
 for i in range(N):
  names += [f'r{i}_{"mu"if flow and f=="h"else f}'for f in SCALARS]
  names += [f'r{i}_t{j}'for j in range(5)]
  names += [f'r{i}_p{s}_{j}'for s in range(3)for j in range(N)]
 return names+['program','argument','output']
class Gate:
 def __init__(self,c,v,d,value):self.c,self.v,self.degree,self.value=c,v,d,value
 def op(self,o,b):
  b=self.c.coerce(b);n='g'+str(len(self.c.rows));self.c.rows.append([n,o,self.v,b.v]);self.c.M+=o=='*';self.c.A+=o!='*'
  value=self.value*b.value if o=='*'else self.value+b.value if o=='+'else self.value-b.value
  return Gate(self.c,n,self.degree+b.degree if o=='*'else max(self.degree,b.degree),value)
 def __add__(self,b):return self.op('+',b)
 __radd__=__add__
 def __sub__(self,b):return self.op('-',b)
 def __mul__(self,b):return self.op('*',b)
 __rmul__=__mul__
class Trace:
 def __init__(self,names):self.names=iter(names);self.rows=[];self.M=0;self.A=0
 def var(self,value):return Gate(self,next(self.names),1,value)
 def coerce(self,v):
  if isinstance(v,Gate):return v
  need(type(v)is int,'literal integer');return Gate(self,v,0,v)
 def sum(self,terms):
  terms=list(terms)
  if not terms:return self.coerce(0)
  out=terms[0]
  for v in terms[1:]:out=out+v
  return out

def finalizer(rows,residuals):
 out=copy.deepcopy(rows)
 for i,r in enumerate(residuals):out.append([f'flow_square_{i}','*',r,r])
 name='flow_square_0'
 for i in range(1,len(residuals)):
  n=f'flow_sum_{i}';out.append([n,'+',name,f'flow_square_{i}']);name=n
 return out,name

def inspect(rows,free,ports):
 seen=set(free);deps={};M=0;degree={v:1 for v in free}
 for n,o,a,b in rows:
  need(type(n)is str and n not in seen and o in('+','-','*'),'typed fresh operation')
  need(all(type(v)is int or type(v)is str and v in seen for v in(a,b)),'closed exact operand')
  da=0 if type(a)is int else degree[a];db=0 if type(b)is int else degree[b];degree[n]=da+db if o=='*'else max(da,db)
  seen.add(n);deps[n]=(a,b);M+=o=='*'
 live=set();todo=list(ports)
 while todo:
  n=todo.pop()
  if type(n)is int or n in live:continue
  live.add(n);todo.extend(deps.get(n,()))
 need(set(deps)<=live and set(free)<=live,'all gates and fields live')
 return {'operations':len(rows),'M':M,'A':len(rows)-M,'degree_upper_bound':max(0 if type(v)is int else degree[v]for v in ports),'all_live':True}

def canonical_parent(N,*,repo):
 need(type(N)is int and N>=1,'positive external row count');m=parent(repo);tr=Trace(fields(N));m.Circuit=lambda:tr
 rows=[{**{f:0 for f in SCALARS},'t':[0]*5,'pointers':[[0]*N for _ in range(3)]}for _ in range(N)]
 result=m.polynomial(rows,0,0,0);size=sum(result['certificate_gates'].values());count=23*N+3
 need(len(tr.rows)==27*N*N+125*N+8,'actual parent complete count')
 squares=tr.rows[size:size+count];need(all(o=='*'and a==b for n,o,a,b in squares),'literal parent finalizer squares')
 res=[r[2]for r in squares];free=fields(N);cert=tr.rows[:size]
 need(len(res)==count and len(free)==3*N*N+19*N+3,'complete parent interface')
 return {'N':N,'free':free,'source':cert,'residuals':res,'polynomial_source':tr.rows,'output':tr.rows[-1][0],
  'certificate_ledger':inspect(cert,free,res),'polynomial_ledger':inspect(tr.rows,free,[tr.rows[-1][0]]),'witnesses':len(free)-3}

def _rewrite(p):
 N=p['N'];old=p['source'];removed=[23*i+22 for i in range(N)];kept=[r for i,r in enumerate(p['residuals'])if i not in removed]
 deps={n:(a,b)for n,o,a,b in old};live=set();todo=list(kept)
 while todo:
  n=todo.pop()
  if n in deps and n not in live:live.add(n);todo.extend(deps[n])
 rows=[copy.deepcopy(r)for r in old if r[0]in live];free=fields(N,True)
 need(not any(f'r{i}_h'in r[2:]for i in range(N)for r in rows),'heights private to erased equations')
 flow=[]
 for i in range(N):
  terms=[]
  for j in range(N):
   for slot in range(3):
    n=f'mass_{i}_{j}_{slot}';rows.append([n,'*',f'r{j}_mu',f'r{j}_p{slot}_{i}']);terms.append(n)
  total=terms[0]
  for k,t in enumerate(terms[1:],1):
   n=f'incoming_{i}_{k}';rows.append([n,'+',total,t]);total=n
  n=f'balance_{i}';rows.append([n,'-',f'r{i}_mu',total])
  if i==0:rows.append(['root_injection','-',n,1]);n='root_injection'
  flow.append(n)
 res=list(p['residuals'])
 for i,j in enumerate(removed):res[j]=flow[i]
 poly,output=finalizer(rows,res);cert=inspect(rows,free,res);ledger=inspect(poly,free,[output])
 need(ledger['operations']==27*N*N+124*N+9,'paid complete flow formula')
 need(ledger['M']==p['polynomial_ledger']['M']and ledger['A']==p['polynomial_ledger']['A']-(N-1),'exact N-1 addition saving')
 return {'N':N,'free':free,'source':rows,'residuals':res,'polynomial_source':poly,'output':output,
  'certificate_ledger':cert,'polynomial_ledger':ledger,'witnesses':len(free)-3,'residual_count':len(res),'exact_degree':4,
  'retained_parent_residual_indices':[i for i in range(len(res))if i not in removed],'changed_parent_residual_indices':removed,
  'domains':'All supplied scalar and selector coordinates natural, including zero. External N>=1.',
  'theorem':'Same represented natural(program,argument,output) triples as the parent at each fixed N; not same witness tuples or unique fibers.',
  'scope':'Finite row-indexed circuit family; N remains external. No fixed-arity universal polynomial or conversion to positive-only witnesses.'}

# Coefficient dictionaries give exact residual identities; they never quotient
# by a zero equation or infer a polynomial identity from sampled evaluations.
def plus(a,b,sign=1):
 out=dict(a)
 for mon,v in b.items():out[mon]=out.get(mon,0)+sign*v
 return {mon:v for mon,v in out.items()if v}
def times(a,b):
 out={}
 for ma,va in a.items():
  for mb,vb in b.items():
   mon=tuple(sorted(ma+mb));out[mon]=out.get(mon,0)+va*vb
 return {mon:v for mon,v in out.items()if v}
def atom(v):return {():v}if type(v)is int and v else {}if type(v)is int else{(v,):1}
def expand(rows,free):
 d={v:atom(v)for v in free}
 for n,o,a,b in rows:
  a=atom(a)if type(a)is int else d[a];b=atom(b)if type(b)is int else d[b]
  d[n]=times(a,b)if o=='*'else plus(a,b,1 if o=='+'else-1)
 return d

def source_proof(p,q):
 N=p['N'];old=expand(p['source'],p['free']);new=expand(q['source'],q['free'])
 # Removed source gates are precisely the old private height cones. Every
 # retained source instruction, not just residual value, is literally equal.
 oldrows={r[0]:r for r in p['source']};kept=[r for r in q['source']if r[0]in oldrows]
 need(all(r==oldrows[r[0]]for r in kept),'literal retained source rows')
 for i in q['retained_parent_residual_indices']:
  need(old[p['residuals'][i]]==new[q['residuals'][i]],'all-value retained residual identity')
 for i,idx in enumerate(q['changed_parent_residual_indices']):
  height=plus(atom(f'r{i}_h'),atom(1),-1);flow=plus(atom(f'r{i}_mu'),atom(int(i==0)),-1)
  for j in range(N):
   for slot in range(3):
    height=plus(height,times(atom(f'r{i}_p{slot}_{j}'),atom(f'r{j}_h')),-1)
    flow=plus(flow,times(atom(f'r{j}_p{slot}_{i}'),atom(f'r{j}_mu')),-1)
  need(old[p['residuals'][idx]]==height and new[q['residuals'][idx]]==flow,'complete height/flow residuals')
 need(all(max(map(len,new[r]),default=0)<=2 for r in q['residuals']),'all residuals quadratic')
 leader={mon:v for mon,v in new[q['residuals'][1]].items()if len(mon)==2}
 need(leader=={('r0_a','r0_a'):-1,('r0_a','r0_b'):-2,('r0_b','r0_b'):-1},'nonzero retained pairing quadratic')
 oldprivate=[r for r in p['source']if r[0]not in {row[0]for row in kept}]
 newprivate=[r for r in q['source']if r[0]not in oldrows]
 count=lambda rows:{'M':sum(r[1]=='*'for r in rows),'A':sum(r[1]!='*'for r in rows)}
 need(count(oldprivate)=={'M':3*N*N,'A':3*N*N+N},'complete old private cone ledger')
 need(count(newprivate)=={'M':3*N*N,'A':3*N*N+1},'complete new private cone ledger')
 need(q['certificate_ledger']['M']==12*N*N+33*N and q['certificate_ledger']['A']==15*N*N+45*N+4,'closed certificate ledger')
 need(q['polynomial_ledger']['M']==12*N*N+56*N+3 and q['polynomial_ledger']['A']==15*N*N+68*N+6,'closed polynomial ledger')
 return {'unchanged_source_rows':len(kept),'retained_residual_identities':len(q['retained_parent_residual_indices']),
  'changed_residual_identities':N,'old_private_ledger':count(oldprivate),'new_private_ledger':count(newprivate),
  'complete_correction':'F_flow(mu)-F_height(h) = sum_i[(mu_i-delta_i0-sum_js mu_j*p_jsi)^2-(h_i-1-sum_js p_isj*h_j)^2]; all other supplied coordinates identical, h and mu independent.',
  'exact_degree':4,'degree_reason':'All residuals quadratic; retained d_0-F(a_0,b_0) has nonzero quadratic part -(a_0+b_0)^2. A sum of real squares of top homogeneous parts cannot cancel.',
  'retained_quadratic_leader':[[list(mon),v]for mon,v in sorted(leader.items())]}

def build(N,*,repo):return _rewrite(canonical_parent(N,repo=repo))
def rewrite(p,*,repo):
 need(type(p)is dict,'parent packet');N=p.get('N');need(exact(p,canonical_parent(N,repo=repo)),'complete canonical parent');return _rewrite(p)
def checked(p,*,repo):
 need(type(p)is dict,'packet');q=build(p.get('N'),repo=repo);need(exact(p,q),'entire canonical packet');return q

def run(rows,values):
 d=dict(values)
 for n,o,a,b in rows:
  a=a if type(a)is int else d[a];b=b if type(b)is int else d[b];d[n]=a*b if o=='*'else a+b if o=='+'else a-b
 return d

def evaluate(p,values,*,signed=False,repo):
 p=checked(p,repo=repo);need(type(signed)is bool and type(values)is dict and set(values)==set(p['free']),'complete assignment and mode')
 need(all(type(k)is str and type(v)is int for k,v in values.items()),'exact integer values')
 if not signed:need(all(v>=0 for v in values.values()),'natural domain')
 return run(p['polynomial_source'],values)[p['output']]

def flatten(rows,program,argument,output,mu=None):
 N=len(rows);d={}
 for i,row in enumerate(rows):
  for f in SCALARS:d[f'r{i}_{"mu"if mu is not None and f=="h"else f}']=mu[i]if mu is not None and f=='h'else row[f]
  d.update({f'r{i}_t{j}':v for j,v in enumerate(row['t'])})
  d.update({f'r{i}_p{s}_{j}':v for s,ps in enumerate(row['pointers'])for j,v in enumerate(ps)})
 d.update(program=program,argument=argument,output=output);return d

def root_flow(rows):
 N=len(rows);mu=[0]*N;mu[0]=1
 for i in sorted(range(N),key=lambda i:rows[i]['h'],reverse=True):
  for ps in rows[i]['pointers']:
   for j,v in enumerate(ps):mu[j]+=mu[i]*v
 return mu

def verify(repo):
 rng=random.Random(20261003);forms=[];counts={'whole_corrections':0,'retained_residual_values':0,'real_application_zeros':0,'guards':0,'copies':0};m=parent(repo)
 for N in(1,2,3,5,8):
  p=canonical_parent(N,repo=repo);q=build(N,repo=repo);need(exact(rewrite(p,repo=repo),q),'exact parent public rewrite')
  for case in range(12):
   values={n:rng.randint(-2,3)for n in p['free']};nv={n.replace('_h','_mu')if n.endswith('_h')else n:v for n,v in values.items()}
   old=run(p['polynomial_source'],values);new=run(q['polynomial_source'],nv)
   difference=sum(new[q['residuals'][i]]**2-old[p['residuals'][i]]**2 for i in q['changed_parent_residual_indices'])
   need(new[q['output']]-old[p['output']]==difference,'whole residual correction')
   for i in q['retained_parent_residual_indices']:need(new[q['residuals'][i]]==old[p['residuals'][i]],'literal retained residual');counts['retained_residual_values']+=1
   counts['whole_corrections']+=1
  for field in q:
   bad=copy.deepcopy(q);bad.pop(field)
   try:checked(bad,repo=repo)
   except ValueError:counts['guards']+=1
   else:raise AssertionError('missing field accepted')
  for field in('source','polynomial_source','free','residuals'):
   bad=copy.deepcopy(q);bad[field]=tuple(bad[field])
   try:checked(bad,repo=repo)
   except ValueError:counts['guards']+=1
   else:raise AssertionError('noncanonical container accepted')
   bad=build(N,repo=repo);bad[field].clear();need(exact(build(N,repo=repo),q),'defensive copy');counts['copies']+=1
  forms.append({'packet':q,'parent':p,'source_proof':source_proof(p,q)})
 for x in range(12):
  for y in range(5):
   ev=m.Evaluation(budget=100,max_bits=512)
   try:z=ev.app(x,y)
   except(m.Exhausted,m.RepeatedActiveCall,RecursionError):continue
   for pad in(0,1):
    rows=m.certificate(ev,(x,y),pad=pad);N=len(rows);q=build(N,repo=repo);values=flatten(rows,x,y,z,root_flow(rows))
    need(evaluate(q,values,repo=repo)==0,'complete genuine root flow zero');counts['real_application_zeros']+=1
 # Root leaf plus a disconnected cyclic counterfeit. Its self loop defeats
 # any natural height assignment; a free positive circulation satisfies flow.
 ev=m.Evaluation();I,omega=10,1014;ev.app(I,omega)
 ev.records[(omega,omega)]=dict(x=omega,y=omega,z=0,h=1,a=I,b=I,c=0,u=omega,v=omega,tag=3,premises=[(I,omega),(I,omega),(omega,omega)])
 ev.app(0,0);rows=m.certificate(ev,(0,0));N=len(rows);cyc=next(i for i,r in enumerate(rows)if(r['x'],r['y'])==(omega,omega));q=build(N,repo=repo);examples=[]
 for circulation in(1,2):
  mu=[0]*N;mu[0]=1;mu[cyc]=circulation
  for ps in rows[cyc]['pointers']:
   for j,v in enumerate(ps):
    if j!=cyc:mu[j]+=circulation*v
  for i in sorted((i for i in range(N)if i!=cyc),key=lambda i:rows[i]['h'],reverse=True):
   for ps in rows[i]['pointers']:
    for j,v in enumerate(ps):mu[j]+=mu[i]*v
  values=flatten(rows,0,0,1,mu);need(evaluate(q,values,repo=repo)==0,'disconnected cycle admitted with correct root')
  need(m.polynomial(rows,0,0,1)['value']>0,'old heights reject same local rows')
  examples.append({'circulation':circulation,'row_count':N,'cycle_row':cyc,'values':values,'output':0})
 # Public domain/type/ownership and warm-source checks supplement the proof.
 def rejects(call):
  try:call()
  except ValueError:counts['guards']+=1
  else:raise AssertionError('malformed public request accepted')
 for badN in(None,True,1.0,0,-1,'2'):rejects(lambda:build(badN,repo=repo))
 q=build(2,repo=repo);p=canonical_parent(2,repo=repo);values={n:0 for n in q['free']}
 for bad in(None,[],q):rejects(lambda:rewrite(bad,repo=repo))
 for field in('source','polynomial_source','residuals'):
  bad=copy.deepcopy(p);bad[field]=tuple(bad[field]);rejects(lambda:rewrite(bad,repo=repo))
 for field in('N','witnesses','exact_degree'):
  bad=copy.deepcopy(q);bad[field]=float(bad[field]);rejects(lambda:checked(bad,repo=repo))
 for val in(True,0.0,-1):
  bad=dict(values);bad['r0_mu']=val;rejects(lambda:evaluate(q,bad,repo=repo))
 for bad in({},dict(values,extra=0)):
  rejects(lambda:evaluate(q,bad,repo=repo))
 rejects(lambda:evaluate(q,values,signed=1,repo=repo))
 for position,row in enumerate(q['polynomial_source']):
  for col in(2,3):
   if type(row[col])is int:
    for val in(float(row[col]),bool(row[col])):
     bad=copy.deepcopy(q);bad['polynomial_source'][position][col]=val
     rejects(lambda:checked(bad,repo=repo))
 negative={n:-1 for n in q['free']};need(evaluate(q,negative,signed=True,repo=repo)==run(q['polynomial_source'],negative)[q['output']],'explicit signed algebra evaluation')
 with tempfile.TemporaryDirectory(prefix='tree_flow_pin_')as tmp:
  file=Path(tmp)/KERNEL;file.parent.mkdir(parents=True);data=(Path(repo)/KERNEL).read_bytes();file.write_bytes(data)
  build(1,repo=tmp);file.write_bytes(data+b'\n');rejects(lambda:build(1,repo=tmp));counts['warm_pin_rejections']=1
 proc=subprocess.run([sys.executable,'-O',str(Path(__file__).resolve()),'--repo',str(repo)],capture_output=True,text=True)
 need(proc.returncode!=0 and 'run without -O'in proc.stderr,'optimized Python rejected');counts['optimized_mode_rejections']=1
 return {'status':'PASS_EAGER_TREE_ROOT_OCCURRENCE_FLOW','source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'kernel_path':KERNEL,'kernel_sha256':PIN,'counts':counts,'forms':forms,'unreachable_cycle_examples':examples,
  'formula':{'natural_witnesses':'3*N^2+19*N','quadratic_residuals':'23*N+3','full_operations':'27*N^2+124*N+9','saved_additions':'N-1','exact_degree':4},
  'scope':'Exact represented triples for every fixed external N. Flow prevents root-reachable cycles only; no same-witness inverse, uniqueness, or fixed-arity universal bound.'}

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--repo',type=Path,required=True);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();r=verify(a.repo)
 if a.expect:need(exact(r,json.loads(a.expect.read_text())),'typed saved receipt')
 if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 print(r['status'],r['counts'])
if __name__=='__main__':main()
