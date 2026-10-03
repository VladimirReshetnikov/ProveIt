"""Complete paid sharing of three beta suffix queries; no unbounded Tree compiler."""
import argparse,copy,hashlib,json,random,subprocess,sys,tempfile
from fractions import Fraction
from pathlib import Path
if not __debug__:raise RuntimeError('Run without -O')
PINS={'eager_tree_beta_membership_interface.py':'bdb27b56b8701a1e392e799e742d135a4c0f107abc987982c5eb59efe947be34','eager_tree_beta_membership_interface.json':'de8da8729d5167aa1196d374d4603dec865a9b6ae4529747afc632576dd83f7b','eager_tree_beta_membership_interface.md':'b7f3ef7c12f0ae0ff14cd49ec57802b06d6842bd5b30bc044397d02866a115e3'}
def need(p,msg):
 if not p:raise ValueError(msg)
def exact(a,b):
 return type(a)is type(b)and(a.keys()==b.keys()and all(exact(a[k],b[k])for k in a)if type(a)is dict else len(a)==len(b)and all(exact(x,y)for x,y in zip(a,b))if type(a)in(list,tuple)else a==b)
def digest(x):return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def authenticate(root=None):
 root=Path(__file__).resolve().parent if root is None else Path(root);blobs={}
 for name,pin in PINS.items():
  b=(root/name).read_bytes();need(hashlib.sha256(b).hexdigest()==pin,'Parent bytes '+name);blobs[name]=b
 receipt=json.loads(blobs['eager_tree_beta_membership_interface.json']);forms=receipt['forms'];need(len(forms)==2,'Both literal parent forms')
 return copy.deepcopy(forms[0]['packet']),copy.deepcopy(forms[1]['packet'])
def plus(a,b,sign=1):
 out=dict(a)
 for m,c in b.items():out[m]=out.get(m,0)+sign*c
 return {m:c for m,c in out.items()if c}
def times(a,b):
 out={}
 for m,c in a.items():
  for n,d in b.items():k=tuple(sorted(m+n));out[k]=out.get(k,0)+c*d
 return {m:c for m,c in out.items()if c}
def atom(x):return {(x,):1}if type(x)is str else({():x}if x else{})
def expand(p):
 env={x:atom(x)for x in p['inputs']+p['witnesses']}
 for n,o,a,b in p['source']:
  a=env[a]if type(a)is str else atom(a);b=env[b]if type(b)is str else atom(b);env[n]=times(a,b)if o=='*'else plus(a,b,1 if o=='+'else-1)
 return env
def run(p,values):
 env=dict(values)
 for n,o,a,b in p['source']:
  a=env[a]if type(a)is str else a;b=env[b]if type(b)is str else b;env[n]=a+b if o=='+'else a-b if o=='-'else a*b
 return env
def ledger(p):
 known=set(p['inputs']+p['witnesses']);deps={};M=0
 for n,o,a,b in p['source']:
  need(type(n)is str and n not in known and o in('+','-','*'),'Fresh binary gate');need(all(type(x)is int or type(x)is str and x in known for x in(a,b)),'Closed exact operands');known.add(n);deps[n]=(a,b);M+=o=='*'
 live=set();todo=[p['output']]
 while todo:
  n=todo.pop()
  if type(n)is int or n in live:continue
  live.add(n);todo.extend(deps.get(n,()))
 need(known<=live,'All supplied ports and paid gates live');return dict(M=M,A=len(p['source'])-M,operations=len(p['source']),all_live=True)
def _assembly(computed_active,ungated,gated,shared):
 inputs=['A','b','i','N','D0','D1','D2']+(['t3','t4']if computed_active else['active','t3']);witnesses=[f'{w}{j}'for j in range(3)for w in('h','k','q','s')];rows=[['active','+','t3','t4']]if computed_active else[]
 if shared:rows.append(['shared_i2','+','i',2])
 residuals=[];sos=[];outputs=[]
 for j in range(3):
  model=ungated if shared else gated
  rename={x:x for x in('A','b','i','N')};rename['D']=f'D{j}';rename['active']='active'if j<2 else't3';rename.update({w:f'{w}{j}'for w in('h','k','q','s')});rename.update({r[0]:f'query{j}_{r[0]}'for r in model['source']})
  for n,o,a,b in model['source']:
   if shared and n=='ih':continue
   if shared and n=='j1':rows.append([rename[n],'+','shared_i2',f'h{j}']);continue
   rows.append([rename[n],o,rename[a]if type(a)is str else a,rename[b]if type(b)is str else b])
  residuals.extend(rename[x]for x in model['residuals']);sos.append(rename['sos']);outputs.append(rename[model['output']])
 if shared:rows.extend([['first_pair','+',sos[0],sos[1]],['first_guard','*','active','first_pair'],['third_guard','*','t3',sos[2]],['output','+','first_guard','third_guard']])
 else:rows.extend([['baseline_pair','+',outputs[0],outputs[1]],['output','+','baseline_pair',outputs[2]]])
 p=dict(computed_active=computed_active,inputs=inputs,witnesses=witnesses,source=rows,residuals=residuals,output='output');p['ledger']=ledger(p);poly=expand(p)['output'];p['exact_degree']=max(map(len,poly));need(p['exact_degree']==7,'Complete degree7')
 return p
def canonical_parent(computed_active=False,*,root=None):
 need(type(computed_active)is bool,'Exact active option');u,g=authenticate(root);return _assembly(computed_active,u,g,False)
def build(computed_active=False,*,root=None):
 need(type(computed_active)is bool,'Exact active option');u,g=authenticate(root);old=_assembly(computed_active,u,g,False);p=_assembly(computed_active,u,g,True)
 need(expand(old)['output']==expand(p)['output'],'Exact full polynomial identity')
 need(p['ledger']==dict(M=17,A=33+int(computed_active),operations=50+int(computed_active),all_live=True),'Whole charged child ledger')
 need(old['ledger']==dict(M=18,A=35+int(computed_active),operations=53+int(computed_active),all_live=True),'Whole charged baseline ledger')
 p.update(parent_pins=copy.deepcopy(PINS),baseline_source_sha256=digest(old['source']),baseline_ledger=old['ledger'],full_polynomial_identity=True,natural_zero_tuple_bijection='Identity map on the same complete supplied natural tuple',supplied_target_scope='D0,D1,D2 are already evaluated scalar ports; target computation and code coherence are not included.',scope='Three local queries at shared A,b,i,N, with12 natural witnesses. Computed-active mode pays active=t3+t4; supplied-active mode leaves this relation external. No fixed-arity Tree compiler or universal count.')
 return p
def checked(p,*,root=None):
 need(type(p)is dict,'Packet dictionary');canonical=build(p.get('computed_active'),root=root);need(exact(p,canonical),'Complete canonical packet');return canonical
def evaluate(p,values,*,signed=False,root=None):
 need(type(signed)is bool,'Exact signed flag');p=checked(p,root=root);need(type(values)is dict and set(values)==set(p['inputs']+p['witnesses'])and all(type(x)is int and(signed or x>=0)for x in values.values()),'Complete exact integer assignment/domain');return run(p,values)[p['output']]
def verify(root):
 forms=[];counts=dict(full_source_identities=0,full_evaluations=0,signed_evaluations=0,rational_evaluations=0,identity_zero_maps=0,rejections=0,copies=0,warm_pins=0)
 rng=random.Random(37014)
 for computed in(False,True):
  old=canonical_parent(computed,root=root);p=build(computed,root=root);po=expand(old);pn=expand(p);need(po['output']==pn['output'],'Whole coefficient identity');need(all(po[r]==pn[r]for r in p['residuals']),'Nine entire local residual identities');counts['full_source_identities']+=1
  for case in range(30):
   v={n:rng.randrange(-3,5)if case%2 else rng.randrange(5)for n in p['inputs']+p['witnesses']}
   if case>=24:v={n:Fraction(x,3)for n,x in v.items()};counts['rational_evaluations']+=1
   elif case%2:counts['signed_evaluations']+=1
   a=run(old,v)['output'];b=run(p,v)['output'];need(a==b,'Complete source evaluation equality');counts['full_evaluations']+=1
   if case<24:need(evaluate(p,v,signed=bool(case%2),root=root)==b,'Guarded public evaluator')
  # Arbitrary A,b, choose actual suffix indices; targets and all quotient/slack witnesses are explicit.
  for A in(0,1,37,101):
   for b in(0,2):
    i=0;N=5;v=dict(A=A,b=b,i=i,N=N,t3=1)
    if computed:v['t4']=1
    else:v['active']=2
    for j,index in enumerate((1,2,3)):
     m=1+(index+1)*b;D=A%m;v.update({f'D{j}':D,f'h{j}':index-i-1,f'k{j}':N-index-1,f'q{j}':A//m,f's{j}':m-1-D})
    need(evaluate(p,v,root=root)==run(old,v)['output']==0,'Identity natural zero map');counts['identity_zero_maps']+=1
   v={n:0 for n in p['inputs']+p['witnesses']};v.update(A=A,N=0,D0=9,D1=8,D2=7);need(evaluate(p,v,root=root)==run(old,v)['output']==0,'Inactive empty-range identity zero');counts['identity_zero_maps']+=1
  forms.append(dict(packet=p,baseline=old,expanded_polynomial=[dict(monomial=list(m),coefficient=c)for m,c in sorted(pn['output'].items())]))
 # Two tempting15-gate coordinate changes omit necessary inverse bounds.
 u,_=authenticate(root);shift_h=copy.deepcopy(u);shift_h['witnesses']=['H','k','q','s'];shift_h['source']=[r for r in shift_h['source']if r[0]!='ih'];shift_h['source'][0]=['j1','+','H',2]
 vh=dict(A=0,b=1,i=1,N=2,D=0,H=0,k=0,q=0,s=2);need(run(shift_h,vh)['sos']==0 and not any(vh['A']%(1+(j+1)*vh['b'])==vh['D']for j in range(vh['i']+1,vh['N'])),'False shifted index certificate')
 shift_s=copy.deepcopy(u);shift_s['witnesses']=['h','k','q','S'];shift_s['source']=[r for r in shift_s['source']if r[0]!='gD'];shift_s['source']=[['r1','-','g','S']if r[0]=='r1'else r for r in shift_s['source']]
 vs=dict(A=3,b=1,i=0,N=2,D=3,h=0,k=0,q=0,S=2);need(run(shift_s,vs)['sos']==0 and not any(vs['A']%(1+(j+1)*vs['b'])==vs['D']for j in range(vs['i']+1,vs['N'])),'False shifted remainder certificate')
 need(len(shift_h['source'])==len(shift_s['source'])==15,'Actual syntactic15-gate side candidates')
 def reject(fn):
  try:fn()
  except(ValueError,TypeError,KeyError):counts['rejections']+=1
  else:raise AssertionError('Bad public call accepted')
 for bad in(0,1,None,'yes',1.0):reject(lambda bad=bad:build(bad,root=root))
 p=build(root=root)
 for key in p:
  bad=copy.deepcopy(p);bad.pop(key);reject(lambda bad=bad:checked(bad,root=root))
 for key in('computed_active','full_polynomial_identity','exact_degree'):
  bad=copy.deepcopy(p);bad[key]=int(bad[key])if type(bad[key])is bool else True;reject(lambda bad=bad:checked(bad,root=root))
 for bad in(True,1.0,Fraction(1),-1):
  values={n:0 for n in p['inputs']+p['witnesses']};values['A']=bad;reject(lambda values=values:evaluate(p,values,root=root))
 values={n:0 for n in p['inputs']+p['witnesses']}
 reject(lambda:evaluate(p,values,signed=1,root=root));reject(lambda:evaluate(p,{k:v for k,v in values.items()if k!='A'},root=root));reject(lambda:evaluate(p,dict(values,foreign=0),root=root))
 for key,value in p.items():
  if type(value)in(list,dict):
   bad=build(root=root);bad[key].clear();need(exact(build(root=root),p),'Fresh defensive metadata/source copy');counts['copies']+=1
 with tempfile.TemporaryDirectory(prefix='beta_three_pins_')as d:
  d=Path(d);root=Path(root)
  for name in PINS:(d/name).write_bytes((root/name).read_bytes())
  build(root=d)
  for name in PINS:
   b=(d/name).read_bytes();(d/name).write_bytes(b+b' ')
   for fn in(lambda:build(root=d),lambda:checked(p,root=d),lambda:evaluate(p,values,root=d)):reject(fn);counts['warm_pins']+=1
   (d/name).write_bytes(b)
 proc=subprocess.run([sys.executable,'-O',str(Path(__file__).resolve())],capture_output=True,text=True,timeout=20);need(proc.returncode!=0 and'Run without -O'in proc.stderr,'Optimized guard');counts['optimized_rejections']=1
 return dict(status='PASS_BETA_THREE_QUERY_SHARING',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),parent_pins=copy.deepcopy(PINS),counts=counts,forms=forms,invalid15gate_candidates=[dict(packet=shift_h,assignment=vh,inverse_h=vh['H']-vh['i']),dict(packet=shift_s,assignment=vs,inverse_s=vs['S']-vs['D'])],scope='Two exact complete50/51-gate local query sources;12 unchanged natural witnesses. No smaller standalone suffix atom or unbounded Tree compilation claimed.')
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();r=verify(a.root)
 if a.expect:need(exact(r,json.loads(a.expect.read_text())),'Exact typed saved receipt')
 if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 print(r['status'],r['counts'])
if __name__=='__main__':main()
