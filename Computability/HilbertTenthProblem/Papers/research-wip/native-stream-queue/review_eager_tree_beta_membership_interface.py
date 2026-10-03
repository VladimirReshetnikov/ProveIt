#!/usr/bin/env python3
"""Independent bounded review of the paid Tree beta-membership interface."""
import argparse,hashlib,itertools,json,math,subprocess,sys,types
from fractions import Fraction
from pathlib import Path
if not __debug__:raise RuntimeError('Run without -O')
PINS={'Computability/HilbertTenthProblem/Lean/Diophantine/Common/DiophantineTrace.lean': 'b644241111b4ff0232d6c49838588cbcc49c44751cfaa440226f2820d4f1aa02',
 'Computability/HilbertTenthProblem/Lean/Diophantine/Common/MRDPCore.lean': 'c6f8b993f95be28b1f18e21cb82442c61d4011907f73f6725ac2f15486864c78',
 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/eager_tree_pointer_product_scout.json': '9d0eaa72ffee7c900f8e348c305293193a8b4ebaa066c534902795f6b87ba4cc',
 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/eager_tree_pointer_product_scout.md': 'c0c5991e451ae74fc9a6b9c15e996a4e2f80dd04b33d2bb2a433d03142bf47b3',
 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/eager_tree_pointer_product_scout.py': '35fab9c363c38421a2d4b569bfd56f1cddf95717f9dfaa37ada4ce7dc6fe49bd',
 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/pell_fixed_affine_exponent52.md': '891301377f3740657c268e3e48f697dc5cb5a08037665aa772c1bff0d200b9ec',
 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_eager_tree_aebfa.md': 'a8a5ff72f4e90ccb461ec77339653c4613d65dc7fc40ff98445370ee13e4ff6d',
 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_one_coordinate_aebfa.md': 'e3bcb9711921b77c4de4823b889fc1f9b1c4d790f05a6da12684067091192937',
 'Logic/PeanoArithmetic/ListCoding/Lean/PAListCoding/BoundedCipherDioph.lean': '889385240f9bbd51bf7732b85aaaf4071f3bc1904fb64af68b80763af031cbf6',
 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/canonical-diophantine-certificates/article.tex': 'e7047ec1f4708fd6497607b41c7b8e37da230ca77398933820c63ebc5a28a3ce'}
AUTHOR={
'eager_tree_beta_membership_interface.py':'bdb27b56b8701a1e392e799e742d135a4c0f107abc987982c5eb59efe947be34',
'eager_tree_beta_membership_interface.json':'de8da8729d5167aa1196d374d4603dec865a9b6ae4529747afc632576dd83f7b',
'eager_tree_beta_membership_interface.md':'b7f3ef7c12f0ae0ff14cd49ec57802b06d6842bd5b30bc044397d02866a115e3',
}
WIP='Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/'
def need(ok,msg):
 if not ok:raise ValueError(msg)
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys()and all(exact(a[k],b[k])for k in a)
 if type(a)is list:return len(a)==len(b)and all(exact(x,y)for x,y in zip(a,b))
 return a==b
def sha(b):return hashlib.sha256(b).hexdigest()
def pins(root,manifest):
 out={}
 for n,h in manifest.items():
  b=(Path(root)/n).read_bytes();need(sha(b)==h,'Pinned blob '+n);out[n]=b
 return out

def run(rows,v):
 e=dict(v)
 for name,op,a,b in rows:
  a=e[a]if type(a)is str else a;b=e[b]if type(b)is str else b
  e[name]=a*b if op=='*'else a+b if op=='+'else a-b
 return e

class Ring:
 def __init__(self,names):self.names=names;self.zero=(0,)*len(names)
 def atom(self,x):
  if type(x)is int:return {self.zero:x}if x else{}
  v=list(self.zero);v[self.names.index(x)]=1;return {tuple(v):1}
 def add(self,a,b,sign=1):
  out=dict(a)
  for e,c in b.items():out[e]=out.get(e,0)+sign*c
  return {e:c for e,c in out.items()if c}
 def mul(self,a,b):
  out={}
  for u,c in a.items():
   for v,d in b.items():e=tuple(x+y for x,y in zip(u,v));out[e]=out.get(e,0)+c*d
  return {e:c for e,c in out.items()if c}
 def source(self,rows):
  e={n:self.atom(n)for n in self.names}
  for n,o,a,b in rows:
   a=e[a]if type(a)is str else self.atom(a);b=e[b]if type(b)is str else self.atom(b)
   e[n]=self.mul(a,b)if o=='*'else self.add(a,b,1 if o=='+'else -1)
  return e
 def serialize(self,p):return [[list(e),c]for e,c in sorted(p.items())]

def inspect(p):
 known=set(p['inputs']+p['witnesses']);defs={};M=0
 for row in p['source']:
  need(type(row)is list and len(row)==4,'literal binary row');n,o,a,b=row
  need(type(n)is str and n not in known and o in('+','-','*'),'fresh arithmetic gate')
  need(all(type(x)is int or type(x)is str and x in known for x in(a,b)),'source closure/exact numeral')
  known.add(n);defs[n]=(a,b);M+=o=='*'
 live=set();todo=[p['output']]
 while todo:
  n=todo.pop()
  if type(n)is int or n in live:continue
  live.add(n);todo.extend(defs.get(n,()))
 need(known<=live,'every gate and supplied coordinate live')
 return M,len(p['source'])-M

def beta(A,b,j):return A%(1+(j+1)*b)
def lift(A,b,i,N,D,j):return dict(h=j-i-1,k=N-j-1,q=A//(1+(j+1)*b),s=(j+1)*b-D)
def code(x,y,z):return (z+((x+y)**2+x))**2+z

def verify(repo,artifacts):
 original=pins(repo,PINS);author=pins(artifacts,AUTHOR);saved=json.loads(author['eager_tree_beta_membership_interface.json'])
 need(exact(saved['pins'],PINS)and saved['source_sha256']==AUTHOR['eager_tree_beta_membership_interface.py'],'receipt provenance')
 path=Path(artifacts)/'eager_tree_beta_membership_interface.py';mod=types.ModuleType('_authenticated_beta_author');mod.__file__=str(path)
 exec(compile(author[path.name],str(path),'exec'),mod.__dict__)
 need(len(saved['forms'])==2,'two exact local forms')
 counts=dict(complete_polynomial_identities=0,paid_live_gates=0,residual_identities=0,natural_assignments=0,natural_zeros=0,all_member_lifts=0,active_checks=0,crt_encodings=0,coherence_counterexamples=0,source_fixture_atoms=0,domain_counterexamples=0,guard_rejects=0,defensive_copies=0)
 forms=[]
 for active in(False,True):
  p=mod.build(active);f=saved['forms'][int(active)];need(exact(p,f['packet']),'actual build matches frozen literal source')
  inputs=['A','b','i','N','D']+(['active']if active else[]);witnesses=['h','k','q','s']
  need(p['inputs']==inputs and p['witnesses']==witnesses and p['residuals']==['r0','r1','r2'],'entire scalar interface')
  ring=Ring(inputs+witnesses);v={n:ring.atom(n)for n in ring.names};a=ring.add;m=ring.mul;num=ring.atom
  t=a(a(v['i'],v['h']),num(2));bjt=m(v['b'],t)
  r0=a(a(v['A'],v['D'],-1),m(v['q'],a(bjt,num(1))),-1)
  r1=a(a(bjt,v['D'],-1),v['s'],-1);r2=a(a(v['N'],t,-1),v['k'],-1)
  expected=a(a(m(r0,r0),m(r1,r1)),m(r2,r2))
  if active:expected=m(v['active'],expected)
  e=ring.source(p['source'])
  for name,want in zip(p['residuals'],[r0,r1,r2]):need(e[name]==want,'hand-derived local residual');counts['residual_identities']+=1
  need(e[p['output']]==expected,'whole emitted coefficient identity');M,A=inspect(p)
  need((M,A)==(5+active,11)and (M,A)==(f['M'],f['A']),'every paid operation')
  degree=max(sum(x)for x in expected);need(degree==6+active==f['degree'],'exact formal degree')
  lead={x:c for x,c in expected.items()if sum(x)==degree}
  wantlead=m(m(v['b'],v['q']),a(v['i'],v['h']));wantlead=m(wantlead,wantlead)
  if active:wantlead=m(v['active'],wantlead)
  need(lead==wantlead,'exact independent leading polynomial')
  savedpoly={}
  for term in f['polynomial_terms']:
   vv=[0]*len(ring.names)
   for name in term['monomial']:vv[ring.names.index(name)]+=1
   need(tuple(vv)not in savedpoly,'no repeated monomial');savedpoly[tuple(vv)]=term['coefficient']
  need(savedpoly==expected,'entire saved coefficient receipt')
  counts['complete_polynomial_identities']+=1;counts['paid_live_gates']+=M+A
  forms.append(dict(active=active,M=M,A=A,operations=M+A,degree=degree,variables=ring.names,polynomial=ring.serialize(expected),leading_form=ring.serialize(lead)))
 plain=mod.build(False);guarded=mod.build(True)
 for A,b,i,N,D in itertools.product(range(4),range(3),range(2),range(4),range(3)):
  base=dict(A=A,b=b,i=i,N=N,D=D);members=[j for j in range(i+1,N)if beta(A,b,j)==D]
  for h,k,q,s in itertools.product(range(3),repeat=4):
   value=dict(base,h=h,k=k,q=q,s=s);env=run(plain['source'],value);res=[env[r]for r in plain['residuals']];out=env[plain['output']]
   need(out==sum(r*r for r in res)>=0,'literal natural sum of squares')
   if out==0:
    j=i+h+1;need(j in members and exact(value,dict(base,**lift(A,b,i,N,D,j))),'zero forces canonical quotient/slacks and suffix index');counts['natural_zeros']+=1
   counts['natural_assignments']+=1
  for j in members:
   w=lift(A,b,i,N,D,j);need(min(w.values())>=0 and run(plain['source'],dict(base,**w))[plain['output']]==0,'explicit member extension');counts['all_member_lifts']+=1
 for A,b,i,N,D in itertools.product(range(3),range(2),range(3),range(4),range(3)):
  val=dict(A=A,b=b,i=i,N=N,D=D,h=1,k=0,q=2,s=3);S=run(plain['source'],val)[plain['output']]
  for active in range(4):
   y=run(guarded['source'],dict(val,active=active))[guarded['output']];need(y==active*S>=0 and (y==0)==(active==0 or S==0),'natural active interface');counts['active_checks']+=1
 # Independent simultaneous CRT witness via the closed product formula, not the author's incremental routine.
 crt=[]
 for N in range(9):
  for shape in range(3):
   values=[(i*i+3*shape*i+shape)%19 for i in range(N)];b=math.factorial(N)*(1+max(values,default=0));ms=[1+(j+1)*b for j in range(N)]
   need(all(math.gcd(x,y)==1 for i,x in enumerate(ms)for y in ms[i+1:]),'pairwise coprime actual moduli');P=math.prod(ms)
   A=sum(v*(P//q)*pow(P//q,-1,q)for v,q in zip(values,ms))%P
   need(all(beta(A,b,j)==v for j,v in enumerate(values)),'independent CRT encoding');counts['crt_encodings']+=1
   crt.append(dict(values=values,A=A,b=b))
 # Reconstruct the literal parent counterexample independently of the author's saved fixture.
 parent=json.loads(original[WIP+'eager_tree_pointer_product_scout.json']);tree=next(f['packet']for f in parent['forms']if f['packet']['N']==3 and f['packet']['cleanup'])
 values={n:0 for n in tree['free']};values.update(program=4,argument=0,output=0,r0_x=4,r0_u=1,r0_v=1,r0_t3=1,r1_z=1,r1_t0=1,r2_z=1,r2_t0=1)
 env=run(tree['polynomial_source'],values);actual=[code(values[f'r{j}_x'],values[f'r{j}_y'],values[f'r{j}_z'])for j in range(3)]
 need(actual==[400,2,2]and all(env[r]==0 for r in tree['residuals'][:18]),'all literal local/root rows zero')
 need(env[tree['output']]==279841,'full pointer-product source correctly rejects')
 root_targets=[env[s['target_port']]for s in tree['slot_map'][:3]];need(root_targets==[2,2,25],'actual root target codes')
 fake=[400,2,25];b=math.factorial(3)*(max(fake)+1);ms=[1+(j+1)*b for j in range(3)];P=math.prod(ms);A=sum(v*(P//q)*pow(P//q,-1,q)for v,q in zip(fake,ms))%P
 atoms=[]
 for slot in tree['slot_map']:
  i=slot['row'];active=env[slot['active_port']];D=env[slot['target_port']]if slot['target_port']else 0
  w=lift(A,b,i,3,D,next(j for j in range(i+1,3)if fake[j]==D))if active else dict(h=0,k=0,q=0,s=0)
  val=dict(A=A,b=b,i=i,N=3,D=D,active=active,**w)
  need(min(val.values())>=0 and run(guarded['source'],val)[guarded['output']]==0,'counterfeit actual active query');counts['source_fixture_atoms']+=1;atoms.append(val)
 need(code(1,1,0)==25 and (0+1)*(0+1+1)+2*1+2==6,'direct Tree app(4,0)=app(1,1)=6')
 savedcounter=saved['unlinked_code_counterexample'];need(exact(savedcounter['tree_assignment'],values)and savedcounter['actual_codes']==actual and savedcounter['unlinked_codes']==fake and savedcounter['true_output']==6,'saved counterexample fully checked')
 counts['coherence_counterexamples']=1
 signed=dict(A=0,b=1,i=0,N=2,D=3,h=0,k=0,q=-1,s=-1);rational=dict(A=1,b=1,i=0,N=2,D=0,h=0,k=0,q=Fraction(1,3),s=2)
 for val in(signed,rational):
  need(run(plain['source'],val)[plain['output']]==0 and beta(val['A'],val['b'],1)!=val['D'],'actual signed/nonnegative-real failure');counts['domain_counterexamples']+=1
 need((6-2)*(6-3)%6==0 and 0 not in[2,3],'composite divisibility shortcut fails')
 counts['divisibility_counterexamples']=1
 for bad in(0,1,None,'true',1.0):
  try:mod.build(bad)
  except AssertionError:counts['guard_rejects']+=1
  else:raise ValueError('inexact active flag accepted')
 p=mod.build();p['source'].clear();need(len(mod.build()['source'])==16,'new local source per call');counts['defensive_copies']+=1
 proc=subprocess.run([sys.executable,'-O',str(path)],capture_output=True,text=True,timeout=30);need(proc.returncode!=0 and'Run without -O'in proc.stderr,'optimized source rejection')
 counts['optimized_rejections']=1
 return dict(status='PASS_INDEPENDENT_TREE_BETA_MEMBERSHIP_INTERFACE',review_source_sha256=sha(Path(__file__).read_bytes()),author_pins=AUTHOR,predecessor_pins=PINS,counts=counts,forms=forms,independent_crt_examples=crt,counterexample=dict(values=values,actual_codes=actual,fake_codes=fake,code_A=A,code_b=b,actual_parent_output=env[tree['output']],actual_Tree_output=6,active_query_assignments=atoms),scope='Complete local scalar16/17 gate membership atoms and literal natural coherence obstruction. Existing bounded-universal proofs read, not rebuilt or exported. No paid complete fixed-arity Tree compiler claimed.')
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--repo',type=Path,required=True);ap.add_argument('--artifacts',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();out=verify(a.repo,a.artifacts)
 if a.expect:need(exact(out,json.loads(a.expect.read_text())),'exact independent saved receipt')
 if a.output:a.output.write_text(json.dumps(out,sort_keys=True,indent=2)+'\n')
 print(out['status'],out['counts'])
if __name__=='__main__':main()
