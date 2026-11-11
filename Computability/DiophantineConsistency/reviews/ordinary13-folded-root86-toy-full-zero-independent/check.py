#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from collections import defaultdict
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
base=Path(__file__).resolve().parents[2];repo=base.parents[1];p=base/'research/ordinary13-folded-root86-toy-full-zero'
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'check.py':'daf016eeb1f475b6c1783eeff9fc2ac780962189acc6dee64c50fb6e0d3fc6b9','result.json':'ed19c59bafa01af942a3b3a36ac9072036aa12a8963ce1739092ec0bf140cd75'}.items():assert sha(p/n)==h
# Only the exact post-review link is removed in memory; separately pin the
# final README and the original mathematical bytes independently reviewed.
readme=(p/'README.md').read_bytes()
assert hashlib.sha256(readme).hexdigest()=='ce7d50e76f3b035f7fc87ad0228327be9da41d28455e231610f2bd780f473693'
tail=(b'\nIndependent external review is recorded in\n'
      b'`../../reviews/ordinary13-folded-root86-toy-full-zero-independent/`.\n')
assert readme.endswith(tail)
assert hashlib.sha256(readme[:-len(tail)]).hexdigest()=='a09bc169746bba112ce3f8ac4eea211b09a851362d30ce693e086c9652bf8d45'
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],cwd=repo,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=120);assert not r.stderr and r.stdout==(p/'result.json').read_bytes()
source=base/'research/ordinary13-four-square88-30/candidate.json';folded=base/'research/ordinary13-folded-root86-probe/candidate.json';free=base/'research/current14-carrier64-free-s-toy-zero';floor=base/'reviews/current14-carrier64-pell-floor-independent/check.py';toy=base/'reviews/current14-carrier64-toy-full-zero-independent/check.py';foldreview=base/'reviews/ordinary13-folded-root86-probe-independent/check.py'
for q,h in [(source,'daaae50a0837b0b79d2d911daad222664194407e94522154e655a1b1a3cfd420'),(folded,'e44c211efa0f124dc00414a475b2dca0d576117aaed7f4a371aa5a687be0a540'),(free/'README.md','8e972356745c9ba5a6e72a322f0d603a3d22bcbdba4af6b9325725430fd26b11'),(free/'check.py','364eabe29ba99a665337861ba532aa3b6117a4b8f803d686b945d751049a6458'),(floor,'65ff9800b15d3313eaecb3f595851f355f9e7b0c8f811afd46187cc95c9f6839'),(toy,'11accf4b23357c66bd7160cd753be7198d5f1d905706fbf29871b7bb7e4c83c1'),(foldreview,'b0896aa3f87844a7ecdee11ff2d2100f62a38982dc7094fb331762de3dc580bc')]:assert sha(q)==h
# Check the finite seed controls and the general Pell/floor and Chebyshev
# review receipts; these do not expand the symbolic full witness.
for q,result in [(free/'check.py',free/'result.json'),(floor,base/'reviews/current14-carrier64-pell-floor-independent/result.json'),(toy,base/'reviews/current14-carrier64-toy-full-zero-independent/result.json')]:
 run=subprocess.run([sys.executable,'-I','-S','-B',str(q)],cwd=repo,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=180);assert not run.stderr and json.loads(run.stdout)==json.loads(result.read_text())
g=json.loads(source.read_text());rows=g['source'];sourceby={r[0]:r for r in rows}
for row in [['qm','*','J','beta'],['q','+',1,'qm'],['q2','*','q','q'],['q3','*','q','q2'],['U','*','Y','q2'],['qF','-','q','F'],['C','-','qF','alpha'],['E','*','X','Y'],['k','+','eta','zeta'],['kY','*','Y','k'],['c','+','eta','kY'],['ell','*','E','kY'],['M','*','q3','qm'],['Bt','-','g27','g28'],['folded_kBt','*','k','Bt'],['folded_g31','-','g31','folded_kBt'],['Z','-','g34','folded_q3Bt'],['g54','*','U','gamma'],['g55','*','E','q'],['shift','-','g56','r0'],['Dstar','+','g58','g59'],['g63','*','Delta','c2'],['A1','-','g61','g65'],['Q','*','Delta','rho'],['I','*','c2','i'],['g72','-','g71','Q'],['V','-','g76','c'],['g78','+','V','u'],['Fa','-','y2','g82'],['Fam','-','Fa',1],['out','+','sum01','sum23']]:assert sourceby[row[0]]==row
assert [z[0] for z in rows if 'r' in z[2:]]==['g31'] and [z[0] for z in rows if 'gamma' in z[2:]]==['g54']
# Fixed scalars and modular transport are finite and independently computed.
beta,K,MC,MF,J,F,alpha=31,9,14,46,1,1,14;q=1+beta*J;C=q-F-alpha;gap=beta*(q-F)+alpha;R=gap*(q*q-1)+J*(MC+q*MF);N=(R-1)//2
assert (q,C,gap,R,N)==(32,17,975,998911,499455) and R%4==3 and R.bit_count()==17 and N.bit_count()-1==15
assert 0<MC<beta<MF<2*beta and pow(2,R-5,beta)==2 and ((K+pow(2,R-5,beta))*C-F)%beta==0
assert R>20 and N>=13 and (1<<40)>136*q**3 and (1<<20)>9
# First-root and main-carrier equations from the actual 88-row graph are
# evaluated over a free multivariate integer polynomial ring at the stated cuts.
def at(s):return {(s,):1}
def add(a,b,s=1):
 z=defaultdict(int,a)
 for k,v in b.items():z[k]+=s*v
 return {k:v for k,v in z.items() if v}
def mul(a,b):
 z=defaultdict(int)
 for x,u in a.items():
  for y,v in b.items():z[tuple(sorted(x+y))]+=u*v
 return {k:v for k,v in z.items() if v}
one={():1};names=('q3','b','t','s','tau','ell','k');v={n:at(n) for n in names};v['qm']=v['b'];v['Y']=mul(v['q3'],v['s']);v['Bt']=mul(v['b'],v['t']);v['M']=mul(v['q3'],v['b']);v['r']=add(add(add(add(add(mul(v['k'],v['Bt']),v['tau']),v['ell'],-1),v['k'],-1),v['s'],-1),v['t'])
def eval_available(vals):
 for n,op,a,b in rows:
  if n in vals:continue
  A=({():a} if a else {}) if type(a)==int else vals.get(a);B=({():b} if b else {}) if type(b)==int else vals.get(b)
  if A is not None and B is not None:vals[n]=mul(A,B) if op=='*' else add(A,B,1 if op=='+' else -1)
 return vals
v=eval_available(v);assert v['Z']==mul(v['M'],v['tau'])
assert v['A0']==mul(mul(v['M'],v['M']),add(add(mul(v['tau'],v['tau']),one,-1),mul(v['ell'],add(v['ell'],v['k'])),-1))
# In the main carrier E*q=U*w when X=q*w, U=Y*q². The gamma shift
# supplies U*gamma=U*gamma0−U*w+(k−R−1), with no division in this check.
names=('U','w','gamma0','k','R','X','a','c','H');v={n:at(n) for n in names};v['g54']=add(add(add(mul(v['U'],v['gamma0']),mul(v['U'],v['w']),-1),v['k']),add(v['R'],one),-1);v['g55']=mul(v['U'],v['w']);v=eval_available(v)
D0=add(add(v['X'],mul(v['a'],v['c'])),mul(v['H'],v['gamma0']));assert v['shift']==mul(v['U'],v['gamma0']) and v['Dstar']==mul(v['U'],D0)
delta=add(mul(v['a'],v['a']),v['H']);assert v['A1']==mul(mul(v['U'],v['U']),add(add(mul(D0,D0),one,-1),mul(delta,mul(v['c'],v['c'])),-1))
# Strong/auxiliary equalities are identities conditional on the Pell norms.
v={n:at(n) for n in ('Delta','f2','I','V','u')};v=eval_available(v);y=add(v['V'],v['u']);assert v['g72']==add(mul(v['I'],v['I']),mul(v['Delta'],add(v['f2'],one,-1)),-1)
assert v['Fam']==add(add(mul(y,y),mul(mul(v['Delta'],add(v['f2'],one,-1)),add(mul(y,y),mul(v['V'],v['V']),-1)),-1),one,-1)
# Independent exact controls for c-th main-unit powers and odd-index auxiliary
# units; the enormous R=998911 witness is intentionally not expanded.
def pmul(a,b,D):return (a[0]*b[0]+D*a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def power(a,n,D):
 z=(1,0)
 while n:
  if n&1:z=pmul(z,a,D)
  a=pmul(a,a,D);n//=2
 return z
for A,R0 in [(2,3),(2,7),(3,3),(4,3)]:
 D=A*A-1;D0,c=power((A,1),R0,D);f,L=power((D0,c),c,D);assert L%(c*c)==0 and f*f-D*L*L==1
 S=D*L;x,y=power((S,1),R0,S*S-1);assert x%S==0;V=x//S
 assert (V+c)%(f*f)==0 and (V+R0)%c==0 and (f*f-1)%c==0
 T,rem=divmod(V+c+f*f*R0,c*f*f);assert rem==0 and T>0 and V>1 and y>V and y*y-S*S*(y*y-V*V)==1
print(json.dumps({'status':'PASS_SCOPED_SYMBOLIC_REVIEW','author_receipt_reproduced':True,'toy_ports':[beta,K,MC,MF],'rank':R,'coordinate_root_signs':'both negative, fixed other twelve coordinates','actual_pell_witness_expanded':False,'scope':'Toy-port full symbolic zero conditional on reviewed general Pell/floor arguments; no actual-port zero, Lean or unrestricted existential nonequivalence.'},indent=2))
