#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign26-zero-extraction-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'778328a208b2af1702dd9787d6e260b75739db130941b5a1e4b28548ca25b96d','source-manifest.json':'f29953bda76305d208ad0577835584f84c2fe36a8eb72169d5af4adcea41f960','src/DiophantineConsistency/Sign26ZeroExtraction.lean':'8ba3c1255b86fa2ba05925f56a5312f344d09cb72b042cd34a573d980f772784'}.items():assert H(P/n)==h
m=json.loads((P/'source-manifest.json').read_text())['rows'];assert len(m)==1 and m[0]['imports']==['DiophantineConsistency.SharingSign26Squares'];s=(P/'src/DiophantineConsistency/Sign26ZeroExtraction.lean').read_text();assert H(D/'research/nine-sharing-sign26-zero-extraction-draft/Sign26ZeroExtraction.lean')==m[0]['source_sha256']
seed=(D/'research/nine-sharing-sign26-sextic-lean-draft/SharingSeed26Sextic.lean').read_text();block=seed.split('def remainingResiduals ',1)[1].split('\n  [\n',1)[1].split('\n  ]',1)[0];rows=[x.strip().removesuffix(',') for x in block.splitlines()];nt=s.split('def ntResidual ',1)[1].split(':=\n',1)[1].split('\n',1)[0].strip();assert len(rows)==16 and nt==rows[9] and 'remainingResiduals p).drop 9' in s
for x in ['SharingSign26Squares.seed_zero_iff_residuals p v','theorem q3_eq','ι (v 15) =','theorem nt_eq','((p 1 : ℤ) : DiffRing V)','ι (v 9) + 1','ι (v 4) *','(p 0 : ℤ) : DiffRing V','[V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]']:assert x in s
# Exact integer polynomial normalization: Hq+q−(H(n+t)+n+(x+1)a)−1 = H(q−n−t)−n−xa for q=a+1.
def add(x,y):
 z=x.copy()
 for k,v in y.items():z[k]=z.get(k,0)+v
 return {k:v for k,v in z.items() if v}
def neg(x):return {k:-v for k,v in x.items()}
def sub(x,y):return add(x,neg(y))
def mul(x,y):
 z={}
 for a,u in x.items():
  for b,v in y.items():
   k=tuple(c+d for c,d in zip(a,b));z[k]=z.get(k,0)+u*v
 return {k:v for k,v in z.items() if v}
one={(0,0,0,0,0):1};a,h,n,t,x=[{tuple(int(i==j) for i in range(5)):1} for j in range(5)];q=add(a,one);lhs=sub(sub(add(mul(h,q),q),add(add(mul(h,add(n,t)),n),mul(add(x,one),a))),one);rhs=sub(sub(mul(h,sub(sub(q,n),t)),n),mul(x,a));assert lhs==rhs
up=D/'reviews/nine-sharing-sign26-seed-squares-terminal-frontier-independent/check.py';assert H(up)=='a60bbcc769f385fd2ac4ac843ad661fa13a9668567e7f15157d3de4fa207911d';subprocess.run([sys.executable,'-I','-S','-B',str(up)],capture_output=True,check=True,timeout=120)
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','scope':'q3 and Nt ring equalities from sign26 seed zero only; symbolic ports, no positivity/representability or Lean replay'},sort_keys=True,indent=2))
