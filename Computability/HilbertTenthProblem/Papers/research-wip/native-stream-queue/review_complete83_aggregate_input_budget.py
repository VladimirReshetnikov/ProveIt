#!/usr/bin/env python3
"""Fresh independent metadata, source-polynomial and aggregate-budget checks."""
import argparse
import hashlib
import json
import math
from pathlib import Path
STEM=Path('/tmp/complete83_aggregate_input_budget')
BASE=Path('/home/codex/.codex/worktrees/2a71/Proofs/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue')
PINS={'md':'803c6d47b503d611a641b456da3887a46a300c55023dfd1e2a7120de5299903f','py':'07c7acb10810b43f7198a63b2bc465c3a59b5dfde38aa9123eb31d016999c8d7','json':'19b5f15b30f99cd6913214eff22366d3417ab4251aa509a018f662e0a5104602'}
def need(v,m):
 if not v:raise ValueError(m)
def sha(b):return hashlib.sha256(b).hexdigest()
def val(n,p):
 need(n!=0,'valuation zero');n=abs(n);v=0
 while n%p==0:n//=p;v+=1
 return v
def fac(n):
 out={};p=2
 while p*p<=n:
  while n%p==0:out[p]=out.get(p,0)+1;n//=p
  p+=1
 if n>1:out[n]=out.get(n,0)+1
 return out
def carries(n,p):
 carry=ans=0
 while n or carry:
  n,digit=divmod(n,p);carry=(digit*2+carry)//p;ans+=carry
 return ans
class Poly:
 def __init__(self,x):self.v=x if isinstance(x,dict) else ({():x} if x else {})
 @staticmethod
 def atom(x):return Poly({(x,):1})
 def __add__(self,y):
  if not isinstance(y,Poly):y=Poly(y)
  out=dict(self.v)
  for mon,c in y.v.items():out[mon]=out.get(mon,0)+c
  return Poly({m:c for m,c in out.items() if c})
 __radd__=__add__
 def __neg__(self):return Poly({m:-c for m,c in self.v.items()})
 def __sub__(self,y):return self+-y if isinstance(y,Poly) else self+(-y)
 def __rsub__(self,y):return -self+y
 def __mul__(self,y):
  if not isinstance(y,Poly):y=Poly(y)
  out={}
  for a,c in self.v.items():
   for b,d in y.v.items():
    mon=tuple(sorted(a+b));out[mon]=out.get(mon,0)+c*d
  return Poly({m:c for m,c in out.items() if c})
 __rmul__=__mul__
 def __eq__(self,y):return self.v==(y.v if isinstance(y,Poly) else Poly(y).v)

def source_check(raw):
 packet=json.loads(raw)['packet'];source=packet['source'];rows={r[0]:r for r in source}
 names='Bm1 Jrep K d2 x0 T k z b MC MF w V'.split();p={n:Poly.atom(n) for n in names}
 q=p['Bm1']*p['Jrep']+1;x=p['x0']+p['T']*p['k'];ell=p['d2']*p['T'];S0=q-(p['K']+2)*p['z']-p['d2']*p['x0']
 env={'Bm1':p['Bm1'],'Jrep':p['Jrep'],'Kconstant':p['K'],'twice_cell_bits':p['d2'],'inner_bits':p['b'],
      'Z':p['z'],'F':p['K']*p['z'],'alpha':S0-ell*p['k'],'x':x,'MC':p['MC'],'MF':p['MF'],'w':p['w'],'transport_quotient':p['V']}
 used=set()
 def get(n):
  if type(n) is int:return Poly(n)
  if n not in env:
   _,op,a,b=rows[n];a,b=get(a),get(b)
   env[n]=a+b if op=='+' else a-b if op=='-' else a*b;used.add(n)
  return env[n]
 need(get('q')==q,'literal q')
 need(get('marked_rhs')==p['z'] and get('W')==0,'exact C and zero offset')
 need(get('odd_index')==p['d2']*x+p['b'],'exact exponent increment')
 q2=q*q
 R=q2*q2-p['K']*p['z']*q2*q-(p['z']+1)*q2+p['K']*p['z']*q+p['z']+(p['MC']+q*p['MF'])*p['Jrep']
 need(get('r_lhs')==R,'literal R including constant z')
 need(all('k' not in m for m in R.v),'R invariant throughout progression')
 need(get('norm_transport')==1+p['z']*p['w']-(p['V']-1)*(q-1),'literal transport')
 need(len(source)==83 and len(packet['witnesses'])==18 and packet['ordinary_input']=='x','unchanged source interface')
 return {'ancestor_count':len(used),'ancestor_names':sorted(used),'complete_source_rows':83,'witnesses':18,'method':'exact sparse integer polynomials under actual supplied-port substitution','full_source_evaluated':False}

def endpoints():
 n=0;nonuniform=0
 for ell in [1,2,3,7,16,31,60]:
  for j in range(0,61):
   for delta in [-1,0,1,ell-1]:
    S=ell*j+delta
    if S<=0:continue
    Kmax=(S-1)//ell;N=(S+ell-1)//ell
    need(N==Kmax+1 and S-ell*Kmax>0 and S-ell*(Kmax+1)<=0,'endpoint')
    for H in sorted(set([1,2,max(1,N-1),N,N+1,2*N+3])):
     accepted=[]
     for k0 in range(H):
      candidates=[k0+t*H for t in range(N//H+2)]
      works=any(S-ell*k>0 for k in candidates)
      need(works==(k0<=Kmax),'least representative iff')
      accepted.append(works);n+=1
     need(all(accepted)==(H<=N)==(ell*(H-1)<S),'uniform all-residues iff')
     nonuniform+=int(not all(accepted) and any(accepted))
 return {'CRT_classes':n,'particular_fit_without_uniform_guarantee':nonuniform,'near_endpoint_data':'S=ell*j+delta, ell in 1,2,3,7,16,31,60; j=0..60; delta=-1,0,1,ell-1'}

def cap_and_carry():
 algebra=0
 for a in range(1,13):
  for tau in range(0,2*a+4):
   for extra in range(0,3*a+4):
    c=a+tau+extra;g=min(tau,2*a);e=min(extra,max(2*a-tau,0));lam=max(3*a-c,0)
    need(g+e+lam==2*a and g+e==min(2*a,c-a),'capped exponent and gcd identity');algebra+=1
 records=above=0
 for r in range(1001,1802,2):
  C=math.comb(2*r,r);odd=(r+1)//(2**val(r+1,2));f=fac(odd)
  divisors=[1]
  for p,b in f.items():divisors=[d*p**e for d in divisors for e in range(b+1)]
  for A in divisors:
   if A==1:continue
   H=G=E=1
   for p,a in fac(A).items():
    b=val(r+1,p);h=(r+1)//p**b;c=carries(r,p);extra=carries(h,p)
    need(c==val(C,p)==b+extra,'independent carry identity')
    tau=b-a;H*=p**max(3*a-c,0);G*=p**min(tau,2*a);E*=p**min(extra,max(2*a-tau,0))
   need(H*G*E==A*A and G*E==math.gcd(A*A,C//A) and H==A**3//math.gcd(A**3,C),'whole capped gcd')
   records+=1;above+=H>A
 return {'formal_exponent_cases':algebra,'new_binomial_records':records,'H_greater_than_A':above,'r_odd_interval':[1001,1801],'carry_method':'direct base-p addition carry count, independently compared to exact math.comb valuations'}

def local_case(doc):
 r,R,u0,ell,q=503,1007,5,6,42;A=21;C=math.comb(2*r,r)
 c={p:val(C,p) for p in [3,7]};b={p:val(pow(2,ell)-1,p) for p in [3,7]}
 H=math.prod(p**max(3-c[p],0) for p in c)
 need(H==49 and c=={3:4,7:1} and b=={3:2,7:1},'local depth')
 p=7;depth=b[p];h=(r+1)//p**depth;root=h%p
 def F(y):return h*(r+2)+r*(r+2)*y+r*(r-1)*p**depth*y*y
 derivative=(r*(r+2)+2*r*(r-1)*p**depth*root)%p
 root+=p*((-F(root)//p)*pow(derivative,-1,p)%p)
 need(F(root)%49==0,'independent Newton root')
 mod=7**3;images=[];hits=[]
 for k in range(H):
  X=(pow(2,R,mod)-pow(2,u0+ell*k,mod))%mod
  need(X%7==0,'exact normalization');image=X//7;images.append(image)
  if F(image)%49==0:hits.append(k)
 need(len(set(images))==H and hits==[25],'unique CRT input class')
 k0=hits[0];u=u0+ell*k0;modulus=2*q**3;X=(pow(2,R,modulus)-pow(2,u,modulus))%modulus
 coefficient=C;total=0;power=1
 for j in range(r+1):
  total=(total+coefficient*power)%modulus;power=power*X%modulus
  if j<r:coefficient=coefficient*(r-j)//(r+j+1)
 need(total==0 and ell*k0>q,'full local sum and actual-q slack obstruction')
 saved=doc['local_example']
 for key,v in [('Hreq',H),('k0',k0),('local_root',root),('residue_images',images),('M_mod_2q3',total),('u',u)]:need(saved[key]==v,'author local record '+key)
 # With the same congruence class, the abstract sharp slack threshold is151,
 # while a uniform guarantee for every class would require289.
 need(150-ell*k0==0 and 151-ell*k0==1 and ell*(H-1)+1==289,'particular versus uniform endpoints')
 return {'r':r,'Hreq':H,'A':A,'k0':k0,'root_mod_49':root,'u':u,'summed_terms':r+1,'M_mod_2q3':total,'particular_minimum_S0':151,'uniform_minimum_S0':289,'synthetic_slack_only':True,'actual_compiler':False}

def sufficient_bound():
 n=0
 for A in range(3,1002,2):
  for sign in [-1,1]:
   q=A*(A+sign)//2;need(3*q>=A*A,'shape lower bound')
   for ell in [1,7,31,121]:
    for G in [g for g in range(1,A+1) if A*A%g==0 and g>=6*ell]:
     H=A*A//G;S=q//2+1
     need(ell*H<S and ell*(H-1)<S,'aggregate sufficient threshold');n+=1
 return {'integer_bound_checks':n,'odd_A_range':[3,1001],'both_shapes':True}

def build():
 author={}
 for ext,pin in PINS.items():
  raw=Path(str(STEM)+'.'+ext).read_bytes();need(sha(raw)==pin,'author pin '+ext);author[ext]={'sha256':pin,'bytes':len(raw)}
 doc=json.loads(Path(str(STEM)+'.json').read_text());dependencies=[]
 for d in doc['dependencies']:
  path=BASE/d['name']
  if not path.exists():path=Path('/tmp')/d['name']
  raw=path.read_bytes();need(sha(raw)==d['sha256'] and len(raw)==d['bytes'],'dependency pin '+d['name']);dependencies.append(d)
 return {'schema':'independent aggregate-input-budget review v1','reviewer_sha256':sha(Path(__file__).read_bytes()),'author':author,'dependencies':dependencies,
 'source':source_check((BASE/'complete83_shared_projection_scout.json').read_bytes()),'endpoints':endpoints(),'capped_carries':cap_and_carry(),'local_deep_lift':local_case(doc),'sufficient_bound':sufficient_bound(),
 'scope':{'author_or_predecessor_program_execution':False,'actual_compiler_zero':False,'automatic_carry_or_binary_condition':False,'fresh_full_source_degree_audit':False}}
def main():
 ap=argparse.ArgumentParser();g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--output');g.add_argument('--expect');a=ap.parse_args();result=build();raw=(json.dumps(result,indent=2,sort_keys=True)+'\n').encode()
 if a.output:
  with open(a.output,'xb') as f:f.write(raw)
 else:need(raw==Path(a.expect).read_bytes(),'exact receipt replay')
 print(json.dumps({'status':'PASS','source_rows':result['source']['ancestor_count'],'CRT_classes':result['endpoints']['CRT_classes'],'carry_records':result['capped_carries']['new_binomial_records'],'local_terms':result['local_deep_lift']['summed_terms']}))
if __name__=='__main__':main()
