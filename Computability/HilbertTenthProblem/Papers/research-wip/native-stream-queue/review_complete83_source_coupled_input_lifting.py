#!/usr/bin/env python3
"""Independent fresh review evidence; all author/predecessor programs are inert."""
import argparse
import hashlib
import json
import math
from pathlib import Path
STEM=Path('/tmp/complete83_source_coupled_input_lifting')
PINS={'py':'2d95450b60f1c480a5f9145b20e167567bc18ea984778d5c334b8c082043f2cd','json':'cca7826dcc53c508cf16ecf8e5d3ddec006fbb707ee6dba23fcd19c083d0d93b','md':'822d192578f379e1e81a00caafbb3612db24989902411748f35ee23343d5934f'}
BASE=Path('/home/codex/.codex/worktrees/2a71/Proofs/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue')
def need(c,m):
 if not c:raise ValueError(m)
def sha(x):return hashlib.sha256(x).hexdigest()
def vp(n,p):
 need(n!=0,'valuation domain');n=abs(n);a=0
 while n%p==0:a+=1;n//=p
 return a
def factors(n):
 out={};p=2
 while p*p<=n:
  while n%p==0:out[p]=out.get(p,0)+1;n//=p
  p=3 if p==2 else p+2
 if n>1:out[n]=out.get(n,0)+1
 return out
def central(r,p):
 total=0;power=p
 while power<=2*r:
  total+=2*r//power-2*(r//power);power*=p
 return total

def source_change(raw):
 packet=json.loads(raw)['packet'];rows=packet['source'];by={r[0]:r for r in rows}
 names=['Bm1','Jrep','F','Z','alpha','twice_cell_bits','x','inner_bits','MC','MF','Kconstant','w','transport_quotient','delta_x']
 zero=(0,)*len(names)
 def const(v):return {} if not v else {zero:v}
 def var(k):
  e=list(zero);e[names.index(k)]=1;return {tuple(e):1}
 def add(a,b,s=1):
  out=dict(a)
  for k,v in b.items():out[k]=out.get(k,0)+s*v
  return {k:v for k,v in out.items() if v}
 def mul(a,b):
  out={}
  for i,x in a.items():
   for j,y in b.items():
    e=tuple(u+v for u,v in zip(i,j));out[e]=out.get(e,0)+x*y
  return {k:v for k,v in out.items() if v}
 used=set()
 def evaluate(changed):
  env={k:var(k) for k in names}
  if changed:
   env['x']=add(env['x'],env['delta_x'])
   env['alpha']=add(env['alpha'],mul(env['twice_cell_bits'],env['delta_x']),-1)
  def get(k):
   if type(k) is int:return const(k)
   if k not in env:
    _,op,x,y=by[k];a,b=get(x),get(y)
    env[k]=mul(a,b) if op=='*' else add(a,b,1 if op=='+' else -1);used.add(k)
   return env[k]
  return {k:get(k) for k in ['q','marked_rhs','W','odd_index','r_lhs','norm_transport']}
 old,new=evaluate(False),evaluate(True)
 for k in ['q','marked_rhs','W','r_lhs','norm_transport']:need(old[k]==new[k],'input/slack source invariant '+k)
 need(new['odd_index']==add(old['odd_index'],mul(var('twice_cell_bits'),var('delta_x'))),'literal exponent shift')
 q=add(mul(var('Bm1'),var('Jrep')),const(1))
 C=add(add(add(add(q,var('F'),-1),var('Z'),-1),var('alpha'),-1),mul(var('twice_cell_bits'),var('x')),-1)
 need(old['marked_rhs']==C,'actual raw slack')
 q2=mul(q,q)
 expectedR=add(mul(add(add(q2,var('Z'),-1),mul(q,var('F')),-1),add(q2,const(1),-1)),mul(add(var('MC'),mul(q,var('MF'))),var('Jrep')))
 need(old['r_lhs']==expectedR,'actual packed index including constant Z')
 need(len(rows)==83 and len(packet['witnesses'])==18 and packet['ordinary_input']=='x','source interface')
 return {'source_rows':len(rows),'positive_witnesses':18,'symbolic_ancestor_rows':len(used),'ancestor_names':sorted(used),'invariants':['q','C','W','R','transport at fixed w'],'changed_exponent':'u -> u + twice_cell_bits*delta_x','method':'fresh exact integer polynomial dictionaries, bound to actual supplied ports'}

def interval_checks():
 count=0;largest_first_hit=0
 for A in range(1501,3002,2):
  if A%5==0:continue
  fs=factors(A);phi=A
  for p in fs:phi=phi//p*(p-1)
  L=math.isqrt(3*A)+1
  need(3*phi*phi>=A*4**len(fs),'Euler product')
  need(L*phi>A*2**len(fs),'strict count threshold')
  for slope in [3,13,23]:
   if math.gcd(slope,A)!=1:continue
   for eta in [2,7,A//3]:
    good=[j for j in range(L) if math.gcd(eta+slope*j,A)==1]
    need(good,'affine interval')
    largest_first_hit=max(largest_first_hit,good[0]);count+=1
 return {'A_odd_interval':[1501,3001],'five_excluded':True,'cases':count,'largest_first_hit':largest_first_hit}

def local_permutations():
 count=0;residues=0;trace=[]
 for p in [3,7,11,13]:
  for depth in [1,2,3]:
   ell=(p-1)*p**(depth-1)
   need((pow(2,ell,p**(depth+1))-1)%p**(depth+1)!=0 and pow(2,ell,p**depth)==1,'period depth')
   for eta in [6,10]:
    if eta%p==0:continue
    r=p**depth*eta-1;R=2*r+1;u0=R%ell
    def poly(z):return eta*(r+2)+r*(r+2)*z+r*(r-1)*p**depth*z*z
    def deriv(z):return r*(r+2)+2*r*(r-1)*p**depth*z
    root=eta%p
    for level in [1,2,3]:
     if level>1:
      modulus=p**(level-1)
      need(poly(root)%modulus==0,'prior root')
      digit=(-poly(root)//modulus*pow(deriv(root),-1,p))%p
      root+=modulus*digit
     modulus=p**level
     need(poly(root)%modulus==0 and root%p!=0,'Newton unit root')
     values=[]
     for k in range(modulus):
      res=(pow(2,R,p**(depth+level))-pow(2,u0+ell*k,p**(depth+level)))%p**(depth+level)
      need(res%p**depth==0,'normalization');values.append(res//p**depth)
     need(sorted(values)==list(range(modulus)),'actual exponential permutation')
     k=values.index(root)
     need(poly(values[k])%modulus==0,'input realizes root')
     count+=1;residues+=modulus;trace.append([p,depth,eta,level,root,k])
 return {'local_cases':count,'enumerated_residues':residues,'precisions':[1,2,3],'transcript_sha256':sha(json.dumps(trace,separators=(',',':')).encode())}

def saved_crt(record):
 r,R,ell,u0,q=record['r'],record['R'],record['ell'],record['u0'],record['q']
 choices=[]
 for k in range(21):
  u=u0+ell*k
  X=(1<<R)-(1<<u)
  if all(sum(math.comb(2*r,r+j)*pow(X,j,p**3) for j in range(3))%p**3==0 for p in [3,7]):choices.append(k)
 need(choices==[12],'independent shared CRT representative')
 X=(1<<R)-(1<<(u0+12*ell));mod=2*q**3
 coef=math.comb(2*r,r);power=1;total=0
 for j in range(r+1):
  total=(total+coef*power)%mod;power=power*X%mod
  if j<r:coef=coef*(r-j)//(r+j+1)
 need(total==0 and record['input_k']==12 and record['full_M_mod_2q3']==0,'complete saved finite sum')
 return {'terms':r+1,'independently_selected_input':12,'M_mod_2q3':total,'scope':'local algebra example only'}

def reconstruct_families(records):
 checked=[]
 for saved in records:
  d,K=saved['d'],saved['K'];B=1<<d;D=d;Q=B;plus=K%5!=3
  q=Q*(Q+1)//2 if plus else Q*(2*Q-1);A=Q+1 if plus else 2*Q-1
  J=(q-1)//(B-1);m0=4*d if plus else 4*d//5;T=D-1 if plus else D+1;ell=2*d*T
  A0=q*q*(q*q-1)+(2+q*(B+3))*J;G=(1+q*K)*(q*q-1)
  zclasses=[z for z in range(1,m0+1,4) if (A0-G*z-5)%(2*d)==0]
  need(len(zclasses)==1,'independent original congruence class')
  zclass=zclasses[0];fs=factors(A)
  taus={p:vp(D-1 if plus else D,p) for p in fs};g=math.prod(p**v for p,v in taus.items());M=A*g
  offset=(A0-G*zclass+1)*pow(G*m0,-1,M)%M
  z0=zclass+m0*offset;period=m0*M;L=math.isqrt(3*A)+1
  good=next(j for j in range(L) if math.gcd((A0-G*(z0+period*j)+1)//(2*M),A)==1)
  z=z0+period*good;R=A0-G*z
  threshold=(K+2)*m0*A*g*L+2*d*(5+T*A)+1<q
  need(threshold==saved['threshold'],'saved threshold')
  if R<=0:
   need(saved.get('positive_R') is False and not threshold,'signed preliminary case')
   checked.append({'d':d,'K':K,'positive_R':False});continue
  r=(R-1)//2;x0=5+(((R-5)//(2*d)-5)%T)
  for key,value in [('z',z),('R',R),('q',q),('A',A),('g',g),('x0',x0)]:need(saved[key]==value,'family reconstruction '+key)
  for sig in saved['prime_signatures']:
   p=sig['p'];a=fs[p];depth=a+taus[p];c=central(r,p)
   need(sig['a']==a and sig['tau']==taus[p] and sig['depth']==depth and sig['central']==c,'saved prime signature')
   need(vp(r+1,p)==depth and c>=3*a,'saved unneeded local lifts')
  need(saved['Hreq']==1 and saved['input_lift_k']==0 and saved['odd_carry_budget'],'saved empty CRT')
  if threshold:
   xmax=x0+(A-1)*T
   need(q-(K+2)*z-2*d*xmax>0,'entire positive input interval')
   need(3*q+1<R<q**4-q**3,'source index range')
   for k in [0,A-1]:
    u=2*d*(x0+k*T)+5
    need(0<u<2*q<R and u>=10*D+5,'positive exponent bounds')
    need((pow(2,R,q*(q-1))-pow(2,u,q*(q-1)))%(q*(q-1))==0,'transport source period')
  checked.append({'d':d,'K':K,'positive_R':True,'threshold':threshold,'first_coprime_offset':good})
 return {'cases':len(checked),'records':checked,'scope':'reconstruction of supplied synthetic evidence; no actual compiled table'}

def result():
 author={}
 for ext,pin in PINS.items():
  raw=Path(str(STEM)+'.'+ext).read_bytes();need(sha(raw)==pin,'author pin '+ext);author[ext]={'sha256':pin,'bytes':len(raw)}
 doc=json.loads(Path(str(STEM)+'.json').read_text());deps={}
 for name,pin in doc['source_binding']['pins'].items():
  raw=(BASE/name).read_bytes();need(sha(raw)==pin,'dependency '+name);deps[name]={'sha256':pin,'bytes':len(raw)}
 return {'schema':'independent-source-coupled-input-lifting-v1','reviewer_sha256':sha(Path(__file__).read_bytes()),'author':author,'dependencies':deps,
         'source_shift':source_change((BASE/'complete83_shared_projection_scout.json').read_bytes()),
         'affine_intervals':interval_checks(),'actual_input_permutations':local_permutations(),'shared_CRT_fixture':saved_crt(doc['composed_crt']),
         'saved_families':reconstruct_families(doc['synthetic_family_cases']),
         'scope':{'author_or_predecessor_program_execution':False,'actual_compiler_zero':False,'huge_exponential_or_Pell_evaluation':False,'all_size_proof_checked_by_reading_not_enumeration':True}}

def main():
 ap=argparse.ArgumentParser();g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--output');g.add_argument('--expect');a=ap.parse_args();r=result()
 if a.output:
  with open(a.output,'x') as f:json.dump(r,f,sort_keys=True,indent=2);f.write('\n')
 else:need(r==json.loads(Path(a.expect).read_text()),'receipt mismatch')
 print(json.dumps({'status':'PASS','source_rows':r['source_shift']['symbolic_ancestor_rows'],'new_intervals':r['affine_intervals']['cases'],'local_maps':r['actual_input_permutations']['local_cases'],'residues':r['actual_input_permutations']['enumerated_residues'],'saved_family_cases':r['saved_families']['cases']},sort_keys=True))
if __name__=='__main__':main()
