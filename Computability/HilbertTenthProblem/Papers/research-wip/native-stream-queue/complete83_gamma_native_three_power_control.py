#!/usr/bin/env python3
"""Fresh bounded checks for actual-history finite ternary-power control."""
import argparse
import hashlib
import json
import math
from pathlib import Path

PINS={
 '../../verification/explore_fixed_raw_universal_76.py':'011097aaee5acb02e938e66f8e6adcec711cf5a097d87a9f50a3cf28f19d97d0',
 'complete75_half_binomial_compiler.py':'d6bed0afef319e5a702bda6b9959bf3888e101da7879b77953c345182f8032d2',
 'complete75_half_binomial_compiler.md':'68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117',
 '../../1980/EXPLORATION_FIVE_ADIC_DUMMY_CONTROL.md':'44ed02164f61e410bb377b52aa292abf476e025eeea1052784f30d654a0522fa',
 'complete83_gamma_native_finite_prime_avoidance.md':'93aa3b61dcd03f7ce65acca9619f90c29710235ec2438cb4dd14000d8bdb8a96',
 'complete83_gamma_native_finite_prime_avoidance.py':'c13626a4efc17639f0b3d3ec59fb574c90c3a8af1cc51e2db7d73b20739b3e81',
 'complete83_gamma_native_finite_prime_avoidance.json':'1a4fd227072987420e6533195e5efa29dfc636d109ae8e5e08c61ebeedea8849',
 'complete83_gamma_small_prime_digit_rules.md':'b7248efe5f292bd5dcbf093ccd9f664d663b2eb23c022974b1a9f64b537a4f8e',
 'gamma_parity_padding_scout.md':'0def681763b4039a7074bd13f33def941c2b215db8f90b4194400e84ffc4080c',
}

def need(ok,msg):
 if not ok:raise ValueError(msg)

def vp(n,p):
 need(n!=0,'valuation of zero');n=abs(n);v=0
 while n%p==0:n//=p;v+=1
 return v

def geom(a,n,m):
 # Pair (a^n, sum_(j<n) a^j), via repeated squaring.
 value=1%m;total=0;block=a%m;blocksum=1%m
 while n:
  if n&1:total=(total+value*blocksum)%m;value=value*block%m
  blocksum=blocksum*(1+block)%m;block=block*block%m;n//=2
 return value,total

def crt(pairs):
 value=0;modulus=1
 for target,m in pairs:
  if m==1:continue
  need(math.gcd(modulus,m)==1,'CRT coprimality')
  value+=modulus*((target-value)*pow(modulus,-1,m)%m);modulus*=m
 return value,modulus

def table(d,N):
 M=d*N;T=N//5;lookup={};weights=[]
 for j in range(T):
  w=pow(2,4*d*j,M);need((w-1)%(5*d)==0,'five-adic subgroup')
  t=(w-1)//(5*d);need(t not in lookup,'subgroup distinctness')
  lookup[t]=j;weights.append(w)
 need(len(lookup)==T,'subgroup coverage')
 return M,T,lookup,weights

def subset(d,N,target,tab):
 M,T,lookup,weights=tab;B=pow(2,d,3*M)
 z=target%M;desired=target%3;epsilon=int(z%5==0)
 k=next(k for k in range(1,15*d) if (k-z+epsilon*B)%(5*d)==0 and (k-epsilon-desired)%3==0)
 need(k<T and k%5!=0,'cardinality')
 numerator=z-epsilon*B-k;need(numerator%(5*d)==0,'integral target')
 sigma=numerator//(5*d)%T
 t0=(sigma-k*(k-1)//2)*pow(k,-1,T)%T
 indices=sorted([4*lookup[(t0+j)%T] for j in range(k)]+([1] if epsilon else []))
 need(len(set(indices))==len(indices),'Boolean subset')
 need(sum(pow(2,d*i,3*M) for i in indices)%(3*M)==target%(3*M),'joint residue')
 return indices,k,epsilon

def test_subsets():
 records=[]
 for d,N,full in [(1,125,True),(5,625,True),(25,3125,False)]:
  need(N>75*d,'height premise');tab=table(d,N);M,T,_,_=tab
  targets=list(range(3*M)) if full else sorted({(104729*j+17)%(3*M) for j in range(160)}|{0,3*M-1})
  digest=hashlib.sha256();counts=[0,0,0];maximum=0
  for target in targets:
   indices,k,epsilon=subset(d,N,target,tab)
   digest.update(json.dumps([target,indices],separators=(',',':')).encode()+b'\n')
   counts[target%3]+=1;maximum=max(maximum,k)
   for h in [1,5,25]:
    if N//h>=25:need(all(i+1<N and i+h<N for i in indices),'nonwrapping control')
  dp=None
  if full:
   modulus=3*M;mask=(1<<modulus)-1;reach=1
   for i in [4*j for j in range(T)]+[1]:
    w=pow(2,d*i,modulus)
    reach|=((reach<<w)|(reach>>(modulus-w)))&mask
   need(reach==mask,'independent subset DP');dp=reach.bit_count()
  records.append({'d':d,'N':N,'modulus':3*M,'targets':len(targets),'exhaustive':full,'target_mod3_counts':counts,'maximum_cardinality':maximum,'subset_stream_sha256':digest.hexdigest(),'independent_dp_coverage':dp})
 return records

def test_layout():
 records=[]
 # Arbitrary coefficient values are allowed in the canceling paired bands.
 for a in [2,3,4,5]:
  for m in [12,24]:
   M=m+6*a-3;Emax=27*M;H=Emax+24*M+3*a+1
   T1=H+2*Emax+a+1;T2=T1+2*Emax+1;high=T2+Emax+1
   for chi in [0,1]:
    dc=sum(pow(-1,e,3) for e in [3*a,H+a,8*M,24*M])+chi*pow(-1,high,3)
    dc+=sum((j+2)*(pow(-1,T1-j,3)+pow(-1,T2-j,3)) for j in range(10))
    dr=pow(-1,H,3)
    need(high%2==0 and (dc-dr)%3==chi,'layout high parity')
    need((2-dc+dr)%3 in [1,2],'Gamma bracket unit')
    records.append({'tile_alphabet_size':a,'even_clause_count':m,'high_correction':chi,'anchor_unit_mod2':M%2,'H_mod2':H%2,'T1_mod2':T1%2,'T2_mod2':T2%2,'high_degree_mod2':high%2,'DC_minus_DR_mod3':(dc-dr)%3,'bracket_mod3':(2-dc+dr)%3})
 return records

def test_gamma():
 cases=0
 for d in [1,5,25]:
  for N in [125,625]:
   for h in [1,5]:
    for e in [2,3]:
     for chi in [0,1]:
      for dr in [1,2,4]:
       # Small coefficient models with the exact proved residue DC-DR=chi.
       dc=dr+chi+3;q=pow(2,d*N,9);B=pow(2,d,9)
       gamma=pow(2,e,9)*(q*q-1)*(1+q*(dc+B*dr+pow(B,h,9)))%9
       need(gamma%3==0 and gamma!=0,'Gamma exact valuation')
       expected=pow(-1,e,3)*(d*N)*(2-chi)%3
       need((gamma//3)%3==expected,'Gamma divided residue')
       L=4*N//5
       need(vp((1<<(d*L))-1,3)==1,'swap valuation')
       cases+=1
 return cases

def test_towers():
 records=[];lift_checks=0
 for u,E,h in [(2,5,1),(3,5,1),(4,5,1),(2,25,5)]:
  d=E//h;Aminus=(1<<(3**u*E))-1;Q=3**(u-2)*Aminus;spacing=2*3**u*h
  Htime=25
  while Htime<=5*((spacing//h)*(Q-2)+1) or h*Htime<=75*d:Htime*=5
  N=h*Htime;L=4*N//5;last=spacing*(Q-2)
  need(last+h<N//5 and last+L+h<N,'tower grid')
  prime_set=[7,31,73,151]+([262657] if u>=3 else [])
  need(all(Aminus%p==0 for p in prime_set),'minus prime membership')
  for gamma_unit in [1,2,7]:
   gamma=3*gamma_unit
   for seed in [0,1,5]:
    Rbase,_=crt([(0,9),(E,d*N),(31,32)])
    Rbase+=seed*9*d*N*32
    need(Rbase%9==0 and Rbase%(d*N)==E%(d*N),'baseline')
    modulus3=3**max(u,3)
    G3=gamma*(pow(2,d*L,modulus3)-1)%modulus3
    need(G3%9==0 and G3%27!=0,'G valuation two')
    target3=(Rbase//9)*pow(2*(G3//9),-1,3**(u-2))%(3**(u-2)) if u>2 else 0
    pairs=[(target3,3**(u-2))];local=[]
    rbase=(Rbase-1)//2
    for p in prime_set:
     v=0
     while gamma*(pow(2,d*L,p**(v+1))-1)%p**(v+1)==0:v+=1
     mod=p**(v+1);G=gamma*(pow(2,d*L,mod)-1)%mod
     need(G%p**v==0 and G%mod!=0,'p valuation')
     wanted=((rbase//p**v)-(p-1))*pow(G//p**v,-1,p)%p
     pairs.append((wanted,p));local.append((p,v,mod,G))
    k,period=crt(pairs);need(k<Q and period<=Q,'CRT prefix capacity')
    sum3=geom(pow(2,d*spacing,modulus3),k,modulus3)[1]
    need((Rbase-2*G3*sum3)%3**u==0,'tower divisibility')
    for p,v,mod,G in local:
     total=geom(pow(2,d*spacing,mod),k,mod)[1]
     changed=(rbase-G*total)%mod
     need(changed//p**v==p-1,'central carry digit');lift_checks+=1
    records.append({'u':u,'E':E,'h':h,'N':N,'Htime':Htime,'Q':Q,'spacing':spacing,'Gamma':gamma,'Rbase':Rbase,'prefix':k,'CRT_modulus':period,'checked_minus_primes':prime_set,'scope':'synthetic Gamma and baseline residues; genuine geometry, no compiled history or full q/Pell tuple'})
 return records,lift_checks

def eq(a,b):
 if type(a) is not type(b):return False
 if isinstance(a,dict):return a.keys()==b.keys() and all(eq(a[k],b[k]) for k in a)
 if isinstance(a,list):return len(a)==len(b) and all(eq(x,y) for x,y in zip(a,b))
 return a==b

def read_json(path):
 def pairs(items):
  result={}
  for k,v in items:need(k not in result,'duplicate JSON key');result[k]=v
  return result
 def invalid(s):raise ValueError('nonfinite JSON '+s)
 return json.loads(path.read_text(),object_pairs_hook=pairs,parse_constant=invalid)

def make(root):
 for name,pin in PINS.items():need(hashlib.sha256((root/name).read_bytes()).hexdigest()==pin,'pin '+name)
 towers,lifts=test_towers();geometric=0
 for modulus in [9,27,81,49,31**2]:
  for a in [4,16,64]:
   for n in range(64):
    need(geom(a,n,modulus)==(pow(a,n,modulus),sum(pow(a,j,modulus) for j in range(n))%modulus),'geometric sum');geometric+=1
 orders=[]
 for p in [7,19,31,73,151,262657]:
  need(all(p%d for d in range(2,math.isqrt(p)+1)),'prime')
  order=next(k for k in range(1,p) if pow(2,k,p)==1)
  orders.append({'p':p,'ord_p_2':order})
 return {'schema':'native-three-power-control-v1','pins':PINS,'layout_parities':test_layout(),'Gamma_valuation_models':test_gamma(),'joint_Boolean_subset_checks':test_subsets(),'tower_CRT_models':towers,'minus_prime_digit_lifts':lifts,'independent_geometric_checks':geometric,'orders':orders,'scope':{'unrestricted_proof':'actual Gamma valuation, joint Boolean subset lemma, genuine-history control of every fixed finite3power and finite prime filter','numerical_evidence':'bounded component checks, not full native compiler histories or Pell zeros','source_change':False,'gamma83_ordinary_input_language':'unresolved'}}

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--root',type=Path,required=True)
 g=p.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path)
 a=p.parse_args();r=make(a.root)
 if a.output:a.output.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
 else:need(eq(r,read_json(a.expect)),'exact receipt mismatch')
 print('PASS: actual-history three-power theorem; bounded joint-subset and CRT evidence')

if __name__=='__main__':main()
