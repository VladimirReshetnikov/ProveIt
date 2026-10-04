#!/usr/bin/env python3
"""Fresh inert-data checks for the native small-prime digit rules."""
import argparse
import hashlib
import json
import math
from pathlib import Path

PINS = {
 'complete83_gamma_native_finite_prime_avoidance.py':'c13626a4efc17639f0b3d3ec59fb574c90c3a8af1cc51e2db7d73b20739b3e81',
 'complete83_gamma_native_finite_prime_avoidance.json':'1a4fd227072987420e6533195e5efa29dfc636d109ae8e5e08c61ebeedea8849',
 'complete83_gamma_native_finite_prime_avoidance.md':'93aa3b61dcd03f7ce65acca9619f90c29710235ec2438cb4dd14000d8bdb8a96',
 'complete75_half_binomial_compiler.md':'68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117',
 'complete75_gamma87_compiler_order_filters.md':'43d613204d6dc7192763e87e120f84ea0e3f18849a4fd23be26f56ca45b9fcc3',
 'complete83_independent_gamma_scout.md':'bdbcc3be5396bced89373da5ffb30f0f3f113f7e8e7ebe65e4f7b730264f1b41',
}
# One exact central-carry prefix for each normalized value, in value order.
SEEDS = {
 (5,3):[33,8,3,58,158],
 (7,2):[410,11,18,4,60,158,67],
 (7,4):[11,410,67,158,60,4,18],
 (13,8):[2412,358,20,59,540,46,189,228,33,215,371,7,202],
 (13,11):[46,1073,7,59,215,228,33,189,553,20,72,371,722],
 (13,7):[410,1073,553,748,59,46,202,20,878,7,33,72,228],
 (17,9):[43,349,60,383,366,1216,9,638,604,128,1233,315,1505,77,672,94,26],
}

def check(ok, message):
 if not ok: raise ValueError(message)

def digit_rule(r,x,p):
 if r==0: return 1,1
 k,d=divmod(r,p)
 g,c=digit_rule(k,x,p)
 if 2*d<p:
  cd=math.comb(2*d,d)%p
  low=pow(1+x,2*d,p)
  upper=sum(math.comb(2*d,j)*pow(x,j,p) for j in range(d,2*d+1))%p
  return pow(x,-d,p)*(low*g+(upper-low)*c)%p,cd*c%p
 low=pow(1+x,2*d-p,p)
 return pow(x,-d,p)*low*((1+x)*g-c)%p,0

def direct(r,x,p):
 # Whole integer binomial row, evaluated modulo p; independent of digit_rule.
 n=2*r; coefficient=1; value=0; power=1; central=None
 for j in range(n+1):
  if j==r:central=coefficient%p
  if j>=r:
   value=(value+coefficient*power)%p
   power=power*x%p
  if j<n:coefficient=coefficient*(n-j)//(j+1)
 return value,central

def exact_equal(a,b):
 if type(a) is not type(b):return False
 if isinstance(a,dict):return a.keys()==b.keys() and all(exact_equal(a[k],b[k]) for k in a)
 if isinstance(a,list):return len(a)==len(b) and all(exact_equal(x,y) for x,y in zip(a,b))
 return a==b

def unique_pairs(pairs):
 out={}
 for k,v in pairs:
  check(k not in out,'duplicate JSON key')
  out[k]=v
 return out

def load_json(path):
 def bad(token):raise ValueError('nonfinite JSON '+token)
 return json.loads(path.read_text(),object_pairs_hook=unique_pairs,parse_constant=bad)

def make(root):
 for name,expected in PINS.items():
  check(hashlib.sha256((root/name).read_bytes()).hexdigest()==expected,'pin '+name)
 recurrence=0
 for p in [5,7,13,17]:
  for x in range(1,p):
   for r in range(121):
    check(digit_rule(r,x,p)==direct(r,x,p),'recurrence')
    recurrence+=1
 seeds=[]; extensions=[]; transitions=0
 for (p,x),table in SEEDS.items():
  z=(1+x)**2*pow(x,-1,p)%p
  for target,t in enumerate(table):
   g,c=direct(t,x,p)
   check(c==0 and g*pow(z,-t,p)%p==target,'seed coverage')
   check(digit_rule(t,x,p)==(g,c),'seed recurrence')
   seeds.append({'p':p,'x':x,'z':z,'normalized':target,'prefix':t,'G':g,'C':c})
   for d in range(p):
    gg,cc=digit_rule(p*t+d,x,p)
    check(cc==0 and gg*pow(z,-(p*t+d),p)%p==target,'append invariance')
    transitions+=1
  # Synthetic scalar-congruence examples only. No actual histories.
  M=math.lcm(p-1,16,3,125 if p!=5 else 1)
  phases=[r for r in range(M) if (2*r+1)%32==31 and pow(2,2*r+1,p)==x and (p==5 or (2*r+1)%125==5)]
  check(bool(phases),'compatible phase')
  phase=phases[0]; ell=3
  v=2 if p==5 else p**ell-1
  for desired in range(p):
   normalized=2*desired*pow(x+1,-1,p)*pow(z,-phase,p)%p
   prefix=table[normalized]; L=ell
   modulus=M*p**ell
   while p**L<modulus:L+=1
   start=prefix*p**L
   # w=v-start mod p^ell; select its M-class by CRT.
   w=(v-start)%(p**ell)
   w+=p**ell*((phase-start-w)*pow(p**ell,-1,M)%M)
   check(0<=w<modulus<=p**L,'prefix interval')
   r=start+w
   g,c=digit_rule(r,x,p)
   a=(x+1)*g*pow(2,-1,p)%p
   check(r%M==phase and r%(p**ell)==v and pow(2,2*r+1,p)==x,'extension congruences')
   check(c==0 and a==desired,'extension target')
   extensions.append({'p':p,'x':x,'M':M,'phase':phase,'ell':ell,'suffix_residue':v,'prefix':prefix,'appended_length':L,'r':r,'R':2*r+1,'a_mod_p':a,'Delta_mod_p':(a+1)*(a+3)%p})
 fixed_bases=[]
 for R3 in range(3):
  R=next(r for r in range(31,31+96,32) if r%3==R3)
  fixed_bases.append({'R_mod_3':R3,'representative_R':R,'bases':{str(p):pow(2,R,p) for p in [5,7,13,17]}})
 # Coefficient residue at a single forced carry for X=1 modulo7.
 seven=[]
 for r in range(1,500):
  if (2*r+1)%3:continue
  g,c=direct(r,1,7)
  if c:continue
  a=g
  check(a==2 and (a+1)*(a+3)%7==1,'seven carry residue')
  seven.append({'r':r,'a_mod_7':a,'Delta_mod_7':1})
 # Geometry and CRT are bounded synthetic data, not compiled histories.
 geometries=[]; crt=[]
 for E,h in [(5,1),(25,5)]:
  d=E//h; Q=3*(2**(3*E)-1); Htime=25
  while Htime<=5*(6*Q-11):Htime*=5
  N=h*Htime; Lswap=4*N//5; imax=6*h*(Q-2)
  check(imax+h<N//5 and imax+Lswap+h<N,'grid geometry')
  check(pow(2,6*E,7)==1 and pow(2,6*E,3)==1,'spacing')
  geometries.append({'E':E,'h':h,'Q':Q,'Htime':Htime,'N':N,'Lswap':Lswap,'last_source':imax})
 for p in [3,7,31]:
  for s in [0,1,3]:
   for base in [0,19,127]:
    G=p**s*2; residue=next(k for k in range(p) if ((base-G*k)//p**s)%p==p-1)
    value=base-G*residue
    check((value//p**s)%p==p-1,'digit target')
    crt.append({'p':p,'s':s,'G':G,'base_half_index':base,'prefix_mod_p':residue})
 orders=[]
 for p,wanted in [(7,3),(151,15),(331,30)]:
  check(all(p%d for d in range(2,math.isqrt(p)+1)),'prime example')
  actual=next(k for k in range(1,p) if pow(2,k,p)==1)
  check(actual==wanted,'order example')
  orders.append({'prime':p,'order_of_2':actual})
 check(2**15-1==7*31*151 and 2**15+1==9*11*331,'factorization')
 return {'schema':'native-small-prime-digit-rules-v1','pins':PINS,
  'scope':{'genuine_history_theorem':'gcd(Delta,2^(6E)-1)=3 and gcd(Delta,(2^(6E)-1)/9)=1 for even selector count and odd tile alphabet; E=dh',
   'barrier':'all compatible finite scalar congruences and digit prescriptions in native-formula indices; no history realization claim',
   'source_change':False,'ordinary_input_language':'unresolved'},
  'fixed_bases':fixed_bases,'new_order_examples':orders,'factorizations':{'2^15-1':[7,31,151],'2^15+1':[3,3,11,331]},'recurrence_full_row_comparisons':recurrence,
  'carry_seeds':seeds,'append_checks':transitions,'synthetic_congruence_extensions':extensions,
  'seven_carry_formula_cases':seven,'grid_geometries':geometries,'synthetic_digit_targets':crt}

def main():
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--root',type=Path,required=True)
 group=parser.add_mutually_exclusive_group(required=True)
 group.add_argument('--output',type=Path);group.add_argument('--expect',type=Path)
 args=parser.parse_args();result=make(args.root)
 if args.output:args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
 else:check(exact_equal(result,load_json(args.expect)),'exact receipt mismatch')
 print('PASS: native small-prime rules; 75 complete carry-prefix certificates; history scope unchanged')

if __name__=='__main__':main()
