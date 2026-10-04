#!/usr/bin/env python3
"""Fresh bounded free-arithmetic-host checks; no compiler or predecessor execution."""
import argparse, hashlib, json, math
from pathlib import Path
PINS={
 'complete83_independent_gamma_scout.json':'ed570bc9e96d59e88ec6b6c1302ac177eb6704cfcd85fe39a3346798e89f5e20',
 'complete83_independent_gamma_scout.md':'bdbcc3be5396bced89373da5ffb30f0f3f113f7e8e7ebe65e4f7b730264f1b41',
 'complete75_independent_gamma87_period.md':'dfe1c4a9c438bfe3907b187a3d407280616a5a7eaaf3aa68048de9938b8ac784',
 'complete75_gamma87_compiler_order_filters.md':'43d613204d6dc7192763e87e120f84ea0e3f18849a4fd23be26f56ca45b9fcc3',
 'complete75_independent_gamma87_local_filters.md':'6dc2b46d7cdc4bf33566b24e5c0252d34858128096dbdb6614881b3a33fb6171',
 'complete83_gamma_power_tests.md':'4e8f358a2d651e4cc20946dd3632491d15ad3ee69eb32474a21289e052ec5e4b',
 'complete83_gamma_small_prime_digit_rules.md':'b7248efe5f292bd5dcbf093ccd9f664d663b2eb23c022974b1a9f64b537a4f8e',
 'gamma_parity_padding_scout.md':'0def681763b4039a7074bd13f33def941c2b215db8f90b4194400e84ffc4080c',
}
def check(ok,why):
 if not ok:raise ValueError(why)
def val(n,p):
 check(n>0,'valuation positive');e=0
 while n%p==0:e+=1;n//=p
 return e
def combine(pairs):
 a,M=0,1
 for b,n in pairs:
  check(math.gcd(M,n)==1,'coprime CRT moduli')
  a+=M*((b-a)*pow(M,-1,n)%n);M*=n
 return a,M

def build(root):
 for name,pin in PINS.items():check(hashlib.sha256((root/name).read_bytes()).hexdigest()==pin,name)
 packet=json.loads((root/'complete83_independent_gamma_scout.json').read_text())['packet']
 source=packet['source'];check(len(source)==83,'actual row count')
 deps={v:{v} for v in packet['free']}
 for name,op,left,right in source:
  deps[name]=(deps[left] if isinstance(left,str) else set()) | (deps[right] if isinstance(right,str) else set())
 for factor in packet['factors']:
  check(bool(deps[factor]&{'rho','delta'})==(factor=='norm_input'),'input-private scope')
 prime_orders=[]
 for k,r in [(1,131071),(3,127855913)]:
  check(all(r%d for d in range(2,math.isqrt(r)+1)),'trial prime')
  n=17**k
  check(pow(2,n,r)==1 and pow(2,n//17,r)!=1,'exact prime-power order')
  prime_orders.append({'k':k,'r':r,'order_of_2':n})
 cases=[]
 d,E,t=5,5,125
 for u in [1,2,3]:
  N=3**u*E;minus=(1<<N)-1;plus=(1<<N)+1;S=minus*plus
  check(val(S,3)==u+1,'S valuation')
  for order in prime_orders:
   k,r=order['k'],order['r'];n=order['order_of_2']
   a,modulus=combine([(0,plus),(pow(4,-1,minus),minus),(-1,n),(-3*pow(4,-1,r),r),(1<<(3*t),1<<(3*t+1))])
   H=4*a+3;Delta=(a+1)*(a+3);A=a+2
   check(a>1<<t and a%6==0 and val(a,2)==3*t,'native-style elementary domain')
   check(a%plus==0 and (4*a-1)%minus==0,'strong residue constraints')
   check(math.gcd(Delta,S)==3 and math.gcd(Delta,S//3**(u+1))==1,'composite filter')
   check(val(Delta,3)==val(H,3)==1 and math.gcd(H,Delta)==3,'three and discriminant')
   check(Delta%n==0 and H%r==0 and math.gcd(n,2*d)==1,'certified divisor of m')
   check(math.gcd(n,H-1)==math.gcd(n,H-3)==1,'all-e power test obstruction')
   # Supplementary bounded residues, not the reason the all-e assertion holds.
   residues=[[e,pow(2,(1<<e)*(H-j),r)] for j in [1,3] for e in range(8)]
   check(all(v!=1 for _,v in residues),'finite power test residues')
   cases.append({'u':u,'E':E,'t':t,'d':d,'k':k,'prime_order_witness':r,'m_divisor':n,
                 'a':a,'H':H,'Delta':Delta,'CRT_modulus':modulus,'v2_a':val(a,2),'v3_a':val(a,3),
                 'S':S,'gcd_Delta_S':math.gcd(Delta,S),'stripped_quotient_gcd':math.gcd(Delta,S//3**(u+1)),
                 'Hminus1_power_residues_at_r':residues[:8],'Hminus3_power_residues_at_r':residues[8:]})
 return {'schema':'gamma83-residual-order-obstruction-v1','pins':PINS,'actual_source_rows_read':len(source),
         'scope':'Free arithmetic parameters only: no native half-binomial identity, masks, computation, input-component tuple, or full polynomial zero.',
         'prime_order_certificates':prime_orders,'cases':cases,'full_orders_computed':False,'full_compiler_zeros_materialized':False}

def equal(a,b):
 if type(a) is not type(b):return False
 if isinstance(a,dict):return a.keys()==b.keys() and all(equal(a[k],b[k]) for k in a)
 if isinstance(a,list):return len(a)==len(b) and all(equal(x,y) for x,y in zip(a,b))
 return a==b

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--root',type=Path,required=True)
 g=p.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path)
 a=p.parse_args();r=build(a.root)
 if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 else:check(equal(r,json.loads(a.expect.read_text())),'receipt mismatch')
 print('PASS: six nonnative CRT hosts, two exact order certificates, no full zero claim')
if __name__=='__main__':main()
