#!/usr/bin/env python3
"""Fresh inert-source proof checks for the native fixed-repunit prime filter."""
import argparse,hashlib,json,math
from pathlib import Path
PINS={
 'complete84_scaled_strong_output.json':'8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf',
 'complete83_independent_gamma_scout.json':'ed570bc9e96d59e88ec6b6c1302ac177eb6704cfcd85fe39a3346798e89f5e20',
 'complete83_gamma_native_three_power_control.py':'7850b360362d95d03d57ec35b59163f84ab5900356020b4e5542fa7decda7023',
 'complete83_gamma_native_three_power_control.json':'6546a250cb4a511a27d1b3dccbf660223cb8b68aaeb1b81084b9921500cbb0a6',
 'complete83_gamma_native_three_power_control.md':'addac036d27190fcf61632df3e0a632815f1e039efd6b96dd3d778005f83e448',
 'gamma_parity_padding_scout.md':'0def681763b4039a7074bd13f33def941c2b215db8f90b4194400e84ffc4080c',
 'gamma83_residual_order_obstruction.md':'7d2d15ccb608f295a344000f23d147b8f7ce2975e5732f2f6e2adc05363b2754',
}
def need(ok,msg):
 if not ok:raise ValueError(msg)
def add(a,b,sign=1):
 r=dict(a)
 for k,v in b.items():r[k]=r.get(k,0)+sign*v
 return {k:v for k,v in r.items() if v}
def mul(a,b):
 r={}
 for k,v in a.items():
  for l,w in b.items():
   t=tuple(x+y for x,y in zip(k,l));r[t]=r.get(t,0)+v*w
 return {k:v for k,v in r.items() if v}
def const(n):return {(0,)*6:n} if n else {}
def cone(source):
 by={row[0]:row for row in source};selected=set();leaves=set()
 def visit(name):
  if not isinstance(name,str):return
  if name not in by:leaves.add(name);return
  if name in selected:return
  selected.add(name)
  for v in by[name][2:]:visit(v)
 visit('r_lhs')
 return [row for row in source if row[0] in selected],leaves

def source_identity(root):
 a=json.loads((root/'complete84_scaled_strong_output.json').read_text())['packet']['source']
 b=json.loads((root/'complete83_independent_gamma_scout.json').read_text())['packet']['source']
 rows,leaves=cone(a);other,otherleaves=cone(b)
 names=['Bm1','Jrep','F','Z','MC','MF']
 need(rows==other and leaves==otherleaves==set(names),'common actual source cone')
 env={name:{tuple(int(i==j) for i in range(6)):1} for j,name in enumerate(names)}
 for name,op,l,r in rows:
  x=env[l] if isinstance(l,str) else const(l);y=env[r] if isinstance(r,str) else const(r)
  env[name]=mul(x,y) if op=='*' else add(x,y,1 if op=='+' else -1)
 q=env['q'];J=env['Jrep'];Bminus=env['Bm1']
 gap=add(add(mul(q,q),env['Z'],-1),mul(q,env['F']),-1)
 quotient=add(add(mul(mul(Bminus,add(q,const(1))),gap),env['MC']),mul(q,env['MF']))
 need(env['r_lhs']==mul(J,quotient),'literal polynomial divisibility')
 data=[{'powers':list(k),'coefficient':v} for k,v in sorted(env['r_lhs'].items())]
 return {'variable_order':names,'actual_rows':rows,'row_count':len(rows),'polynomial_terms':len(data),'polynomial_coefficients':data,'quotient_terms':len(quotient),'identity':'r_lhs=Jrep*(Bm1*(q+1)*(q*q-Z-q*F)+MC+q*MF), q=1+Bm1*Jrep','MF_convention':'literal already-shifted source port; no native-mask substitution'}

def geom(a,n,m):
 value,total=1%m,0;block,bs=a%m,1%m
 while n:
  if n&1:total=(total+value*bs)%m;value=value*block%m
  bs=bs*(1+block)%m;block=block*block%m;n//=2
 return value,total

def crt(pairs):
 value,mod=0,1
 for t,m in pairs:
  if m==1:continue
  need(math.gcd(mod,m)==1,'CRT coprime');value+=mod*((t-value)*pow(mod,-1,m)%m);mod*=m
 return value,mod

def repunits():
 records=[]
 for d in [1,5,25,125]:
  B=1<<d
  for N0 in [1,5,25]:
   J0=((1<<(d*N0))-1)//(B-1)
   need(math.gcd(J0,30)==1 and J0%17!=0,'reference coprimalities')
   for ratio in [1,5,25]:
    N=N0*ratio;J=((1<<(d*N))-1)//(B-1)
    quotient=sum(1<<(d*N0*i) for i in range(ratio))
    need(J==J0*quotient,'nested repunit')
    records.append({'d':d,'N0':N0,'N_over_N0':ratio,'J0_bits':J0.bit_length(),'J_bits':J.bit_length(),'J0_mod30':J0%30,'J0_mod17':J0%17,'exact_nested_identity':True})
 return records

def orders():
 records=[]
 for p,wanted in [(601,25),(1801,25),(3607,601),(28817,1801),(2147483647,31)]:
  need(all(p%t for t in range(2,math.isqrt(p)+1)),'trial prime')
  need(pow(2,wanted,p)==1 and all(pow(2,t,p)!=1 for t in range(1,wanted) if wanted%t==0),'exact order')
  records.append({'p':p,'ord_p_2':wanted})
 need(((1<<25)-1)//((1<<5)-1)==601*1801,'illustrative J0 factorization')
 return records

def towers():
 records=[];lifts=0
 # Deliberately bounded geometry models; d=1 is not a compiled-program width.
 for u,d,h,N0,D0 in [(2,1,1,5,31),(3,1,1,5,31),(2,1,1,25,31),(2,5,1,1,1),(3,5,1,1,1)]:
  E=d*h;J0=((1<<(d*N0))-1)//((1<<d)-1);need(J0%D0==0,'reference divisor');n=3**u*E*D0
  Aminus=(1<<n)-1;Q=3**(u-2)*Aminus;spacing=2*3**u*h*D0
  Htime=25
  while h*Htime%N0 or h*Htime<=75*d or Htime<=5*((spacing//h)*(Q-2)+1):Htime*=5
  N=h*Htime;L=4*N//5;last=spacing*(Q-2)
  need(last+h<N//5 and last+L+h<N,'grid geometry')
  primes=[7,73]+([2147483647] if D0==31 else [31,151])
  need(all(Aminus%p==0 for p in primes),'finite test primes')
  for unit in [1,2]:
   Gamma=3*J0*unit
   Rbase,_=crt([(0,9),(E,d*N),(31,32),(0,J0)])
   need(Rbase%J0==0,'baseline reference factor')
   mod3=3**max(u,3);G3=Gamma*(pow(2,d*L,mod3)-1)%mod3
   need(G3%9==0 and G3%27!=0,'actual valuation shape')
   ternary=3**(u-2)
   target=(Rbase//9)*pow(2*(G3//9),-1,ternary)%ternary if ternary>1 else 0
   pairs=[(target,ternary)];local=[];rbase=(Rbase-1)//2
   for p in primes:
    v=0
    while Gamma*(pow(2,d*L,p**(v+1))-1)%p**(v+1)==0:v+=1
    mod=p**(v+1);G=Gamma*(pow(2,d*L,mod)-1)%mod
    target=((rbase//p**v)-(p-1))*pow(G//p**v,-1,p)%p
    pairs.append((target,p));local.append((p,v,mod,G))
   k,period=crt(pairs);need(k<period<=Q,'prefix capacity')
   total=geom(pow(2,d*spacing,mod3),k,mod3)[1]
   need((Rbase-2*G3*total)%3**u==0,'controlled ternary power')
   # J0 preservation follows independently because Gamma already contains J0.
   need(Gamma%J0==0 and Rbase%J0==0,'reference preservation')
   for p,v,mod,G in local:
    total=geom(pow(2,d*spacing,mod),k,mod)[1]
    residue=(rbase-G*total)%mod
    need(residue//p**v==p-1,'binomial carry digit');lifts+=1
   records.append({'u':u,'d':d,'h':h,'N0':N0,'J0':J0,'D0':D0,'n':n,'N':N,'Q':Q,'spacing':spacing,'Gamma':Gamma,'Rbase':Rbase,'prefix':k,'CRT_modulus':period,'checked_minus_primes':primes,'scope':'synthetic baseline/Gamma and bounded arithmetic geometry; not an accepting compiler history'})
 return records,lifts

def equal(a,b):
 if type(a) is not type(b):return False
 if isinstance(a,dict):return a.keys()==b.keys() and all(equal(a[k],b[k]) for k in a)
 if isinstance(a,list):return len(a)==len(b) and all(equal(x,y) for x,y in zip(a,b))
 return a==b

def read_json(path):
 def pairs(items):
  out={}
  for k,v in items:need(k not in out,'duplicate JSON key');out[k]=v
  return out
 def bad(s):raise ValueError('nonfinite JSON '+s)
 return json.loads(path.read_text(),object_pairs_hook=pairs,parse_constant=bad)

def make(root):
 for name,pin in PINS.items():need(hashlib.sha256((root/name).read_bytes()).hexdigest()==pin,'pin '+name)
 models,lifts=towers()
 return {'schema':'native-repunit-filter-v1','pins':PINS,'source_identity':source_identity(root),'nested_repunit_checks':repunits(),'illustrative_prime_orders':orders(),'prefix_CRT_models':models,'minus_prime_digit_lifts':lifts,'scope':{'genuine_history_theorem':'for fixed reference N0, enlarged future times preserve J0|R and support the composite filter at n=3^u*d*h*D0 for every fixed positive divisor D0 of J0','fixed_d5_example':'illustrative only; no claim the universal compiler has d=5','source_change':False,'full_histories_or_Pell_zeros_materialized':False,'gamma83_language':'unresolved'}}

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--root',type=Path,required=True)
 g=p.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path)
 args=p.parse_args();r=make(args.root)
 if args.output:args.output.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
 else:need(equal(r,read_json(args.expect)),'exact receipt mismatch')
 print('PASS: literal repunit divisibility and bounded native-filter arithmetic checks')

if __name__=='__main__':main()
