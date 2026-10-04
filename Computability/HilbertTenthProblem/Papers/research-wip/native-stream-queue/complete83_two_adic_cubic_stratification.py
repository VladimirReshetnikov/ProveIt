"""Fresh local cubic arithmetic; no predecessor program is run or imported."""
from pathlib import Path
from math import comb
import argparse,hashlib,json

ROOT=Path('/home/codex/.codex/worktrees/2a71/Proofs/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue')
PINS={'complete83_even_radix_boundary.md':'eba3e2944154dd7ff28e5b20d5e32e8ee6a0138b515c8e5f3846979dadaaa8dc','complete83_shared_projection_math.md':'1a9923b7202bef2e5a640b3b27c942423b9d9829d9fc6e7f4b55fa5c4d91053c','complete83_dyadic_zero_offset_exclusion.md':'afa5bf412a150d61deb91e0c5b1eaa17f7f9423c254a93fd1d699221a285adc1'}
def ck(ok,msg):
 if not ok:raise ValueError(msg)
def v(n):
 if not n:raise ValueError('zero valuation')
 n=abs(n);return (n&-n).bit_length()-1
def sha(b):return hashlib.sha256(b).hexdigest()
def evalpoly(cs,x):return sum(c*x**j for j,c in enumerate(cs))
def lift_odd(cs,bits):
 z=1
 ck(evalpoly(cs,z)%2==0,'odd root mod2')
 for n in range(1,bits):
  m=1<<(n+1);choices=[w for w in [z,z+(1<<n)] if evalpoly(cs,w)%m==0]
  ck(len(choices)==1,'unique next odd lift');z=choices[0]
 return z
def build():
 for f,h in PINS.items():ck(sha((ROOT/f).read_bytes())==h,'dependency pin')
 cases=low=linear=cubic=0;records=hashlib.sha256();lifts=0
 for r in range(3,1024,2):
  C=[comb(2*r,r+j) for j in range(4)];p=r.bit_count();k=v(r+1);ell=v(r+3);h2=v(r-1)
  ck([v(c) for c in C]==[p,p-k,p+h2-k,p+h2-k-ell],'coefficient valuations')
  for alpha in range(2,10):
   for z in (1,3,5,7,13):
    X=(1<<alpha)*z;P=evalpoly(C,X);actual=v(P);kind=''
    if k>=2:
     if k!=alpha:ck(actual==p+min(0,alpha-k),'nonresonant linear branch');kind='linear-nontie'
     else:
      G=[C[0]>>p,C[1]>>(p-k),(C[2]>>(p+1-k))<<(k+1),(C[3]>>(p-k))<<(2*k)]
      ck(P==(1<<p)*evalpoly(G,z),'linear normalized identity');linear+=1;kind='linear-tie'
      root=lift_odd(G,7);ck((evalpoly(G,z)%128==0)==(z%128==root),'linear root criterion');lifts+=1
    else:
     if ell!=3*alpha+1:ck(actual==p+min(0,1-ell+3*alpha),'nonresonant cubic branch');kind='cubic-nontie'
     else:
      G=[C[0]>>p,(C[1]>>(p-1))<<(alpha-1),(C[2]>>(p+1))<<(2*alpha+1),C[3]>>(p-3*alpha)]
      ck(P==(1<<p)*evalpoly(G,z),'cubic normalized identity');cubic+=1;kind='cubic-tie'
      root=lift_odd(G,7);ck((evalpoly(G,z)%128==0)==(z%128==root),'cubic root criterion');lifts+=1
    for t in range(2,alpha+1):
     threshold=3*t+1
     if p<threshold and actual>=threshold:
      ck((k==alpha and k>=2) or (alpha==t and p==3*t and r==(1<<(3*t+1))-3),'low-central dichotomy');low+=1
    records.update(f'{r},{alpha},{z},{actual},{kind}\n'.encode());cases+=1
 # The exceptional family is exact at any t>=2, without full binomial expansion.
 exceptional=[]
 for t in range(2,5):
  r=(1<<(3*t+1))-3;C=[comb(2*r,r+j) for j in range(4)]
  for z in (1,3,5):
   X=(1<<t)*z;val=v(evalpoly(C,X));ck(r.bit_count()==3*t and val>=3*t+1,'explicit exceptional family')
   exceptional.append({'t':t,'r':r,'odd_X_unit':z,'cubic_v2':val})
 return {'helper_sha256':sha(Path(__file__).read_bytes()),'pins':PINS,'exact_cubic_cases':cases,'low_central_passing_cases':low,'linear_resonance_cases':linear,'cubic_resonance_cases':cubic,'binary_lifts_to_seven_bits':lifts,'records_sha256':records.hexdigest(),'exceptional_family':exceptional,'scope':{'t_at_least':2,'actual_source_zero_evaluated':False,'odd_prime_conditions_checked':False,'predecessor_execution':False,'universal83_claim':False}}
def main():
 ap=argparse.ArgumentParser();g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path);a=ap.parse_args();s=json.dumps(build(),indent=2,sort_keys=True)+'\n'
 if a.output:
  with a.output.open('x') as f:f.write(s)
 else:ck(a.expect.read_text()==s,'exact receipt')
 print('PASS fresh exact 2-adic cubic criteria')
if __name__=='__main__':main()
