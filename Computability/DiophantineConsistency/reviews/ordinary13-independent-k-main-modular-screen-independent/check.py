from pathlib import Path
from hashlib import sha256
import math,json,sys,subprocess
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-independent-k-main-modular-screen-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
for name in ('ordinary13-independent-k-main-modular-screen','ordinary13-independent-k-fixed-slice-conditional'):
 p=Path('research')/name;assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')])==(p/'receipt.json').read_bytes()
source=Path('Lean/DiophantineConsistency/Compact44/CompactFixedBeta.lean').read_text()
assert 'def betaNat : ℕ := 2^(67*8807)-1' in source
G=json.loads(Path('research/ordinary13-eta-zeta84-independent-k-candidate/candidate.json').read_text());r={z[0]:z[1:] for z in G['source']}
for name,row in {'q':['+',1,'qm'],'X':['*','q','n_w'],'q2':['*','q','q'],'q3':['*','q','q2'],'Y':['*','q3','s'],'E':['*','X','Y'],'a':['+','E','Y'],'g15':['*',4,'a'],'H':['+',3,'g15']}.items():assert r[name]==row,(name,r[name])
N=67*8807;bound=2000000;B=4096
# Independent segmented sieve with separately trial-divided base primes.
base=[]
for x in range(2,math.isqrt(bound)+1):
 if all(x%p for p in base if p*p<=x):base.append(x)
count=0;div=[]
for lo in range(2,bound+1,B):
 hi=min(bound+1,lo+B);a=bytearray(b'\x01')*(hi-lo)
 for p in base:
  start=max(p*p,((lo+p-1)//p)*p)
  if start<hi:a[start-lo::p]=b'\x00'*(((hi-1-start)//p)+1)
 for i in range(hi-lo):
  if a[i]:
   p=lo+i;count+=1;q=pow(2,N,p)
   if (4*(pow(q,4,p)+pow(q,3,p))+3)%p==0:div.append(p)
assert count==148933 and div==[3]
q3=pow(2,N,3);q9=pow(2,N,9)
assert N==590069 and N%2==1 and q3==2 and q9==5
assert (4*(q9**4+q9**3)+3)%9==6
# Fixed-slice R odd follows from q even, MC even, and G=q*t-1.
for q in range(2,50,2):
 for t in range(1,8):
  for mc in range(0,20,2):
   for mf in range(6):
    R=(q*t-1)*(q*q-1)+mc+q*mf
    assert R%2==1 and pow(2,R,3)==q3
low=Path('Lean/DiophantineConsistency/Compact44/CompactLowEven.lean').read_text()
assert 'theorem low_even' in low
ports=Path('Lean/DiophantineConsistency/Compact44/CompactSymbolicPorts.lean').read_text()
assert 'def ports (β K L H : ℕ) : Fin 4 → ℕ := ![β,K,L,β+H]' in ports
print(json.dumps({'author_and_fixed_slice_receipts_reproduced':True,'independent_segmented_sieve_bound_inclusive':bound,'primes_checked':count,'small_prime_factors_of_H':div,'graph_H_formula_wiring_checked':True,'q_mod_3':q3,'q_mod_9':q9,'H_mod_9':6,'odd_rank_mod_3_controls_checked':True,'fixed_main_condition_proved':False,'lean_executed':False},sort_keys=True,indent=2))
