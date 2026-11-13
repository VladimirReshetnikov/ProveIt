from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-independent-k-main-modular-screen')
for path,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(path).read_bytes()).hexdigest()==h,path
N=67*8807;limit=2_000_000
s=bytearray(b'\x01')*(limit+1);s[:2]=b'\x00\x00'
for p in range(2,int(limit**0.5)+1):
 if s[p]:s[p*p::p]=b'\x00'*(((limit-p*p)//p)+1)
factors=[];count=0
for p in range(2,limit+1):
 if not s[p]:continue
 count+=1;q=pow(2,N,p)
 if (4*pow(q,3,p)*(q+1)+3)%p==0:factors.append(p)
assert factors==[3]
# N and R odd, so both q and 2^R equal 2 modulo 3.
assert N%2==1 and pow(2,N,3)==2 and all(pow(2,r,3)==2 for r in range(1,32,2))
q9=pow(2,N,9);assert (4*pow(q9,3,9)*(q9+1)+3)%9!=0
print(json.dumps({'prime_limit_inclusive':limit,'primes_checked':count,'prime_divisors_of_H_found':factors,'p3_main_congruence':'always passes for the pinned odd R and N','H_not_divisible_by_9':True,'q_and_R_materialized':False,'large_prime_or_prime_power_obstruction_excluded':False,'fixed_main_condition_proved':False,'lean_executed':False},sort_keys=True,indent=2))
