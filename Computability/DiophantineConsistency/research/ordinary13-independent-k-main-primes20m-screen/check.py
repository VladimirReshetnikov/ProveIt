from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-independent-k-main-primes20m-screen')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
N=67*8807;limit=20_000_000
sieve=bytearray(b'\x01')*(limit+1);sieve[:2]=b'\x00\x00'
for p in range(2,int(limit**0.5)+1):
 if sieve[p]:sieve[p*p::p]=b'\x00'*(((limit-p*p)//p)+1)
factors=[];count=0
for p in range(2,limit+1):
 if not sieve[p]:continue
 count+=1;q=pow(2,N,p)
 if (4*pow(q,3,p)*(q+1)+3)%p==0:factors.append(p)
assert count==1_270_607 and factors==[3]
assert N%2==1 and pow(2,N,3)==2
q9=pow(2,N,9);assert (4*pow(q9,3,9)*(q9+1)+3)%9==6
print(json.dumps({'N':N,'inclusive_prime_limit':limit,'primes_checked':count,'prime_divisors_of_H':factors,'p3_congruence':'passes because q and 2^R are both 2 mod 3 for odd R','H_mod_9':6,'q_H_R_materialized':False,'large_factors_screened':False,'main_divisibility_decided':False,'lean_executed':False},sort_keys=True,indent=2))
