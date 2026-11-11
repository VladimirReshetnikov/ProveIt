#!/usr/bin/env python3
"""Independent CRT order, port pins and finite controls; no Lean."""
import gzip,hashlib,json,math
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary13-folded-root86-negated-compact44-seed'
def read(p,sha):
 x=p.read_bytes();assert hashlib.sha256(x).hexdigest()==sha;return x
final_readme=read(A/'README.md','7d1dc11038b1d12bb7862a226aabf1742823523bcc34adf9a7c82b7e3905c6f5')
link_tail=b'\nIndependent external review is recorded in\n`../../reviews/ordinary13-folded-root86-negated-compact44-seed-independent/`.\nIt independently reconstructs the scalar seed and checks the symbolic Pell\nsteps. Its same-q, same-R parent obstruction does not exclude parent zeros\nat other q or R.\n'
assert final_readme.endswith(link_tail)
assert hashlib.sha256(final_readme[:-len(link_tail)]).hexdigest()=='a83ca2a55a847d3f5cc72f597acff2da858f85c5a65f51fca3b7e96e7124adac'
read(A/'check.py','e64afc3b2e1de86e0d61d50b114fc13bfa268fa68db3ecde2bfcb6cde648764a')
receipt=json.loads(read(A/'result.json','5a781e806480d779095ce81d8481856fb0fe88946e9d980122a9013232912421'))
read(D/'research/ordinary13-folded-root86-negated/candidate.json','186471e8454b9443df2234b25380d6b34d494e951648291645cc492a6d646166')
read(D/'research/current14-carrier64-pell-floor/README.md','8d3b46e7949b7db849a12ef1b6c3586cac661d3158e0347c402581c3b1d08db8')
read(D/'research/ordinary13-folded-root86-toy-full-zero/README.md','ce7d50e76f3b035f7fc87ad0228327be9da41d28455e231610f2bd780f473693')
p=D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13';b=json.loads(read(p/'ACTIVE_BINDING.json','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf')); b115=json.loads(read(D/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json','dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01'));v={}
for n,meta in b['ports'].items():
 assert b115['ports'][n]['sha256_raw']==meta['sha256_raw'] and b115['ports'][n]['sha256_gzip']==meta['sha256_gzip'];z=read(p/meta['path'],meta['sha256_gzip']);x=gzip.decompress(z);assert len(x)==meta['raw_bytes'] and hashlib.sha256(x).hexdigest()==meta['sha256_raw'];v[n]=int.from_bytes(x,'little')
B=590069;beta,K,lo,hi=(v[n] for n in ('beta','K0','MC','MF'));q=beta+1; assert beta==(1<<B)-1 and 0<lo<beta<hi<2*beta and K>0
Q=q*q-1;assert math.gcd(K+1,beta)==math.gcd(Q,B)==math.gcd(beta,B)==1
r_beta=(-pow(K+1,-1,beta))%beta
r_B=(-(beta*beta*(Q%B)+lo+q*hi)*pow(Q%B,-1,B))%B
r_B4=r_B+B*((lo-r_B)*pow(B,-1,4)%4)
a0=r_beta+beta*((r_B4-r_beta)*pow(beta,-1,4*B)%(4*B))
if a0<=beta:a0+=4*B*beta
R0=(beta*beta+a0)*Q+lo+q*hi; period=4*B*beta; W=period*Q; L=R0.bit_length()+1;S=W.bit_length()+1
alpha=a0+period*sum(1<<(L+j*S) for j in range(4));R=(beta*beta+alpha)*Q+lo+q*hi;N=(R-1)//2
sha=lambda n:hashlib.sha256(n.to_bytes((n.bit_length()+7)//8,'big')).hexdigest()
assert alpha>beta and R>=2*B and R%B==0 and R%4==3 and (alpha*(K+1)+1)%beta==0
assert R.bit_length()==receipt['R_bit_length'] and sha(R)==receipt['R_sha256_be'] and sha(alpha)==receipt['alpha_sha256_be'] and N.bit_count()==receipt['N_popcount']>=3*B+1
for m in range(1,30):
 for k in range(2,20): assert (m*k+k)**2 > 1+m*(m+1)*k*k
for b0 in range(1,20):
 q0=b0+1
 for aa in range(b0+1,b0+10):
  G=b0*b0+aa
  for F in range(1,10):assert q0*(q0-F)-G<=b0-aa<0
print(json.dumps({'independent_crt_order':True,'author_R_sha256_be':sha(R),'author_alpha_sha256_be':sha(alpha),'popcount':N.bit_count(),'fixed_q_R_parent_scalar_obstruction':True,'scope':'external symbolic candidate zero, conditional same-q/R parent exclusion; no Lean or unrestricted nonequivalence'},sort_keys=True,indent=2))
