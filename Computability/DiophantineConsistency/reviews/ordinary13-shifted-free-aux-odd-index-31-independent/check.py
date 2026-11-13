from pathlib import Path
from hashlib import sha256
import json,sys,subprocess,math
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-shifted-free-aux-odd-index-31-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
p=Path('research/ordinary13-shifted-free-aux-odd-index-31-obstruction')
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')])==(p/'receipt.json').read_bytes()
g=json.loads(Path('research/ordinary13-shifted85-free-aux-square-criterion/candidate.json').read_text());r={x[0]:x[1:] for x in g['source']}
for n,row in {'s':['+','n_s',1],'q':['+',1,'qm'],'X':['*','q','n_w'],'Y':['*','q3','s'],'k':['+','kbase',1],'c':['+','n_eta','kY'],'a':['+','E','Y'],'Delta':['+','H','g17'],'g72':['-','g71','Q'],'Fa':['-','n_y2','g82'],'r0':['-','kbase','R'],'Dstar':['+','g58','g59']}.items():assert r[n]==row,(n,r.get(n))
assert 'def betaNat : ℕ := 2^(67*8807)-1' in Path('Lean/DiophantineConsistency/Compact44/CompactFixedBeta.lean').read_text()
assert pow(2,67*8807,31)==16
# Direct matrix step, not the author's binary Pell-algebra multiplication.
def seq(A,mod,n):
 d=(A*A-1)%mod;x,y=1,0;out=[(x,y)]
 for _ in range(n):x,y=(A*x+d*y)%mod,(x+A*y)%mod;out.append((x,y))
 return out
p=seq(2,31,32);assert p[8]==(0,14) and p[16]==(30,0) and p[32]==(1,0)
for I in (11,20):
 assert I*I%31==28
 s=seq(I,31,65);quot=[x*pow(I,-1,31)%31 for x,y in s[1::2]]
 assert quot[:16]==quot[16:32] and set(quot[:16])=={1,3,8,15,16,23,28,30}
 assert 4 not in quot[:16] and 27 not in quot[:16]
# Validate even subsequence closed residue for all j in bounded A ranges.
for A in range(2,90):
 mod=4*A*A;v=seq(A,mod,4*A)
 for j in range(1,2*A+1):assert v[2*j][1]==((-1)**(j-1)*2*A*j)%mod
 assert v[4*A][1]==0
# Small compact-exponent analogues; H is coprime to q^5*31 and larger
# than both positive divisibility obstructions.
for N in range(3,30):
 q=2**N;Y=31*q**3;a=Y*(q+1);A=a+2;c=2*A;H=4*a+3;U=31*q**5
 assert A%31==2 and A%8==2 and (4*A)%32==8
 assert math.gcd(H,U)==1 and 0<q-4<H and 0<4*q+1<H
 k=2*(q+1);eta=4;nzeta=2*q-3
 assert eta+Y*k==c and k==eta+nzeta+1 and nzeta>=0
 x2=2*A*A-1
 assert x2*x2-(A*A-1)*c*c==1 and (x2-a*c-4)%H==0
print(json.dumps({'author_receipt_reproduced':True,'exact_shifted_child_rows_checked':True,'mod31_pair_period32_verified':True,'odd_quotient_both_roots_independent_sequence':True,'even_subsequence_divisibility_controls':88,'fixed_exponent_signed_main_analogues':27,'full_two_norm_zero_or_reverse_equivalence_proved':False,'lean_executed':False},sort_keys=True,indent=2))
