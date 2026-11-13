from pathlib import Path
from hashlib import sha256
import json,math,sys,subprocess
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-i-unshift-more-power-offset-obstructions')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
p=Path('research/ordinary13-i-unshift-fixed-shifted-power-modular-obstructions')
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')])==(p/'receipt.json').read_bytes()
root=Path('Lean/DiophantineConsistency/Compact44')
assert 'def betaNat : ℕ := 2^(67*8807)-1' in (root/'CompactFixedBeta.lean').read_text()
mask=(root/'CompactConcreteMask.lean').read_text()
assert 'range 943 ∪ Ico 983 993 ∪ Ico 1003 1012 ∪ Ico 1013 1032' in mask and '{1063,1064,1095,2195,3296}) \\ {1}' in mask
lst=(root/'CompactListMask.lean').read_text()
assert 'if j=special then B-4 else if j∈S then B-2 else B-1' in lst
hs=(root/'CompactHighPopulation.lean').read_text()
for x in ('def mu : ℕ := 2^51-2','def padding : ℕ := 2^65-1','def lastPadding : ℕ := 2^19-1','[4] ++ List.replicate 1012 0 ++ List.replicate 10 1','List.replicate 42 0 ++ List.replicate 9 1','List.replicate 1121 0 ++ [1] ++ List.replicate 1100 0 ++ [1]','List.replicate 1096 0 ++ [mu] ++ List.replicate 1101 0 ++ [mu]','List.replicate 3296 0 ++ List.replicate 13 padding ++ [lastPadding,0]'):
 assert x in hs
ports=(root/'CompactSymbolicPorts.lean').read_text()
assert '![β,K,L,β+H]' in ports and '8807 1063 CompactConcreteMask.support' in ports and 'CompactHighPopulation.highDigits' in ports
g=json.loads(Path('research/ordinary13-eta-zeta84-unshift-i-signed-full-zero/probe.json').read_text());r={x[0]:x[1:] for x in g['source']}
for name,row in {'q':['+',1,'qm'],'g46':['-','q2',1],'g47':['*','G','g46'],'g48':['*','MF','q'],'g49':['+','MC','g48'],'g50':['*','n_J','g49'],'R':['+','g47','g50']}.items():assert r[name]==row
S=(set(range(943))|set(range(983,993))|set(range(1003,1012))|set(range(1013,1032))|{1063,1064,1095,2195,3296})-{1}
high=[4]+[0]*1012+[1]*10+[0]*42+[1]*9+[0]*1121+[1]+[0]*1100+[1]+[0]*1096+[2**51-2]+[0]*1101+[2**51-2]+[0]*3296+[2**65-1]*13+[2**19-1,0]
assert len(S)==985 and len(high)==8807
prime=761838257287
assert prime>2 and all(prime%d for d in range(3,math.isqrt(prime)+1,2))
assert pow(2,67,prime)==1 and prime*193707721==2**67-1
def residues(mod):
 rho=pow(2,67,mod);beta=(pow(rho,8807,mod)-1)%mod
 low=(beta-sum(pow(rho,j,mod) for j in S)-2*pow(rho,1063,mod))%mod
 h=sum(x*pow(rho,j,mod) for j,x in enumerate(high))%mod
 return rho,beta,low,h,(beta+h)%mod
r3=residues(3);rp=residues(prime)
assert r3==(2,1,1,0,1)
assert rp==(1,0,761838256300,564148635659,564148635659)
R=(rp[2]+rp[4])%prime;assert R==564148634672
D0=(20*R+45)%prime;assert D0==617237091467 and pow(D0,(prime-1)//2,prime)==prime-1
# For h≡1 mod3, the necessary polynomial 0=hR has no L residue.
assert [(L*L+2*L+2)%3 for L in range(3)]==[2,2,1]
# Independent finite controls of the exact exponent identity and specialized
# offsets. These supplement the algebra in README, not a general proof.
for L in range(6,500):
 for h in range(1,min(L+1,31)):
  d=L+1-h
  numer=d*(d+L+1)
  if numer%h:continue
  n=numer//h;m=n+d;R0=2*n-1
  assert (m+L+1)*(m-1)-(L+1)-(m+2*L+2)*(n-1)==0
  assert h*R0==4*L*L+(8-6*h)*L+2*h*h-7*h+4
  if h%3==1 or h in (3,6):assert R0%3!=0
print(json.dumps({'prior_receipt_reproduced':True,'second_prime':prime,'prime_trial_division_through':math.isqrt(prime),'rho_beta_MC_high_MF_mod3':r3,'rho_beta_MC_high_MF_mod_p':rp,'rank_J1_mod_p':R,'h5_completed_square_residue':D0,'euler_residue':prime-1,'h_congruent_one_mod3_all_power_two_q_excluded':True,'h3_h6_all_power_two_q_excluded':True,'h5_J1_excluded':True,'other_J_or_graph_zero_excluded':False,'lean_executed':False},sort_keys=True,indent=2))
