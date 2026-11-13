#!/usr/bin/env python3
"""Finite checks for the fixed-port shifted Pell-index congruences."""
import hashlib, json, math
from pathlib import Path
root=Path(__file__).resolve().parents[2]
here=Path(__file__).resolve().parent
for name,digest in json.loads((here/'pins.json').read_text()).items():
    assert hashlib.sha256((root/name).read_bytes()).hexdigest()==digest, name

def require(name,*strings):
    text=(root/name).read_text()
    for s in strings: assert s in text,(name,s)
require('Lean/DiophantineConsistency/Compact44/CompactFixedBeta.lean',
        'def betaNat : ℕ := 2^(67*8807)-1')
require('Lean/DiophantineConsistency/Compact44/CompactConcreteMask.lean',
        'range 943 ∪ Ico 983 993 ∪ Ico 1003 1012 ∪ Ico 1013 1032',
        '{1063,1064,1095,2195,3296}) \\ {1}',
        '(2^67)^8807 - 1 - (∑ j ∈ support, (2^67)^j) - 2*(2^67)^1063')
require('Lean/DiophantineConsistency/Compact44/CompactHighPopulation.lean',
        'def mu : ℕ := 2^51-2', 'def padding : ℕ := 2^65-1',
        'def lastPadding : ℕ := 2^19-1',
        '[4] ++ List.replicate 1012 0 ++ List.replicate 10 1 ++',
        'List.replicate 42 0 ++ List.replicate 9 1 ++',
        'List.replicate 1121 0 ++ [1] ++ List.replicate 1100 0 ++ [1] ++',
        'List.replicate 1096 0 ++ [mu] ++ List.replicate 1101 0 ++ [mu] ++',
        'List.replicate 3296 0 ++ List.replicate 13 padding ++ [lastPadding,0]')
require('Lean/DiophantineConsistency/Compact44/CompactSymbolicPorts.lean',
        'def lowNat : ℕ := Nat.ofDigits (2^67) (CompactListMask.digits (2^67) 8807 1063 CompactConcreteMask.support)',
        'def highNat : ℕ := Nat.ofDigits (2^67) CompactHighPopulation.highDigits',
        '![β,K,L,β+H]')
rows={x[0]:x[1:] for x in json.loads((root/'research/ordinary13-eta-zeta84-unshift-i-signed-full-zero/probe.json').read_text())['source']}
for k,v in {'qm':['*','n_J','beta'],'q':['+',1,'qm'],'q2':['*','q','q'],
            'g46':['-','q2',1],'g47':['*','G','g46'],'g48':['*','MF','q'],
            'g49':['+','MC','g48'],'g50':['*','n_J','g49'],'R':['+','g47','g50']}.items():
    assert rows[k]==v,(k,rows[k])
S=(set(range(943))|set(range(983,993))|set(range(1003,1012))|
   set(range(1013,1032))|{1063,1064,1095,2195,3296})-{1}
h=[4]+[0]*1012+[1]*10+[0]*42+[1]*9+[0]*1121+[1]+[0]*1100+[1]+[0]*1096+[2**51-2]+[0]*1101+[2**51-2]+[0]*3296+[2**65-1]*13+[2**19-1,0]
assert len(S)==985 and len(h)==8807
p=193707721
assert all(p%d for d in range(2,math.isqrt(p)+1))
def residues(mod):
    rho=pow(2,67,mod); beta=(pow(rho,8807,mod)-1)%mod
    low=(beta-sum(pow(rho,i,mod) for i in S)-2*pow(rho,1063,mod))%mod
    high=0
    for x in reversed(h): high=(rho*high+x)%mod
    assert high==sum(x*pow(rho,i,mod) for i,x in enumerate(h))%mod
    return rho,beta,low,high,(beta+high)%mod
r3=residues(3); rp=residues(p)
assert r3==(2,1,1,0,1)
assert rp==(1,0,193706734,55802646,55802646)
# q=2^t is nonzero mod 3 and J≡q-1. Verify both possible residues.
assert all(((q-1)*(1+q))%3==0 for q in (1,2))
assert [(4*x*x+2*x-1)%3 for x in range(3)]==[2,2,1]
# At p and J=1 q=1, so rank≡low+high. Complete square  (4L-2)^2 = 8R+12.
c=(rp[2]+rp[4])%p
disc=(12+8*c)%p
euler=pow(disc,(p-1)//2,p)
assert c==55801659 and disc==58997842 and euler==p-1
# This is an algebraic identity and finite control, not proof from sampling.
for L in range(4,200):
    n=L*(L-1); d=L-1; m=n+d
    assert n*(L+1-d)==d*(d+L+1)
    assert (m-1)*(m+L+1)==L+1+(n-1)*(m+2*L+2)
    assert 4*(m-1)<2**(m-L)
print(json.dumps({'prime':p,'prime_trial_division_to':math.isqrt(p),
 'rho_beta_MC_high_MF_mod3':r3,'rho_beta_MC_high_MF_mod_p':rp,
 'rank_J1_mod_p':c,'discriminant_mod_p':disc,'euler_residue':euler,
 'd_equal_L_all_power_of_two_q_excluded':True,'d_equal_L_minus_1_J1_excluded':True,
 'd_equal_L_minus_1_other_J_excluded':False,'eta_interval_compatible_at_leading_power_level':True,
 'graph_zero_nonexistence_proved':False,'lean_executed':False,'huge_compact_values_expanded':False},indent=2,sort_keys=True))
