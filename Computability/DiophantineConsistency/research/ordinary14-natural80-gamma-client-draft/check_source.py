#!/usr/bin/env python3
"""Check proposed client assumptions and finite radix/rank controls; no Lean."""
from pathlib import Path
import hashlib,json,random
P=Path(__file__).resolve().parent;D=P.parents[1]
pins={
 P/'Natural80GammaClient.lean':'7fca431907062c8578970ae7840f37d3710f09f49c0e1e4a784ba7a94cb8288b',
 D/'research/ordinary14-natural80-main-pairs-draft/Natural80MainPairs.lean':'22350958652773aa4f900c69e99b0891b4811168d70c479a4c463bb0924028c0',
 D/'research/ordinary14-natural80-gamma-premises-draft/GammaPremises.lean':'cfdbb97e748edbef9a8bf121cc3e44ac09bc91dc1e60e362b32d675df7ad7192',
 D/'research/ordinary14-natural80-gamma-narrow-draft/GammaZeroNarrow.lean':'f64c3701ac0894998823fee6eaf7497549aa73b7448ae26b327983b6155642a7',
 D/'Lean/DiophantineConsistency/ArithmeticAdaptiveRankWindow2011.lean':'0895f6e74b29c2cc2e4542d739b238352778750da62766819caeb105995fb794',
}
sources={}
for p,h in pins.items():
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h,str(p);sources[p.name]=b.decode()
s=sources['Natural80GammaClient.lean']
for x in ('theorem radix_bounds','theorem gamma_pos_of_80_zero',
          '(hbeta : (p 0 : DiffRing V)=ι beta)', '(hK : (p 1 : DiffRing V)=ι K)',
          '(hMC : (p 2 : DiffRing V)=ι MC)', '(hMF : (p 3 : DiffRing V)=ι MF)',
          '(hb : 0<beta) (hKpos : 0<K) (hMCbound : MC<beta) (hMFbound : MF<2*beta)',
          'units_of_80_zero','gap_of_80_zero','norm_of_80_zero',
          'direct_main_orientation','large_ordinate_of_two_norms','scalar_rank_window',
          'narrow_inequalities','gamma_zero_impossible',
          '#print axioms DiophantineConsistency.Natural80GammaClientDraft.radix_bounds',
          '#print axioms DiophantineConsistency.Natural80GammaClientDraft.gamma_pos_of_80_zero'):
 assert x in s,x
assert 'sorry' not in s and 'admit' not in s
rng=random.Random(148080);controls=0
for _ in range(500):
 beta=rng.randrange(2,10);J=rng.randrange(1,6);q=beta*J+1
 F=rng.randrange(1,q-1);alpha=rng.randrange(1,q-F)
 MC=rng.randrange(beta);MF=rng.randrange(2*beta)
 w=rng.randrange(1,5);ss=rng.randrange(1,5)
 X=q*w;Y=q**3*ss;m=X*Y*Y;k=8*m+4;eta=1
 R=(alpha+(q-F)*J*beta)*(q*q-1)+J*(MC+MF*q)
 assert q>=2 and q<=X and q**3<=Y and Y>=8
 assert F+alpha<q and R+q**3+q+1<=q**4
 assert R+1<k and X<eta+Y*k
 controls+=1
print(json.dumps({'scope':'unelaborated client source and finite arithmetic controls only',
                  'represented_four_ports_and_rank_bounds_explicit':True,
                  'no_positive_gamma_premise':True,'finite_radix_rank_controls':controls,
                  'axiom_print_commands_not_executed':2,'no_model_ipra_or_byte_claim':True},sort_keys=True,indent=2))
