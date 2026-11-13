from pathlib import Path
from hashlib import sha256
import json,random,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/current2011-shear-current-port-cast-second-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
base='research/current2011-shear-current-port-cast-draft/'
assert subprocess.run([sys.executable,'-I','-S','-B',base+'check.py'],stdout=subprocess.PIPE,check=True,timeout=15).stdout==Path(base+'result.json').read_bytes()
s=Path(base+'CurrentPortCast.lean.src').read_text();m=Path('Lean/DiophantineConsistency/CurrentMaskData2011.lean').read_text();c=Path('Lean/DiophantineConsistency/Carrier65.lean').read_text();r=Path('Lean/DiophantineConsistency/ArithmeticCarrierRadix2011.lean').read_text();f=Path('research/current2011-shear-forward-index-binding-draft/ForwardIndex.lean.src').read_text();g=Path('research/current2011-shear-rank-cast-generic-draft/RankCast.lean.src').read_text()
for tok in ['![beta, K, lowPort, highPort + beta]']:assert tok in m
for tok in ['(CurrentMasks2011.highPort+CurrentMasks2011.beta:ℕ):V','theorem currentP_eq_embedded','theorem core_q_cast','theorem core_c_cast','theorem core_rank_cast','gap_implies_F_le_q (natural_gap_and_half v hz).1','ring_half_of_casts v hz (core_rank_cast v hF) (core_c_cast v)']:assert tok in s,tok
for tok in ['let q := b + 1','let c := k * Y + eta','let rank := (b * (q - F) + alpha) * (q ^ 2 - 1) + (p 2 + q * p 3) * J']:assert tok in c,tok
for tok in ['def q (v : Fin 14 → V)', 'def Y (v : Fin 14 → V)', 'def rank (v : Fin 14 → V)', '(CurrentMasks2011.highPort+CurrentMasks2011.beta:ℕ):V']:assert tok in r,tok
for tok in ['def shifted (v : Fin 14 → V)', 'def shiftedRing (v : Fin 14 → V)', 'theorem natural_gap_and_half','theorem ring_half_of_casts']:assert tok in f,tok
for tok in ['theorem cast_tsub_of_le', 'theorem gap_implies_F_le_q','theorem rank_cast', '(hF : F ≤ q)']:assert tok in g,tok
rng=random.Random(71246)
for _ in range(900):
 beta=rng.randrange(1,10);J=rng.randrange(1,8);q=beta*J+1;F=rng.randrange(q+1);alpha=rng.randrange(8)
 low=rng.randrange(9);high=rng.randrange(9);mf=high+beta;s0=rng.randrange(1,5);eta=rng.randrange(1,5);zeta=rng.randrange(1,5)
 qring=beta*J+1;Y=s0*q**3;cN=(eta+zeta)*Y+eta;cR=(eta+zeta)*(s0*qring**3)+eta
 natural=(max(q-1,0)*max(q-F,0)+alpha)*max(q*q-1,0)+(low+q*mf)*J
 ring=(beta*J*(qring-F)+alpha)*(qring*qring-1)+(low+qring*mf)*J
 assert q==qring and cN==cR and natural==ring
q=2;F=3
assert max(q-F,0)!=q-F
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),'author_static_check_reproduced':True,'independent_integer_controls':900,'rank_cast_needs_F_le_q_counterexample':True,'lean_executed':False,'all_model_proof_or_provider_authenticated':False},sort_keys=True,indent=2))
