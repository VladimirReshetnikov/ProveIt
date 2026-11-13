#!/usr/bin/env python3
"""Static source pins and markers; not Lean elaboration."""
import hashlib
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
PINS={
 'research/current2011-shear-current-port-cast-draft/CurrentPortCast.lean.src':'be27b59b37e99d41eb90f6913ef6f19f0d943581c51ded85477477e9f46fc320',
 'research/current2011-shear-forward-index-binding-draft/ForwardIndex.lean.src':'fb39f3cb211700acd7e431da2f7a4e95a256a4a6f98087f8db0cb163beb9101a',
 'research/current2011-shear-rank-cast-generic-draft/RankCast.lean.src':'e66627d9c499e178cfb5005aaad5188fd05ba8d6586d7627be28e654b5f2b602',
 'Lean/DiophantineConsistency/CurrentKernelData2011.lean':'529b2f89e4e93516a8a52343d98dc749c57f5a967d8ef522b92373bf3adf0a2c',
 'Lean/DiophantineConsistency/CurrentMaskData2011.lean':'8e92c1f507bc250c31fb2671a921dfbef7a44ba643956f962cd64d9b50bd4582',
}
for name,h in PINS.items():
 if hashlib.sha256((ROOT/name).read_bytes()).hexdigest()!=h: raise RuntimeError('source pin changed: '+name)
mask=(ROOT/'Lean/DiophantineConsistency/CurrentMaskData2011.lean').read_text()
kernel=(ROOT/'Lean/DiophantineConsistency/CurrentKernelData2011.lean').read_text()
src=(ROOT/'research/current2011-shear-current-port-cast-draft/CurrentPortCast.lean.src').read_text()
if '![beta, K, lowPort, highPort + beta]' not in mask or 'CurrentMasks2011.ports (K : ℤ)' not in kernel:
 raise RuntimeError('current tuple source changed')
for marker in ['theorem currentP_eq_embedded','theorem core_q_cast','theorem core_c_cast','theorem core_rank_cast','theorem ring_half_at_parent_zero','gap_implies_F_le_q','ring_half_of_casts v hz (core_rank_cast v hF) (core_c_cast v)']:
 if marker not in src: raise RuntimeError('source marker missing: '+marker)
print(json.dumps({'scope':'static source/tuple markers only; all draft proofs unelaborated',
 'pinned_sources':len(PINS),'high_port_beta_shift_count':1,'proposed_casts_without_extra_premises':True},indent=2,sort_keys=True))
