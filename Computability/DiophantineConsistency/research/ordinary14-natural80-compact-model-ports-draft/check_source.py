#!/usr/bin/env python3
"""Bounded source/signature inventory; no Lean or model proof check."""
from pathlib import Path
import hashlib,json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
pins={
'research/ordinary14-natural80-compact-model-ports-draft/Natural80CompactModelPorts.lean':'7bf66a61ec2281d2826c04c6321fb22acd1ca1e9afedb8c4fa22905d5a0fc7b4',
'research/ordinary14-compact-port-bounds-slim-draft/CompactPortBoundsSlim.lean':'fb35a320b1521b3005feb597ace302ea9779304839a952b9590f6e0b9a6b4fa4',
'research/ordinary14-strict-k0-symbolic-source-draft/StrictK0Symbolic.lean':'7b694e0aa874a1d321cc348db26d2aa56a6dc6509b331b6bb3dfdd9c1d6ce31a',
'Lean/DiophantineConsistency/Compact44/CompactConcreteMask.lean':'f93993e8b4badb6518d8ac6e575d406f322d7205b7d95c17c185103510b474c2',
'Lean/DiophantineConsistency/Compact44/CompactSymbolicModelIff.lean':'379616890bb253e86d6defdc2424793e187be8c949e7a186d231bb024c2f1f46',
'Lean/DiophantineConsistency/Compact44/CompactSymbolicPorts.lean':'0fc8eb4f60e801b38a3a516cd23d9f44c1e9eda62609d34bd76764de7ac51414',
'Lean/DiophantineConsistency/Compact44/CompactFixedBeta.lean':'bcb892e7ae6b0d3cf329a248ca6b468e36a9a1b582d75cacafb7fd49f89025ea',
'Lean/DiophantineConsistency/ArithmeticWindowDigits.lean':'8f09db2fbd93de5351c7f5daedd6c6b3fac00cbd8d8e3f3cdc7e02945a25605b',
'Lean/DiophantineConsistency/ArithmeticAdaptiveRankWindow2011.lean':'0895f6e74b29c2cc2e4542d739b238352778750da62766819caeb105995fb794',
'Lean/DiophantineConsistency/ArithmeticStandardCasts.lean':'8f7014e3f71cae1b7afb3d0ca97eaba73965b544bbc95fd8f7887e71ae46417b',
'Lean/DiophantineConsistency/ModelDifferenceRing.lean':'5f8007e437fe309d0801bed075c03dc7ef5e7cba0138210aa1805e43a0869998',
}
s={}
for p,h in pins.items():
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;s[Path(p).name]=b.decode()
def norm(x):return re.sub(r'\s+',' ',x)
def dec(name,term):
 text=s[name];m=re.search(r'\b(?:def|theorem)\s+'+re.escape(term)+r'\b(.*?)(?=\s+:=\s*by\b)',text,re.S);assert m,(name,term);return norm(m.group(1))
ports=s['CompactSymbolicPorts.lean'];assert '![β,K,L,β+H]' in ports
assert 'ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat j:ℤ' in norm(s['CompactSymbolicModelIff.lean'])
assert 'def betaNat : ℕ := 2^(67*8807)-1' in s['CompactFixedBeta.lean']
slim=dec('CompactPortBoundsSlim.lean','port_bounds')
for t in ('(ports B K L H 0 : V)', '(ports B K L H 2 : V)', '(ports B K L H 3 : V)', '(46 : V)', '(hB :', '(hL :', '(hH :'):assert t in slim,t
assert '0 < (paramKernel rho : V)' in dec('StrictK0Symbolic.lean','kernel_model_pos')
origin=dec('CompactConcreteMask.lean','model_origin')
for t in ('dig 67', 'Exp.exp 67-2'):assert t in origin,t
assert 'theorem dig_zero_index' in s['ArithmeticWindowDigits.lean']
rank=dec('ArithmeticAdaptiveRankWindow2011.lean','scalar_rank_window')
for t in ('(hbeta : 0<beta)', '(hMC : MC<beta)', '(hMF : MF<2*beta)'):assert t in rank,t
client=s['Natural80CompactModelPorts.lean'];rep=dec('Natural80CompactModelPorts.lean','port_representation')
assert '(CompactSymbolicModelIff.p j : DiffRing V) = ι (modelPorts (V:=V) j)' in rep
bound=dec('Natural80CompactModelPorts.lean','port_bounds')
for t in ('0 < modelPorts (V:=V) 0','(46 : V) ≤ modelPorts (V:=V) 0','0 < modelPorts (V:=V) 1','0 < modelPorts (V:=V) 2','modelPorts (V:=V) 2 < modelPorts (V:=V) 0','0 < modelPorts (V:=V) 3','modelPorts (V:=V) 3 < 2 * modelPorts (V:=V) 0'):assert t in bound,t
for t in ('CompactPortBoundsSlimDraft.port_bounds', 'StrictK0SymbolicDraft.kernel_model_pos','CompactConcreteMask.model_origin','ArithmeticStandardCasts.cast_exp', 'exp_monotone_le.mpr','tsub_pos_iff_lt.mpr','ArithmeticWindowDigits.dig'):
 assert t in client,t
for t in ('port_representation','low_model_pos','port_bounds'):
 assert '#print axioms DiophantineConsistency.Natural80CompactModelPortsDraft.'+t in client
assert 'sorry' not in client and 'admit' not in client
print(json.dumps({'scope':'pinned source/signature audit only; no Lean elaboration, model theorem, iPRA or byte/PDF binding','pinned_files':len(pins),'model_ports':['beta','K0','MC','beta+highNat'], 'proposed_bounds':['beta>0','beta>=46','K0>0','MC>0','MC<beta','MF>0','MF<2*beta'], 'unexecuted_axiom_commands':3},sort_keys=True,indent=2))
