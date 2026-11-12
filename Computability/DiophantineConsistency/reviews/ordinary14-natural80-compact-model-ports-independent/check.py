#!/usr/bin/env python3
"""Independent source/signature audit of proposed model ports; no Lean."""
from pathlib import Path
import hashlib,json,re
D=Path(__file__).resolve().parents[2]
files={
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
'Lean/DiophantineConsistency/Compact44/CompactKernelSplit.lean':'3614e342fd80f60feab91e0f5da514b2d266a3cfba800a270380a1855a3a6420',
'Lean/DiophantineConsistency/Compact44/CompactSymbolicKernel.lean':'9b2b73430cbf4578ef4b4c7d4658c9526b7ebdc423263470df907a16b454ba55'}
s={}
for p,h in files.items():
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;s[p.rsplit('/',1)[-1]]=b.decode()
a=s['Natural80CompactModelPorts.lean'];slim=s['CompactPortBoundsSlim.lean'];fixed=s['CompactFixedBeta.lean'];kp=s['StrictK0Symbolic.lean'];ports=s['CompactSymbolicPorts.lean'];model=s['CompactSymbolicModelIff.lean'];mask=s['CompactConcreteMask.lean'];digits=s['ArithmeticWindowDigits.lean'];casts=s['ArithmeticStandardCasts.lean'];rank=s['ArithmeticAdaptiveRankWindow2011.lean'];split=s['CompactKernelSplit.lean'];rho=s['CompactSymbolicKernel.lean']
def hdr(src,name):
 m=re.search(r'\btheorem\s+'+re.escape(name)+r'\b(.*?)\s*:=\s*by',src,re.S);assert m,name
 return ' '.join(m.group(1).split())
assert 'def ports (β K L H : ℕ) : Fin 4 → ℕ := ![β,K,L,β+H]' in ports
assert 'def lowNat : ℕ := Nat.ofDigits (2^67) (CompactListMask.digits (2^67) 8807 1063 CompactConcreteMask.support)' in ports
assert 'def p : Fin 4 → ℤ := fun j => (ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat j:ℤ)' in model
assert 'def naturalPorts : Fin 4 → ℕ :=' in a and 'ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat' in a
rep=hdr(a,'port_representation');assert '(CompactSymbolicModelIff.p j : DiffRing V) = ι (modelPorts (V:=V) j)' in rep
assert 'theorem kernel_split_generic (r : ℕ) : paramKernel r = r ^ 8849 + lowerKernelAt r' in split
assert 'def rho : ℕ := 2^67' in rho and '0 < (paramKernel rho : V)' in hdr(kp,'kernel_model_pos')
assert 'def betaNat : ℕ := 2^(67*8807)-1' in fixed and 'theorem beta_identity' in fixed
hb=hdr(slim,'port_bounds')
for x in ('(hB : (B : V) + 1 = Exp.exp ((67 : V) * 8807))','(hL : L = lowNat)','(hH : H = highNat)',
 '0 < (ports B K L H 0 : V)','(ports B K L H 2 : V) < (ports B K L H 0 : V)',
 '(ports B K L H 3 : V) < 2 * (ports B K L H 0 : V)','(46 : V) ≤ (ports B K L H 0 : V)'):
 assert x in hb,x
origin=hdr(mask,'model_origin')
assert 'dig 67 ((Nat.ofDigits (2^67) (digits (2^67) 8807 1063 support) : ℕ):V) 0' in origin
assert 'Exp.exp 67-2' in origin and 'open CompactListMask' in mask
assert 'noncomputable def dig (w X k : V) : V := X / Exp.exp (w*k) % Exp.exp w' in digits
assert 'theorem cast_exp (n : ℕ) : Exp.exp (n:V) = ((2^n : ℕ) : V)' in casts
for x in ('CompactConcreteMask.model_origin','ArithmeticStandardCasts.cast_exp (V:=V) 2',
 'exp_monotone_le.mpr','tsub_pos_iff_lt.mpr','simp [ArithmeticWindowDigits.dig]',
 'StrictK0SymbolicDraft.kernel_model_pos','CompactPortBoundsSlimDraft.port_bounds'):
 assert x in a,x
bound=hdr(a,'port_bounds')
for x in ('0 < modelPorts (V:=V) 0','(46 : V) ≤ modelPorts (V:=V) 0',
 '0 < modelPorts (V:=V) 1','0 < modelPorts (V:=V) 2',
 'modelPorts (V:=V) 2 < modelPorts (V:=V) 0',
 '0 < modelPorts (V:=V) 3','modelPorts (V:=V) 3 < 2 * modelPorts (V:=V) 0'):
 assert x in bound,x
rankhdr=hdr(rank,'scalar_rank_window')
for x in ('(hbeta : 0<beta)','(hJ : 0<J)','(hF : 0<F)','(halpha : 0<alpha)',
 '(hMC : MC<beta)','(hMF : MF<2*beta)','(hq : q=beta*J+1)','(hgap : F+alpha<q)'):
 assert x in rankhdr,x
for name in ('port_representation','low_model_pos','port_bounds'):
 assert '#print axioms DiophantineConsistency.Natural80CompactModelPortsDraft.'+name in a
assert 2**67>2 and (2**67-2)>0 and (0//(2**(67*0)))%(2**67)==0
print(json.dumps({'scope':'bounded source/signature and digit reasoning audit; no Lean or physical-byte theorem',
 'pinned_sources':len(files),'symbolic_tuple':['beta','K0','MC','beta+highNat'],
 'MC_origin_digit_positive_reason_checked':True,'rank_other_input_premises_remain':True,
 'axiom_commands_unexecuted':3},sort_keys=True,indent=2))
