#!/usr/bin/env python3
"""Bounded source-interface survey of decimal port bridge; no Lean or writes."""
from pathlib import Path
import hashlib,json,re,sys
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode):raise SystemExit('Use python3 -I -S -B')
D=Path(__file__).resolve().parents[2]
files={
 'bridge':('research/ordinary14-natural79-decimal-render-candidate/Natural79DecimalPortBridge.lean.src','137ee4023ab657552c329e8ef8c2d38afab9c4e6c0d790b50b7080361df6b1cd'),
 'seed':('research/ordinary14-natural79-decimal-render-candidate/DECIMAL_SEED.txt','8c85329f040c7a4d41d521deee0dec970191ff59e08ccf5487e32655dc09a297'),
 'endpoint':('research/ordinary14-natural79-beta-only-overlay/source/Natural79Endpoint.lean.src','da1bbfbc339c26ea5763e5ff4c1aaa885898dab9c3fafd21854b8b69e5c54b7b'),
 'decimal_review':('reviews/ordinary14-natural79-decimal-render-independent/result.json','6b68ea9e4b7cddb643b191769a3621d15b3d73029903048ff2236cfc95e34274'),
 'byte_tuple':('Lean/DiophantineConsistency/Compact44/CompactFourPortByteAssembly2.lean','3f863dde2c2c5bc3b5dd9789d2e2f5ae70c5856482979b577a4e405f6d7c019e'),
 'byte_int':('Lean/DiophantineConsistency/Compact44/CompactBytePortsModelIff.lean','6a6a15e046bf82817c28e0df884b24f52c0741e24d92149e485fe33836db042d'),
 'list_mask':('Lean/DiophantineConsistency/Compact44/CompactListMask.lean','34c4d38c265160155a7fa3f99ea3af692c5f3be10b7b77cac211afc199953d4b'),
 'low_recipe':('Lean/DiophantineConsistency/Compact44/CompactConcreteMask.lean','f93993e8b4badb6518d8ac6e575d406f322d7205b7d95c17c185103510b474c2'),
 'ports':('Lean/DiophantineConsistency/Compact44/CompactSymbolicPorts.lean','0fc8eb4f60e801b38a3a516cd23d9f44c1e9eda62609d34bd76764de7ac51414'),
 'model_tuple':('Lean/DiophantineConsistency/Compact44/CompactSymbolicModelIff.lean','379616890bb253e86d6defdc2424793e187be8c949e7a186d231bb024c2f1f46'),
 'kernel':('Lean/DiophantineConsistency/Compact44/CompactSymbolicKernelOpaque.lean','8ae9ed11d9e7408e4fd71555569181b0fb785f24f3177facc6c6c997d0d5e615'),
 'slots':('Lean/DiophantineConsistency/Compact44/CompactSymbolicKernel.lean','9b2b73430cbf4578ef4b4c7d4658c9526b7ebdc423263470df907a16b454ba55'),
 'high':('Lean/DiophantineConsistency/Compact44/CompactHighPopulation.lean','b1e962aed2f9fc2b49533a52f3508a84af4d433c4a9fae210540e085056dab1d'),
 'beta':('Lean/DiophantineConsistency/Compact44/CompactFixedBeta.lean','bcb892e7ae6b0d3cf329a248ca6b468e36a9a1b582d75cacafb7fd49f89025ea'),
 'selector':('Lean/DiophantineConsistency/Compact44/CompactCoefficientMass.lean','1dad41ebf3fe6c9c68b6f6d76bd6d1a42f318ca75eb6f107d3bcd0407246b592'),
 'table':('Lean/DiophantineConsistency/Compact44/Compact943Data.lean','10a75f23bf358ac745949b9d2717da33c8ccbc4e069892128b913d78d43617f8'),
 'radix':('Lean/DiophantineConsistency/Compact44/SparseRadix.lean','1e9f64186090cc13c77c8f704ff0291928e35700390833c70333e5fc386f65fa'),
 'digits_append':('Lean/DiophantineConsistency/ArithmeticMaskData.lean','751b53e808f4fd17ccf33f4759489feb9d01da67d09fa80b586f4bfc02fac72e'),
 'native_no_zero':('Lean/DiophantineConsistency/IPRAExpressionNative.lean','f2ecaf302d2e41f7d85a4c5c078f7c9a47f69b8ae4ee40d9b320b4817636b8e8'),
 'model_zero':('Lean/DiophantineConsistency/ModelDifferenceRing.lean','5f8007e437fe309d0801bed075c03dc7ef5e7cba0138210aa1805e43a0869998')}
t={}
for k,(p,h) in files.items():
 raw=(D/p).read_bytes();assert hashlib.sha256(raw).hexdigest()==h,k;t[k]=raw.decode()
assert len(t['seed'].strip())==15086 and t['seed'].strip().isdecimal()
for x in ['(hb : beta = CompactFixedBeta.betaNat)','(hk : K = paramKernel rho)',
 '(hl : low = lowNat)','(hh : shiftedHigh = CompactFixedBeta.betaNat + highNat)',
 'Natural79EndpointDraft.native_equivalence','![beta,K,low,shiftedHigh]']:
 assert x in t['bridge'],x
assert 'def expression : Expr (Fin 14) := (P79NaturalForcedW.graph CompactSymbolicModelIff.p).output' in t['endpoint']
assert 'def betaNat : ℕ := 2^(67*8807)-1' in t['beta']
assert 'def rho : ℕ := 2^67' in t['slots'] and 'theorem slots_length : slots.length = 41' in t['slots']
assert 'def paramKernel (r : ℕ) : ℕ :=' in t['kernel'] and 'r^8807*r^42' in t['kernel']
assert 'def selector (t : Nat × Nat × Nat × Nat) : Nat := 1 + 2^10 * (2^41 - value t)' in t['selector']
assert 'theorem rows_length : rows.length=943' in t['table']
assert 'theorem digit_ofDigits (b : ℕ) (L : List ℕ) (hb : 0 < b)' in t['radix']
assert '(Nat.ofDigits b L / b ^ i) % b = L[i]' in t['radix']
assert 'theorem concrete_recipe :' in t['low_recipe'] and '2*(2^67)^1063' in t['low_recipe']
assert 'def highDigits : List ℕ :=' in t['high'] and 'theorem digits_length : highDigits.length = 8807' in t['high']
assert 'theorem ofDigits_replicate_append (b n a : ℕ) (l : List ℕ)' in t['digits_append']
assert 'def ports (β K L H : ℕ) : Fin 4 → ℕ := ![β,K,L,β+H]' in t['ports']
assert 'def p : Fin 4 → ℤ := fun j => (ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat j:ℤ)' in t['model_tuple']
assert 'theorem decode_ports :' in t['byte_tuple'] and 'Nat.ofDigits 256 (bytePorts j)' in t['byte_tuple']
assert 'theorem byteP_eq : byteP = p' in t['byte_int']
assert 'def nativeNoZero' in t['native_no_zero'] and 'theorem internalZero_iff' in t['model_zero']
print(json.dumps({'scope':'pinned source-interface assessment only; no Lean, authenticated providers or file semantics',
 'inputs':{k:{'path':p,'sha256':h} for k,(p,h) in sorted(files.items())},
 'decimal_digits':15086,'decimal_block_count':943,'decimal_block_width':16,'leading_zero_padding':2,
 'bridge_requires_four_natural_equalities':True,'byte_recipes_not_physical_file_theorems':True,
 'draft_axiom_report_unexecuted':True},sort_keys=True,indent=2))
