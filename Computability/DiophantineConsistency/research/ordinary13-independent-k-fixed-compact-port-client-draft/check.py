from pathlib import Path
from hashlib import sha256
import json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-independent-k-fixed-compact-port-client-draft')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
s=(D/'IndependentKFixedCompactPorts.lean.src').read_text()
for n in ('fixed_ports_eq_retained','port_cast','bounds','child_J_positive','zero_k_fact_cut'):
 assert len(re.findall(r'^theorem '+n+r'\b',s,re.M))==1
 assert '#print axioms DiophantineConsistency.IndependentKFixedCompactPortsDraft.'+n in s
for x in ['def natPorts : Fin 4 → ℕ := C44Short15Facts.c44','CompactSymbolicModelIff.p',
 'P72Root.cast_port (V:=V) natPorts j','C44Short15Facts.port_bounds (V:=V)',
 'C44Short15Facts.K_pos (V:=V)','IndependentKJPositiveDraft.J_positive natPorts v',
 'IndependentKFirstRankDiscreteDraft.zero_k_impossible','(hfirst : let b : DiffRing V',
 '(hrank : (ι R : DiffRing V)=','(hshape : let a:=X*Y+Y','(hnorm : let a:=X*Y+Y']:
 assert x in s,x
assert not re.search(r'\b(?:sorry|admit|axiom)\b',s)
f=Path('Lean/DiophantineConsistency/Compact44/C44Short15Facts.lean').read_text()
assert 'abbrev c44 : Fin 4 → ℕ := ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat' in f
assert 'theorem port_bounds (B K L H : ℕ)' in f and 'theorem K_pos (B K L H : ℕ)' in f
model=Path('Lean/DiophantineConsistency/Compact44/CompactSymbolicModelIff.lean').read_text()
assert 'def p : Fin 4 → ℤ := fun j => (ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat j:ℤ)' in model
assert 'def ports (β K L H : ℕ) : Fin 4 → ℕ := ![β,K,L,β+H]' in Path('Lean/DiophantineConsistency/Compact44/CompactSymbolicPorts.lean').read_text()
g=json.loads(Path('research/ordinary13-eta-zeta84-independent-k-candidate/candidate.json').read_text())
assert g['fixed_numerals']==['beta','K0','MC','MF']
assert g['witnesses'][0:3]==['n_J','n_F','n_alpha'] and g['witnesses'][7:11]==['n_s','n_r','n_eta','n_k'] and g['witnesses'][12]=='n_gamma'
assert '(natPorts 0:V) (v 0) (natPorts 2:V) (natPorts 3:V)' in s
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'exact_fixed_compact_tuple_source_definitions_checked':True,'once_shifted_fourth_port':True,
 'child_port_and_witness_slot_names_checked':True,'source_interfaces_and_conditional_call_observed':True,
 'bounded_lexical_proof_escape_scan_clear':True,'lean_executed':False,
 'elaboration_or_provider_validation':False},sort_keys=True,indent=2))
