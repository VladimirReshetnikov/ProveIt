from pathlib import Path
from hashlib import sha256
import json,sys,re,subprocess
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-independent-k-fixed-compact-port-client-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
p=Path('research/ordinary13-independent-k-fixed-compact-port-client-draft')
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')])==(p/'receipt.json').read_bytes()
s=(p/'IndependentKFixedCompactPorts.lean.src').read_text();norm=lambda t:re.sub(r'\s+',' ',t)
for token in ['def natPorts : Fin 4 → ℕ := C44Short15Facts.c44','def intPorts : Fin 4 → ℤ := fun j => (natPorts j : ℤ)','theorem fixed_ports_eq_retained : intPorts=CompactSymbolicModelIff.p := by rfl','P72Root.cast_port (V:=V) natPorts j']:
 assert token in s
c=Path('Lean/DiophantineConsistency/Compact44/C44Short15Facts.lean').read_text()
assert 'abbrev c44 : Fin 4 → ℕ := ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat' in c
m=Path('Lean/DiophantineConsistency/Compact44/CompactSymbolicModelIff.lean').read_text()
assert 'def p : Fin 4 → ℤ := fun j => (ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat j:ℤ)' in m
ports=Path('Lean/DiophantineConsistency/Compact44/CompactSymbolicPorts.lean').read_text()
assert 'def ports (β K L H : ℕ) : Fin 4 → ℕ := ![β,K,L,β+H]' in ports
root=Path('Lean/DiophantineConsistency/Compact44/P72Root.lean').read_text()
assert '(((fun j => (p j : ℤ)) j : ℤ) : DiffRing V) = ι (p j : V)' in root
for token in ['theorem port_bounds (B K L H : ℕ)','(hL : L = lowNat) (hH : H = highNat)','theorem K_pos (B K L H : ℕ) (hK : K = paramKernel rho)']:
 assert token in c
assert 'theorem beta_identity : (betaNat:V)+1=Exp.exp ((67:V)*8807)' in Path('Lean/DiophantineConsistency/Compact44/CompactFixedBeta.lean').read_text()
j=Path('research/ordinary13-independent-k-j-positive-model-draft/IndependentKJPositive.lean.src').read_text()
assert '(p : Fin 4 → ℕ) (v : Fin 13 → V)' in j and '(hz : InternalZero (graph (fun j => (p j:ℤ))).output v)' in j
r=Path('research/ordinary13-independent-k-first-rank-discrete-repair/IndependentKFirstRankDiscrete.lean.src').read_text()
assert '(q beta J MC MF F alpha d r R X Y s eta gamma : V) (z : DiffRing V)' in r
assert norm('''q (natPorts 0:V) (v 0) (natPorts 2:V) (natPorts 3:V)
    (v 1+1) (v 2+1) (X+(natPorts 1:V)) (v 8) R X Y (v 7+1)
    (v 9) (v 12) z hq hb hJ hMC hMF hF ha hd hfirst hrank hqpos hs hY hshape hnorm''') in norm(s)
g=json.loads(Path('research/ordinary13-eta-zeta84-independent-k-candidate/candidate.json').read_text())
assert g['fixed_numerals']==['beta','K0','MC','MF'] and g['witnesses']==['n_J','n_F','n_alpha','n_f','n_i','n_T','n_w','n_s','n_r','n_eta','n_k','n_y','n_gamma']
# These are hypotheses of the fact-level client, not derived from the graph.
for x in ['(hJ : 0<v 0)','(hq : q=(natPorts 0:V)*v 0+1)','(hfirst : let b','(hrank :','(hY :','(hshape :','(hnorm :']:
 assert x in s
print(json.dumps({'author_receipt_reproduced':True,'fixed_natural_and_integer_tuple_sources_match':True,'four_port_cast_interface_checked':True,'positive_kernel_and_mask_bound_argument_interfaces_checked':True,'exact_child_witness_and_port_order_checked':True,'conditional_helper_full_argument_order_checked':True,'lean_executed':False,'source_elaboration_and_provider_validation':False},sort_keys=True,indent=2))
