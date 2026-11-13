from pathlib import Path
from hashlib import sha256
import json,sys,subprocess
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path;p=P('research/ordinary13-unscale84-compact-chain-draft')
files=[p/'Unscale84CompactChain.lean.src',p/'README.md',p/'check.py',p/'pins.json',p/'receipt.json',P('research/ordinary13-unscale84-conditional-endpoint-draft/Unscale84Endpoint.lean.src'),P('research/ordinary13-unscale84-large-k-model-draft/Unscale84LargeK.lean.src'),P('research/ordinary13-positive87-to88-bounds-model-draft/Positive87To88Bounds.lean.src'),P('research/ordinary13-positive87-to88-aux-model-draft/Positive87To88Aux.lean.src'),P('research/ordinary13-freej88-four-square-lean-draft/P88FourSquareModel.lean'),P('Lean/DiophantineConsistency/Compact44/CompactSymbolicModelIff.lean'),P('Lean/DiophantineConsistency/Compact44/CompactSymbolicPorts.lean'),P('Lean/DiophantineConsistency/Compact44/CompactSymbolicKernel.lean'),P('Lean/DiophantineConsistency/Compact44/CompactSymbolicKernelOpaque.lean'),P('Lean/DiophantineConsistency/Compact44/CompactFixedBeta.lean'),P('research/ordinary13-residue90-norm-model-draft/Residue90CompactPortBounds.lean.src'),P('research/ordinary13-unscale84-reverse-graph-model-draft/Unscale84ReverseGraph.lean.src'),P('research/ordinary13-positive87-first-norm-binding-draft/Positive87FirstNormBinding.lean.src'),P('Lean/DiophantineConsistency/Compact44/IPRAOrdinary12.lean'),P('Lean/DiophantineConsistency/Compact44/IPRAOrdinary12Chain.lean'),P('research/ordinary13-positive84-to87-unscale-model-draft/PositiveUnscale84Graph.lean.src'),P('research/ordinary13-positive83-to84-model-draft/PositiveUnscaled84Graph.lean.src'),P('research/ordinary13-qcube-unscale84/candidate.json')]
s=[f.read_text() for f in files]
for n in ['def fixedK : ℕ := paramKernel rho','theorem compact_beta','CompactFixedBeta.bounds (V:=V) (1:V)',
 'theorem positiveBridge87','Positive87To88BoundsDraft.bounds_cut (ports K) (compact_beta K)',
 'Positive87To88AuxDraft.positive_zero_iff','theorem fixed_ports','portsInt (ports fixedK)=CompactSymbolicModelIff.p := by rfl',
 'theorem fixed88Bridge','P88FourSquareModel.positiveBridge','theorem native84',
 'Unscale84EndpointDraft.native84 fixedK (positiveBridge87 fixedK fixed88Bridge)']:
 assert n in s[0],n
for n in ['def expression84 (K : ℕ)','def expression87 (K : ℕ)','PositiveUnscale84GraphDraft.graph','PositiveUnscale87GraphDraft.graph',
 'theorem positiveBridge84','PositiveModelBridge (expression87 K)','theorem native84','∼mappedNativeRefutation embedding']:
 assert n in s[5],n
assert 'theorem compact_positive_zero_iff (K : ℕ)' in s[6] and 'theorem bounds_cut (p : Fin 4 → ℕ)' in s[7]
assert 'theorem positive_zero_iff (p : Fin 4 → ℤ)' in s[8] and 'theorem positiveBridge : PositiveModelBridge expression' in s[9]
assert 'def expression : Expr (Fin 13) := (P88FourSquare.graph CompactSymbolicModelIff.p).output' in s[9]
assert 'def p : Fin 4 → ℤ := fun j => (ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat j:ℤ)' in s[10]
assert 'def ports (β K L H : ℕ) : Fin 4 → ℕ := ![β,K,L,β+H]' in s[11]
assert 'def rho : ℕ := 2^67' in s[12] and 'def paramKernel (r : ℕ) : ℕ' in s[13]
assert 'theorem bounds (J : V) (hJ : 0<J)' in s[14]
assert 'CompactSymbolicPorts.ports CompactFixedBeta.betaNat K' in s[15]
assert 'def portsInt (p : Fin 4 → ℕ) : Fin 4 → ℤ := fun j => (p j : ℤ)' in s[16]
assert 'def intPorts (p : Fin 4 → ℕ) : Fin 4 → ℤ := fun i => (p i : ℤ)' in s[17]
assert 'def PositiveModelBridge' in s[18] and 'theorem native_of_positive' in s[19]
# Bound separate graph names: compare all 84 literal lines and terminal field
# selections; this lexical comparison is not an elaboration or equality proof.
g=json.loads(s[22]);assert len(g['source'])==84
for src in (s[20],s[21]):
 for i,n in enumerate(g['witnesses']):assert f'  let {n} : Expr (Fin 13) := .var {i}\n' in src
 for i,n in enumerate(g['fixed_numerals']):assert f'  let {n} : Expr (Fin 13) := .constant (p {i})\n' in src
 for n,op,l,r in g['source']:assert f'  let {n} := {l} {op} {r}\n' in src,n
assert '⟨A0,A1,Fa,g72,Z,Bt,ell,k,out⟩' in s[20]
assert '⟨A0,A1,Fa,g72,out⟩' in s[21]
res=subprocess.run([sys.executable,'-I','-S','-B',str(files[2])],check=True,stdout=subprocess.PIPE);assert res.stdout==files[4].read_bytes()
print(json.dumps({'sha256':{str(f):sha256(f.read_bytes()).hexdigest() for f in files},'fixed_tuple_source_definitions_checked':True,'port_cast_wrappers_source_definitional_shape_checked':True,'endpoint_chain_statements_checked':True,'distinct_84_graph_names_row_comparison':True,'author_receipt_reproduced':True,'lean_executed':False,'scope':'Bounded source/tuple audit; definitional equality and all proofs/provider/axiom/physical bindings remain unchecked.'},sort_keys=True,indent=2))
