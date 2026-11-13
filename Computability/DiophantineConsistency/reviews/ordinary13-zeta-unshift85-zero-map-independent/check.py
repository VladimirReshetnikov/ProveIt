from pathlib import Path
import hashlib,json,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-zeta-unshift85-zero-map-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert hashlib.sha256(Path(p).read_bytes()).hexdigest()==h,p
P=Path('research/ordinary13-zeta-unshift85-zero-map-draft')
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(P/'check.py')])==(P/'receipt.json').read_bytes()
parent=json.loads(Path('research/ordinary13-eta-zero-graph-adapter-audit/prototype.json').read_text());probe=json.loads(Path('research/ordinary13-eta85-zeta-zero-boundary-audit/probe.json').read_text())
assert len(parent['source'])==len(probe['source'])==85 and parent['output']==probe['output']=='out'
assert parent['witnesses']==probe['witnesses'] and parent['fixed_numerals']==probe['fixed_numerals'] and parent['witnesses'][10]=='n_zeta'
# Derive all probe rows independently, with only the two k/r0 edits.
expected=[]
for n,op,x,y in parent['source']:
 if n=='k':
  assert [op,x,y]==['+','kbase',1];continue
 if n=='r0':
  assert [op,x,y]==['-','kbase','R'];expected.extend([['r0base','-','kbase','R'],['r0','-','r0base',1]]);continue
 assert 'kbase' not in (x,y)
 expected.append([n,op,'kbase' if x=='k' else x,'kbase' if y=='k' else y])
assert expected==probe['source']
for g,f,k in [(parent,'research/ordinary13-eta-natural-unit-norm-bridge-draft/EtaNaturalUnitGraph.lean.src','k'),(probe,'research/ordinary13-eta-zeta-natural-unit-norm-draft/EtaZetaNaturalUnitGraph.lean.src','kbase')]:
 s=Path(f).read_text()
 for i,n in enumerate(g['witnesses']):assert f'  let {n} : Expr (Fin 13) := .var {i}\n' in s
 for i,n in enumerate(g['fixed_numerals']):assert f'  let {n} : Expr (Fin 13) := .constant (p {i})\n' in s
 for n,op,x,y in g['source']:assert f'  let {n} := {x} {op} {y}\n' in s
 assert f'⟨A0, A1, Fa, Fs, out, g72, qm, Z, X, s, {k}, U, a, c, Dstar, n_y, V, n_f, I, ell, Delta⟩' in s
src=(P/'ZetaUnshift85Transport.lean.src').read_text()
for x in ['if i=10 then v i+1 else v i','if i=10 then v i-1 else v i','raiseZeta (lowerZeta v)=v','(zero_iff _ v).mp hz','(zero_iff _ (lowerZeta v)).mpr','have hp := hforce v hz','def ForcedZeta (K : ℕ)','(hparent : PolynomialBridge (EtaNaturalUnitGraphDraft.graph','compact_sameNoZero K hforce','ZetaZeroCompactGraphDraft.zeta_positive K v hz','(polynomialBridge K (proposed_forcing K) hparent)']:
 assert x in src,x
forced=Path('research/ordinary13-zeta-zero-compact-parity-draft/ZetaZeroCompactGraph.lean.src').read_text()
assert 'theorem zeta_positive (K : ℕ) (v : Fin 13 → V)' in forced
assert '0<v 10 := by' in forced
h=Path('Lean/DiophantineConsistency/HAExpressionNoZeroEquiv.lean').read_text()
assert '(h : SameNoZero e f) (hf : PolynomialBridge f) : PolynomialBridge e' in h
native=Path('Lean/DiophantineConsistency/IPRAExpressionNative.lean').read_text()
assert 'theorem equivalence_of_bridge {n : ℕ} (e : Expr (Fin n)) (hp : HAExpressionAssembly.PolynomialBridge e)' in native
print(json.dumps({'both_85_literal_graphs_all_rows_checked':True,'raise_coordinate_10_row_identity_and_r0_checked':True,'zero_and_no_zero_directions_checked':True,'forcing_and_parent_bridge_premises_checked':True,'same_compact_tuple_checked':True,'author_receipt_reproduced':True,'lean_executed':False,'scope':'Unelaborated source-only zero map; forcing proof and parent bridge remain open.'},sort_keys=True,indent=2))
