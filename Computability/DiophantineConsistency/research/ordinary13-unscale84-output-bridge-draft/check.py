from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path;d=P('research/ordinary13-unscale84-output-bridge-draft')
pins=json.loads((d/'pins.json').read_text())
for p,h in pins.items():assert sha256(P(p).read_bytes()).hexdigest()==h,p
p84=P('research/ordinary13-positive84-to87-unscale-model-draft/PositiveUnscale84Graph.lean.src')
p83=P('research/ordinary13-positive83-to84-model-draft/PositiveUnscaled84Graph.lean.src')
g=json.loads(P('research/ordinary13-qcube-unscale84/candidate.json').read_text());assert len(g['source'])==84
texts=[p84.read_text(),p83.read_text()]
for text in texts:
 for i,n in enumerate(g['witnesses']):assert f'  let {n} : Expr (Fin 13) := .var {i}\n' in text,(n,i)
 for i,n in enumerate(g['fixed_numerals']):assert f'  let {n} : Expr (Fin 13) := .constant (p {i})\n' in text,(n,i)
 for n,op,l,r in g['source']:assert f'  let {n} := {l} {op} {r}\n' in text,n
assert '⟨A0,A1,Fa,g72,Z,Bt,ell,k,out⟩' in texts[0]
assert '⟨A0,A1,Fa,g72,out⟩' in texts[1]
s=(d/'Unscale84OutputBridge.lean.src').read_text()
for token in ['theorem output_eq (p : Fin 4 → ℤ)', '(PositiveUnscale84GraphDraft.graph p).output =',
 '(PositiveUnscaled84GraphDraft.graph p).output := by\n  rfl',
 'theorem bridge84','PositiveModelBridge (Unscale84EndpointDraft.expression87 K)',
 'IPRAOrdinary12.bridge_of_positive','Unscale84EndpointDraft.positiveBridge84 K h87','rw [output_eq] at h',
 'theorem bridge83','Positive83To84BridgeDraft.bridge83 K hg hd (bridge84 K h87)',
 'theorem native85','Positive83To84BridgeDraft.native85 K hc hg hd (bridge84 K h87)',
 'theorem fixed_native85','Unscale84CompactChainDraft.positiveBridge87','Unscale84CompactChainDraft.fixed88Bridge']:
 assert token in s,token
assert 'sorry' not in s and '\naxiom ' not in s
end=P('research/ordinary13-unscale84-conditional-endpoint-draft/Unscale84Endpoint.lean.src').read_text()
bridge=P('research/ordinary13-positive83-to84-model-draft/Positive83To84Bridge.lean.src').read_text()
adapter=P('Lean/DiophantineConsistency/Compact44/IPRAOrdinary12.lean').read_text()
assert 'PositiveModelBridge (expression87 K)' in end and 'PositiveModelBridge (expression84 K)' in end
assert 'theorem bridge_of_positive' in adapter and 'PolynomialBridge (positiveShift e)' in adapter
assert 'theorem bridge83 (K : ℕ) (hg : GammaCut K) (hd : DivCut K)' in bridge
assert 'theorem native85 (K : ℕ) (hc : Positive81To83TransportDraft.CrossRootCut K)' in bridge
print(json.dumps({'source_pins':pins,'both_exact_84_input_port_and_row_lists_match':True,'output_projection_names_checked':True,'conditional_bridge_source_signatures_checked':True,'lean_executed':False,'scope':'Unelaborated source proposal; no definitional equality proof, cut/provider validation or internal endpoint is established.'},sort_keys=True,indent=2))
