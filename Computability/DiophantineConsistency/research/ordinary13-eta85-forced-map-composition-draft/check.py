#!/usr/bin/env python3
"""Pinned type/interface and exact row substitution checks; no Lean."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
pins=json.loads((HERE/'pins.json').read_text())
for path,digest in pins.items():assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==digest,path
base=ROOT/'research'
parent=json.loads((base/'ordinary13-natural-forced-w86/candidate.json').read_text())
child=json.loads((base/'ordinary13-eta-zero-graph-adapter-audit/prototype.json').read_text())
assert parent['witnesses']==child['witnesses'] and parent['witnesses'][9]=='n_eta'
assert parent['fixed_numerals']==child['fixed_numerals']
assert len(parent['source'])==86 and len(child['source'])==85
assert [[('n_eta' if x=='eta' else x) for x in row]
 for row in parent['source'] if row!=['eta','+','n_eta',1]]==child['source']
source=(HERE/'Eta85ForcedMap.lean.src').read_text()
force=(base/'ordinary13-eta-natural-graph-parity-composition-draft/EtaNaturalGraphParity.lean.src').read_text()
transport=(base/'ordinary13-eta-unshift85-zero-map-model-draft/EtaUnshift85Transport.lean.src').read_text()
for s in ['theorem forcedEta (K : ℕ) : EtaUnshift85TransportDraft.ForcedEta K',
 'EtaNaturalGraphParityDraft.eta_positive K v hz',
 'EtaUnshift85TransportDraft.compact_sameNoZero K (forcedEta K)',
 'EtaUnshift85TransportDraft.polynomialBridge K (forcedEta K) hparent',
 'EtaUnshift85TransportDraft.native_equivalence K (forcedEta K) hparent']:
 assert s in source,s
for n in ['polynomialBridge','native_equivalence']:
 head=source.split('theorem '+n,1)[1].split(':=',1)[0]
 assert '(hparent : PolynomialBridge (EtaShifted86GraphDraft.literal' in head
 assert 'ForcedEta' not in head
assert 'theorem eta_positive (K : ℕ)' in force and 'ports K j:ℤ' in force
assert 'def ForcedEta (K : ℕ)' in transport and 'ports K j:ℤ' in transport
assert 'if i=9 then v i+1 else v i' in transport and 'if i=9 then v i-1 else v i' in transport
print(json.dumps({'source_pins':pins,'parent_rows':len(parent['source']),
 'child_rows':len(child['source']),'coordinate9_shift_exact':True,
 'eta_forcing_source_composed':True,'exact_86_parent_bridge_retained':True,
 'lean_executed':False,'scope':'unelaborated source composition; no zero-map build or endpoint proof'},sort_keys=True,indent=2))
