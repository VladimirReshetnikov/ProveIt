#!/usr/bin/env python3
"""Bounded source pins and statement checks; never runs Lean or stages."""
from pathlib import Path
import hashlib,json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
items={
 'natural79_endpoint':('research/ordinary14-natural79-corrected-reflection-overlay/source/Natural79Endpoint.lean.src','9b527ff7a8b6e166869f2565b83a8c37956680d538c49557de9c82ea1a6041e6'),
 'historical_quote_prefix':('research/current14-seed-readable-prefix-staged-check/src/DiophantineConsistency/Current14QuotedPrefixEndpoint.lean','0c2f555a11bde2e9580fe3b956f0d7777563526d9b1265caecc1e2a3614e00d2'),
 'historical_translated_endpoint':('research/current14-quoted-translated-endpoint-check/src/DiophantineConsistency/Current14QuotedTranslatedEndpoint.lean','90a459830c2b41085faa6d932ce2d83e00b7479e7e11a113665f53f1c80d3965'),
 'zfc_translation':('Lean/DiophantineConsistency/IPRABoundedRhoZFC.lean','11105cf224931655e8fe2b68b0d529363a4fb36bbc902c491a93bb3ca203012c'),
 'standard_conversion':('Lean/DiophantineConsistency/IPRAStandardTheory.lean','c2800acbf0077a1c4d95707a6118e89d6d5cf6a3f9193139d5b2098411b4f120'),
 'mapped_refutation':('Lean/DiophantineConsistency/IPRAFoundationZFCMappedNegation.lean','9186acc49f486e0fbed0aa52ada450e253f028e64b18c5ee637e926edd4ad95c'),
 'foundation_sentence':('Lean/DiophantineConsistency/FoundationZFCConsistencyNat.lean','c9e90e5861848ece065a410ad2b0012617e481b9d4fbfccd37436b2ebf40b613'),
 'proposed_client':('research/ordinary14-natural79-carrier65-quoted-composition-draft/Natural79QuotedCarrier65Comparison.lean.src','af6ad674259c14540045971798fe80f47d08975fdf59c17adae4989a6c015056')}
texts={}
for name,(path,h) in items.items():
 raw=(D/path).read_bytes();assert hashlib.sha256(raw).hexdigest()==h,name;texts[name]=raw.decode()
a=texts['natural79_endpoint'];q=texts['historical_quote_prefix'];t=texts['historical_translated_endpoint'];z=texts['zfc_translation'];s=texts['standard_conversion'];f=texts['foundation_sentence'];client=texts['proposed_client']
assert 'theorem standard_equivalence : IPRAStandardTheory.standardTheory ⊢' in a and '∼mappedNativeRefutation embedding' in a
assert 'theorem quoted_endpoint : ∃ φ, quoteSentence = some φ ∧' in q and 'standardTheory ⊢ φ 🡘 ∼mappedNativeRefutation embedding' in q
assert 'theorem quoted_translated_endpoint : ∃ φ, quoteSentence = some φ ∧' in t and '(standardTheory ⊢ φ 🡘 (Semiformula.lMap embedding sourceSentence)ᴺ)' in t
assert '(Semiformula.lMap embedding sourceSentence)ᴺ 🡘 ∼mappedNativeRefutation embedding' in z
assert 'standardTheory ⊢ φ ↔ nativeTheory ⊢ φ' in s
assert 'ZermeloFraenkelChoice : LO.FirstOrder.SetTheory).consistent' in f
for n in ('standard_common_target','quoted_standard_equivalence','quoted_standard_equivalence_via_translated','quoted_reference_equivalence'):assert 'theorem '+n in client
assert 'Current14QuotedPrefix.quoted_endpoint' in client and 'Current14QuotedPrefix.quoted_translated_endpoint' in client
assert '#print axioms' in client
print(json.dumps({'scope':'exact source pins and selected textual statement observations only; no Lean, syntax/typechecking or provider authentication',
 'pinned_inputs':{n:{'path':path,'sha256':h} for n,(path,h) in sorted(items.items())},
 'same_mapped_refutation_text_observed':True,'same_translated_foundation_target_text_observed':True,
 'client_inert_and_unelaborated':True,'axiom_reports_executed':False},indent=2,sort_keys=True))
