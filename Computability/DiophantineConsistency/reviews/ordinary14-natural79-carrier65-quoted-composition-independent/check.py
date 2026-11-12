#!/usr/bin/env python3
"""Independent bounded source review, no Lean or staging."""
from pathlib import Path
import hashlib,json,re,sys
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode):raise SystemExit('Use python3 -I -S -B')
D=Path(__file__).resolve().parents[2]
F=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/lib/FormalizedFormalLogic-Foundation/Foundation')
inputs={
'draft':(D/'research/ordinary14-natural79-carrier65-quoted-composition-draft/Natural79QuotedCarrier65Comparison.lean.src','af6ad674259c14540045971798fe80f47d08975fdf59c17adae4989a6c015056'),
'author_receipt':(D/'research/ordinary14-natural79-carrier65-quoted-composition-draft/result.json','c9f142ee78d1a4e002d97c4e1cc26bb5a225a27c19da6c447b2604e172520eea'),
'79_endpoint':(D/'research/ordinary14-natural79-corrected-reflection-overlay/source/Natural79Endpoint.lean.src','9b527ff7a8b6e166869f2565b83a8c37956680d538c49557de9c82ea1a6041e6'),
'quote_endpoint':(D/'research/current14-seed-readable-prefix-staged-check/src/DiophantineConsistency/Current14QuotedPrefixEndpoint.lean','0c2f555a11bde2e9580fe3b956f0d7777563526d9b1265caecc1e2a3614e00d2'),
'quote_translated_endpoint':(D/'research/current14-quoted-translated-endpoint-check/src/DiophantineConsistency/Current14QuotedTranslatedEndpoint.lean','90a459830c2b41085faa6d932ce2d83e00b7479e7e11a113665f53f1c80d3965'),
'standard_theory':(D/'Lean/DiophantineConsistency/IPRAStandardTheory.lean','c2800acbf0077a1c4d95707a6118e89d6d5cf6a3f9193139d5b2098411b4f120'),
'bridge':(D/'Lean/DiophantineConsistency/IPRABoundedRhoZFC.lean','11105cf224931655e8fe2b68b0d529363a4fb36bbc902c491a93bb3ca203012c'),
'erasure':(D/'Lean/DiophantineConsistency/IPRAOrderErasure.lean','d14c6b50d1ee5c09bc6f3673d3bd9b3715ca2d9aba21c403a154fb6ff5da21d6'),
'reference':(D/'Lean/DiophantineConsistency/IPRAReferenceInductionConversion.lean','e94ba7c5e4fe4ca809c55be43870331f0a4a7506eae372aa97ce74c789cb6cc9'),
'logic_iff':(F/'Logic/LogicSymbol.lean','eb52f07ae7e3f7db9e32456cafc51824d52b008d76917a9d714473f5e81c271a'),
'logic_rules':(F/'Propositional/Entailment/Minimal/Basic.lean','16d1111c34adcce61fdd4d64df3b85120903e4b795119b224b6039cc73115223'),
'quote_terminal_review':(D/'reviews/current14-seed-readable-prefix-staged-terminal-independent/README.md','cf3e4e04bc0ef239060d39b787760552ae47d9a6f74cdebe68bfada66fd23d2f'),
'quote_translated_terminal_review':(D/'reviews/current14-quoted-translated-endpoint-terminal-independent/result.json','0c7e369ef1210e398d857dac5851836f93c9819db69874a4fba2ccd6efe5d957')}
texts={}
for n,(p,h) in inputs.items():
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h,n;texts[n]=b.decode()
def flat(x):return re.sub(r'\s+',' ',x).strip()
def theorem(text,name):
 m=re.search(r'^theorem '+re.escape(name)+r'\b',text,re.M);assert m,name
 end=re.search(r'^theorem |^end |^#print',text[m.end():],re.M)
 return flat(text[m.start():m.end()+end.start() if end else len(text)])
q=flat(texts['quote_endpoint']);t=flat(texts['quote_translated_endpoint']);a=flat(texts['79_endpoint']);d=texts['draft']
assert 'def quoteSentence : Option (Sentenceᵢ language)' in q
assert 'let e ← quotedExpr linePorts let e := positiveShift e' in q
assert 'theorem quoteSentence_eq : quoteSentence = some displayedNoZero' in q
assert 'theorem quoted_endpoint : ∃ φ, quoteSentence = some φ ∧ (standardTheory ⊢ φ 🡘 ∼mappedNativeRefutation embedding)' in q
assert 'exact ⟨displayedNoZero, quoteSentence_eq, displayed_endpoint⟩' in q
assert 'theorem quoted_translated_endpoint : ∃ φ, quoteSentence = some φ ∧ (standardTheory ⊢ φ 🡘 (Semiformula.lMap embedding sourceSentence)ᴺ)' in t
assert 'refine ⟨displayedNoZero, quoteSentence_eq, ?_⟩' in t
assert 'IPRAExpressionNative.nativeNoZero expression 🡘 ∼mappedNativeRefutation embedding' in a
assert 'theorem provable_iff (φ : Sentenceᵢ language) : standardTheory ⊢ φ ↔ nativeTheory ⊢ φ' in flat(texts['standard_theory'])
assert '(Semiformula.lMap embedding sourceSentence)ᴺ 🡘 ∼mappedNativeRefutation embedding' in flat(texts['bridge'])
common=theorem(d,'standard_common_target');chain=theorem(d,'standard_compose')
assert '(hA : standardTheory ⊢ A 🡘 R)' in common and '(hB : standardTheory ⊢ B 🡘 R)' in common
assert '(Entailment.C_trans (Entailment.K_left a) (Entailment.K_right b)) (Entailment.C_trans (Entailment.K_left b) (Entailment.K_right a))' in common
assert '(hA : standardTheory ⊢ A 🡘 R)' in chain and '(hC : standardTheory ⊢ C 🡘 R)' in chain and '(hB : standardTheory ⊢ B 🡘 C)' in chain
assert '(Entailment.C_trans (Entailment.C_trans (Entailment.K_left a) (Entailment.K_right c)) (Entailment.K_right b)) (Entailment.C_trans (Entailment.C_trans (Entailment.K_left b) (Entailment.K_left c)) (Entailment.K_right a))' in chain
p=theorem(d,'quoted_standard_equivalence');v=theorem(d,'quoted_standard_equivalence_via_translated');r=theorem(d,'quoted_reference_equivalence')
assert '⟨φ, hquote, hφ⟩ := Current14QuotedPrefix.quoted_endpoint' in p and 'standard_common_target Natural79EndpointDraft.standard_equivalence hφ' in p
assert '⟨φ, hquote, hφ⟩ := Current14QuotedPrefix.quoted_translated_endpoint' in v and 'standard_compose Natural79EndpointDraft.standard_equivalence hzfc hφ' in v
assert '(IPRAStandardTheory.provable_iff _).2 ⟨IPRABoundedRhoZFC.zfcEquiv⟩' in v
assert '⟨φ, hquote, h⟩ := quoted_standard_equivalence' in r and '(IPRAStandardTheory.provable_iff _).1 h' in r and 'IPRAReferenceInductionConversion.nativeToReference hn' in r
assert 'theorem nativeToReference {σ : Sentenceᵢ PRALanguage.language} (h : IPRANativeTheory.nativeTheory ⊢ σ) : referenceTheory ⊢ erase σ' in flat(texts['reference'])
assert '| _, .and φ ψ => .and (erase φ) (erase ψ)' in texts['erasure'] and '| _, .imp φ ψ => .imp (erase φ) (erase ψ)' in texts['erasure']
assert '@[match_pattern] def iff (a b : α) := (a 🡒 b) ⋏ (b 🡒 a)' in texts['logic_iff']
assert 'def C_trans [HasAxiomImplyK' in texts['logic_rules'] and 'def K_left [ModusPonens' in texts['logic_rules'] and 'def K_right [ModusPonens' in texts['logic_rules']
assert len(re.findall(r'^#print axioms ',d,re.M))==5
assert not re.search(r'^\s*(?:axiom|opaque)\b|\b(?:sorry|admit)\b',d,re.M)
print(json.dumps({'scope':'independent source-level text/direction checks only; no Lean or provider verification',
 'inputs':{n:{'path':str(p),'sha256':h} for n,(p,h) in sorted(inputs.items())},
 'same_historical_witness_declared':'displayedNoZero','common_target_route':['A → R → B','B → R → A'],
 'translated_route':['A → R → C → B','B → C → R → A'],
 'reference_route':'same φ and quote equality; standard-to-native transfer followed by erasure of the whole biconditional',
 'axiom_reports_unexecuted':5},sort_keys=True,indent=2,ensure_ascii=False))
