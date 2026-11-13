#!/usr/bin/env python3
"""Pin and compare statement-level source and historical receipts; no Lean."""
from pathlib import Path
import hashlib,json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
pins={
'research/ordinary14-natural-forced-w79-ipra-draft/Natural79Endpoint.lean':'9b527ff7a8b6e166869f2565b83a8c37956680d538c49557de9c82ea1a6041e6',
'Lean/DiophantineConsistency/FoundationZFCConsistencyNat.lean':'c9e90e5861848ece065a410ad2b0012617e481b9d4fbfccd37436b2ebf40b613',
'Lean/DiophantineConsistency/FoundationHAConsistencyNormalization.lean':'1a69a875738db6ebbd7c5e466022d0d169ee747e50184fc838077d42f0ad8e09',
'Lean/DiophantineConsistency/IPRANativeFormula.lean':'dcc5601c6d138dcf999efbf3d84f75dcef29aef4c0fd471c71c1216c0214abef',
'Lean/DiophantineConsistency/IPRAFoundationZFCMappedNegation.lean':'9186acc49f486e0fbed0aa52ada450e253f028e64b18c5ee637e926edd4ad95c',
'Lean/DiophantineConsistency/IPRABoundedRhoZFC.lean':'11105cf224931655e8fe2b68b0d529363a4fb36bbc902c491a93bb3ca203012c',
'Lean/DiophantineConsistency/IPRAStandardTheory.lean':'c2800acbf0077a1c4d95707a6118e89d6d5cf6a3f9193139d5b2098411b4f120',
'Lean/DiophantineConsistency/IPRAStandardCurrentEndpoint.lean':'756d87adb5a9cb8e192156b043714f55afe3836d7833ef87d5113cba8d772c38',
'research/current14-quoted-translated-endpoint-check/src/DiophantineConsistency/Current14QuotedTranslatedEndpoint.lean':'90a459830c2b41085faa6d932ce2d83e00b7479e7e11a113665f53f1c80d3965',
'research/current14-seed-readable-prefix-staged-check/src/DiophantineConsistency/Current14QuotedPrefixEndpoint.lean':'0c2f555a11bde2e9580fe3b956f0d7777563526d9b1265caecc1e2a3614e00d2',
'research/current14-quoted-translated-endpoint-check/attempt01/outer-result.json':'541e62eabc834b518b068ed5f464349d7cf82b3e7b8eed6b05d813d83e09df0d',
'research/current14-quoted-translated-endpoint-check/attempt01/Current14QuotedTranslatedEndpoint-compile.txt':'4f3e8dbde2a08381dec7174fa7825a333715bd7dde8fb58d622f7b43d16054c3',
'reviews/current14-quoted-translated-endpoint-terminal-independent/result.json':'0c7e369ef1210e398d857dac5851836f93c9819db69874a4fba2ccd6efe5d957'}
s={}
for path,h in pins.items():
 raw=(D/path).read_bytes();assert hashlib.sha256(raw).hexdigest()==h,path;s[Path(path).name]=raw.decode()
def has(n,*xs):
 for x in xs:assert x in s[n],(n,x)
has('Natural79Endpoint.lean','def expression : Expr (Fin 14) := (P79NaturalForcedW.graph CompactSymbolicModelIff.p).output',
 'theorem standard_equivalence : IPRAStandardTheory.standardTheory ⊢',
 'IPRAExpressionNative.nativeNoZero expression 🡘 ∼mappedNativeRefutation embedding')
has('FoundationZFCConsistencyNat.lean','noncomputable def sourceSentence : ArithmeticSentence :=',
 '(LO.FirstOrder.SetTheory.ZermeloFraenkelChoice : LO.FirstOrder.SetTheory).consistent',
 'theorem source_nat_iff_no_refutation :')
has('FoundationHAConsistencyNormalization.lean','noncomputable def rho : ArithmeticSentence :=',
 'provabilityPred (LO.FirstOrder.SetTheory.ZermeloFraenkelChoice : LO.FirstOrder.SetTheory)',
 '(⊥ : SetTheorySentence)','theorem source_eq_neg_rho : sourceSentence = ∼rho := rfl')
has('IPRANativeFormula.lean','| _, .nrel r v => ∼(.rel r v)','| _, .or p q => native p ⋎ native q',
 '| _, .exs p => ∃⁰ native p')
has('IPRAFoundationZFCMappedNegation.lean','native (Semiformula.lMap f rho)',
 '(hbackward : T ⊢! (Semiformula.lMap f rho)ᴺ 🡒 ∼∼mappedNativeRefutation f)',
 'T ⊢! (Semiformula.lMap f sourceSentence)ᴺ 🡘 ∼mappedNativeRefutation f')
has('IPRABoundedRhoZFC.lean','def zfcEquiv : nativeTheory ⊢!',
 '(Semiformula.lMap embedding sourceSentence)ᴺ 🡘 ∼mappedNativeRefutation embedding',
 'fromOpenFamily matrixOpen')
has('IPRAStandardTheory.lean','theorem provable_iff (φ : Sentenceᵢ language) : standardTheory ⊢ φ ↔ nativeTheory ⊢ φ')
has('IPRAStandardCurrentEndpoint.lean','exact ⟨Entailment.K_intro',
 '(Entailment.C_trans (Entailment.K_left h) (Entailment.K_right z))',
 '(Entailment.C_trans (Entailment.K_left z) (Entailment.K_right h))⟩')
has('Current14QuotedTranslatedEndpoint.lean','theorem quoted_translated_endpoint : ∃ φ, quoteSentence = some φ ∧',
 'standardTheory ⊢ φ 🡘 (Semiformula.lMap embedding sourceSentence)ᴺ')
has('Current14QuotedPrefixEndpoint.lean','theorem quoted_endpoint : ∃ φ, quoteSentence = some φ ∧',
 'standardTheory ⊢ φ 🡘 ∼mappedNativeRefutation embedding')
outer=json.loads(s['outer-result.json']);terminal=json.loads(s['result.json'])
assert outer['outer_exit_code']==0 and outer['outer_session']==48120
state_raw=(D/'research/current14-quoted-translated-endpoint-check/attempt01/state.json').read_bytes()
assert hashlib.sha256(state_raw).hexdigest()==outer['state_sha256']
state=json.loads(state_raw);assert state['status']=='PASS' and len(state['rows'])==1
assert state['rows'][0]['source_sha256']==pins['research/current14-quoted-translated-endpoint-check/src/DiophantineConsistency/Current14QuotedTranslatedEndpoint.lean']
assert outer['logs']['Current14QuotedTranslatedEndpoint-compile.txt']==pins['research/current14-quoted-translated-endpoint-check/attempt01/Current14QuotedTranslatedEndpoint-compile.txt']
assert terminal['status']=='PASS_TERMINAL_AUDIT' and terminal['outer_session']==48120
log=s['Current14QuotedTranslatedEndpoint-compile.txt'];assert 'quoted_translated_endpoint' in log
for a in ('propext','Classical.choice','Quot.sound'):assert a in log
assert 'sorryAx' not in log
print(json.dumps({'scope':'pinned source statements and retained historical receipt, no Lean execution or current provider closure',
 'pinned_files':len(pins),'draft79_target':'N79 iff not native mapped rho',
 'historical_quote_target':'quote iff GG(mapped sourceSentence)',
 'existing_comparison_orientation':'GG(mapped sourceSentence) iff not native mapped rho',
 'historical_outer_session':48120,'historical_terminal_audit':'PASS_TERMINAL_AUDIT',
 'new79_kernel_check':False},sort_keys=True,indent=2))
