#!/usr/bin/env python3
"""Check exact pinned source statements and draft shape, not Lean elaboration."""
import hashlib,json,re,sys
from pathlib import Path
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode):
    raise SystemExit('Use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1]
sha=lambda b:hashlib.sha256(b).hexdigest()
files={
 'natural79_endpoint':('research/ordinary14-natural-forced-w79-ipra-draft/Natural79Endpoint.lean','9b527ff7a8b6e166869f2565b83a8c37956680d538c49557de9c82ea1a6041e6'),
 'carrier65_bfs_endpoint':('Lean/DiophantineConsistency/BFS943/IPRACarrier65BFS943.lean','6ef47f75856066859044f38a91ad066e294a1679fcdd342fa35eb66f2c50eae9'),
 'native_no_zero':('Lean/DiophantineConsistency/IPRAExpressionNative.lean','f2ecaf302d2e41f7d85a4c5c078f7c9a47f69b8ae4ee40d9b320b4817636b8e8'),
 'positive_shift_source':('Lean/DiophantineConsistency/AdaptiveEquationSyntax2011.lean','f1d7f3835bc2a183b0767497a45ffdd0a54e6aab086b259ccce3de4af9392cb6'),
 'zfc_translation':('Lean/DiophantineConsistency/IPRABoundedRhoZFC.lean','11105cf224931655e8fe2b68b0d529363a4fb36bbc902c491a93bb3ca203012c'),
 'reference_translation':('Lean/DiophantineConsistency/IPRAReferenceInductionConversion.lean','e94ba7c5e4fe4ca809c55be43870331f0a4a7506eae372aa97ce74c789cb6cc9'),
 'draft':('research/ordinary14-natural79-carrier65-bfs-direct-comparison-draft/Natural79Carrier65BFSComparison.lean','48d46d534b6d0834546e5e169af515d942ad1e43fbff2f6db40ab29b2a16c5e8')}
data={}
for k,(p,h) in files.items():
 b=(D/p).read_bytes();assert sha(b)==h,(k,sha(b));data[k]=b.decode()
flat=lambda s:re.sub(r'\s+',' ',s)
def declaration(s,n):
 m=re.search(r'\b(?:theorem|def) '+re.escape(n)+r'\s*:',s);assert m,n
 body=s[m.end():];stop=body.index(':=');return flat(body[:stop]).strip()
a=declaration(data['natural79_endpoint'],'native_equivalence')
b=declaration(data['carrier65_bfs_endpoint'],'native_equivalence')
z=declaration(data['zfc_translation'],'zfcEquiv')
assert a=='nativeTheory ⊢ IPRAExpressionNative.nativeNoZero expression 🡘 ∼mappedNativeRefutation embedding'
assert b=='nativeTheory ⊢ IPRAExpressionNative.nativeNoZero (positiveShift expression) 🡘 ∼mappedNativeRefutation embedding'
assert z=='nativeTheory ⊢! (Semiformula.lMap embedding sourceSentence)ᴺ 🡘 ∼mappedNativeRefutation embedding'
assert 'namespace DiophantineConsistency.AdaptiveEquationSyntax2011' in data['positive_shift_source']
assert 'def positiveShift {σ : Type*} (e : Expr σ) : Expr σ :=' in data['positive_shift_source']
s=data['draft']
assert re.search(r'^open AdaptiveEquationSyntax2011\b', s, re.M)
for token in ['(h79 : nativeTheory ⊢','(h65 : nativeTheory ⊢','Natural79EndpointDraft.native_equivalence',
 'IPRACarrier65BFS943.native_equivalence','IPRABoundedRhoZFC.zfcEquiv',
 'IPRAReferenceInductionConversion.nativeToReference','positiveShift IPRACarrier65BFS943.expression']:
 assert token in s,token
assert len(re.findall(r'^#print axioms ',s,re.M))==7
assert not re.search(r'^\s*(?:axiom|opaque)\b|\b(?:sorry|admit)\b',s,re.M)
print(json.dumps({'scope':'pinned source-statement comparison and inert draft shape only; no Lean, proof or axiom check',
 'sources':{k:{'path':p,'sha256':h} for k,(p,h) in sorted(files.items())},
 'natural79_native_declaration':a,'carrier65_bfs_native_declaration':b,
 'foundation_translation_declaration':z,'shared_target':'∼mappedNativeRefutation embedding',
 'carrier65_positive_shift_explicit':True,'draft_axiom_reports_unexecuted':7},sort_keys=True,indent=2,ensure_ascii=False))
