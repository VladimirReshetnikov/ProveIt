#!/usr/bin/env python3
"""Independent source audit of AQ22 quotient residual-map cases."""
from pathlib import Path
import hashlib,json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b.decode()
s=pin('research/adaptive-aq22-quotient110-residual-maps-draft/AQ22Quotient110ResidualMaps.lean.src','94d01b77db20c49538ea1b35a3ba2ab638ead80e36d0490ae1d0175071120531')
pin('research/adaptive-aq22-quotient110-residual-maps-draft/receipt.json','68775dbd0ed9704bfb3a83aa3b414675da30b4c6c2a35e85bf0646d2d3969095')
t=pin('research/adaptive-aq22-quotient110-model-draft/AQ22Quotient110ConditionalTransfer.lean.src','cf38af5ba1e2a24cfbf3d8e5005a3da31b26574e417dfae61ddf4e0cf42a4f31')
w=pin('research/adaptive-aq22-quotient110-model-draft/AQ22Quotient110Witness.lean.src','501bf108b26cbd5e2d6c84e83a0996b8f3fd9f37949c5f0b2ba6940db3987d2a')
r=pin('research/adaptive-aq22-quotient110-model-draft/AQ22Quotient110Residuals.lean.src','569bcc47ad1b0ad31f9b603f0f96afba70496d3feaf221d255cc31f05b41467b')
pin('research/adaptive-aq22-quotient110-model-draft/receipt.json','908d966815a471c0b8a175a60bc0a4e402f7485b0f707f73fd653a5aa525b3fb')
pin('reviews/adaptive-aq22-two-quotients110-independent/result.json','6cc3d19451dff340d051166103b9a0178258d975b22927976da794dd7d70147b')
g=json.loads(pin('research/adaptive-aq22-two-quotients110/candidate.json','b82ef3f8e45cc260d8ffee26f3f8fa7ef2f207834829aee1a5ac357fcab0ffc1'))
p=json.loads(pin('research/adaptive-square-sums22-degree10/candidate.json','1266b143c5512351739ea2c71fc8e0b8b0e5cecc599392f128c0803ff78ce106'))
assert [p['witnesses'][i] for i in (9,10,13,14,16,17,18,19,21)]==['eta','zeta','scaleVariable','mainScaleVariable','ellVariable','cSquareVariable','zValueVariable','dValueVariable','deltaVariable']
assert [g['witnesses'][i] for i in (13,14,18,19)]==['scaleVariable','mainScaleVariable','firstQuotient','mainQuotient']
assert 'if i.val=18 then u else if i.val=19 then t else v i' in t
assert 'if i.val=18 then v 13*v 18 else if i.val=19 then v 14*v 19 else v i' in t
assert w.count('ArithmeticAdaptiveQuotients2011.scaled_quotient')==2
for x in ['(v 13) (v 18) (1+v 16*(v 16+(v 9+v 10))) (hv 13) h0','(v 14) (v 19) (1+v 21*v 17) (hv 14) h1','rw [←hu]; exact hv 18','rw [←ht]; exact hv 19']:assert x in w,x
def theorem(n):
 m=re.search(r'(?ms)^theorem '+re.escape(n)+r'\b(.*?)(?=^theorem |^end DiophantineConsistency)',s);assert m,n;return m.group(1)
for i in range(13):
 q=theorem('relation%02d'%i)
 assert f'AdaptiveAQ22Zeros.residuals p {i})' in q and f'AQ22Quotient110ResidualsDraft.residuals p {i})' in q
 assert 'extend v k' in q
 if i<2:assert f'ι (v {13+i}) * ι (v {13+i}) *' in q
assert 'extend (project v u t)=v' in theorem('extend_project')
assert 'u*u=1+v 16*(v 16+(v 9+v 10))' in theorem('project_norm0')
assert 't*t=1+v 21*v 17' in theorem('project_norm1')
def branches(n):return re.split(r'(?m)^  · ',theorem(n).split('fin_cases i',1)[1])[1:]
e=branches('extend_zero');z=branches('project_zero');assert len(e)==len(z)==13
for i,x in enumerate(e):
 assert f'relation{i:02d} p v' in x and f'hc {i}' in x,i
 if i<2:assert 'mul_zero' in x
for i,x in enumerate(z):
 if i<2:assert f'project_norm{i} p v u t h'+('un' if i==0 else 'tn') in x
 else:assert f'AdaptiveAQ22Zeros.residuals p {i})' in x and f'using hp {i}' in x and f'relation{i:02d} p (project v u t)' in x,i
q=theorem('graphZeroObligations');assert 'project_zero CurrentWindowCarry2011.ports' in q and 'extend_zero CurrentWindowCarry2011.ports' in q
assert 'AQ22Quotient110ConditionalTransferDraft.native_equivalence graphZeroObligations' in theorem('native_equivalence')
assert 'IPRAAQ22Native.bridge22' in t and 'mappedNativeRefutation embedding' in theorem('native_equivalence')
assert not re.search(r'(?m)^\s*(?:sorry|axiom)\b',s+t+w+r)
print(json.dumps({'scope':'static source and case audit only; no Lean elaboration or axioms','pointwise_residual_relations':13,'extend_cases':13,'project_cases':13,'scaled_norm_indices':[0,1],'quotient_slots':[18,19],'scale_slots':[13,14],'finite_case_order_assumed':True,'closed_client_source_unelaborated':True},sort_keys=True,indent=2))
