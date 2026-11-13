#!/usr/bin/env python3
"""Independent 88-to-parent nonfirst field source review; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-88-parent-fields-draft'
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,str(p);return b
s=pin(A/'ParentFields88.lean','b1ba62bd7c416935973f9e3a42e66dad50eaa4133691e6962215e7ff5ef05dab').decode()
pin(A/'check_source.py','7cc61c7d47be8d2c5c4620a3fc8221644e134bfa38bcbb9910dff03ccf35050c')
receipt=pin(A/'observation.json','54aaba9791180bf79dbb6e68f89e38ac5ffe55d76b30cceaefe3de51a7ccc0db')
r=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-88-parent-fields-draft-independent/`.\n')
assert r.endswith(tail) and sha(r[:-len(tail)])=='33650d83e9ee3ecf83fc8f23447a98054fb66fe774ece84a8d033a5e22b9b654'
for name,ch,rh in (
 ('ordinary14-88-parent-ring-client-draft-independent','880c9b6e5b89a922d05f35414367af24a5e4d1dea0667479ce6fd7add019e43a','ee5684d0c6d91a32eb601dc8370b1195201e716a29cfeca7c8a5593ab5a4a848'),
 ('ordinary14-88-guard-draft-independent','11b01dfb20f0c90bbf0c28c638cf7a95bc0e02ed6814dc65d45cffd8af0d6c90','35cda6ae4546078790eee91db89cd5933fcca8140d9589de7539ce303602d03e')):
 p=D/'reviews'/name;pin(p/'check.py',ch);pin(p/'result.json',rh)
for f in ('(hz : InternalZero (P88QuotientGuarded.graph p).output v)',
 '(eval (P88QuotientGuarded.graph p).aux v-1)',
 'exact ⟨h.2.1,h.2.2.1,h.2.2.2.1⟩',
 '(r : DiffRing V)','rw [Ring88ToParentDraft.main_eval]',
 'rw [Ring88ToParentDraft.aux_eval]','rw [Ring88ToParentDraft.strong_eval]'):
 assert f in s,f
rr=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
assert not rr.stderr and rr.stdout==receipt
print(json.dumps({'scope':'88 own-zero parent nonfirst-field source review; no Lean','prior_component_reviews':'pinned, not rerun'},sort_keys=True,indent=2))
