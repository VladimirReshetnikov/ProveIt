#!/usr/bin/env python3
"""Independent 88→13 positive model-map source review; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-88-to-parent-model-map-draft'
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,str(p);return b
s=pin(A/'ModelMap88ToParent.lean','f80607356308421e6d6b93cd5274bfb797caefaa536019524df8fbd263cc66ac').decode()
pin(A/'check_source.py','4b43eaa75fcdd89b0dd6d498a9987e50b5c223a05cd8f5b90fc67003e3f56224')
receipt=pin(A/'observation.json','a8a88e42efbc7f607025721dc23b32de8331ea8b7dbe27642c78f8885e18c8c0')
r=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-88-to-parent-model-map-draft-independent/`.\n')
assert r.endswith(tail) and sha(r[:-len(tail)])=='313492dbabbb11db10c65330ceb816523e913c444a7e54b537e85aae927712b1'
for name,ch,rh in (
 ('ordinary14-88-first-root-gap-draft-independent','93a249d2208875be0e121ca5360aa022675b76b7ea3e09a5d6a95d73c4248788','bde13ee1dbd8b9d02348f94b7e1967e182baf6043766fcb46b497ee1791005c5'),
 ('ordinary14-fresh-parent-root-draft-independent','b7cd6ffe4dd83a7ddd8f76fbc4e2673173b55006e795c7dd4997bf8dd01cb406','3af40a9ce64a90f53a22c3a2baf4b3c8ccf8ace1a9985402d97023653c791330'),
 ('ordinary14-88-parent-first-draft-independent','d7b3f13f02dde23e5467063a33fdf24d6d2b66f4fe1a1e5deed3c8226f6efe32','ebb7652521f898381584d827b5e0874c68907b223fd61edaae60e80eecb65724'),
 ('ordinary14-88-parent-fields-draft-independent','9beb62db7fd9d5343f75c6387695b7b15e409500bb4e29ac683ac692ac306f6e','b065065512e9efa45fd2071ebe3a1d6ecc2b7e07462365b95b07651694071f11')):
 p=D/'reviews'/name;pin(p/'check.py',ch);pin(p/'result.json',rh)
for f in ('Function.update (fun j : Fin 13 => v j.castSucc) 8 r',
 'FirstRootGap88Draft.quotient_and_root_gap p beta v hbeta (hv 0) (hv 6) (hv 7) (hv 9) (hv 10) hport hz',
 'FreshParentRootDraft.fresh_root m (k v) s tau (v 0*beta) (v 13) hb (hv 13) hgap',
 'ParentFirst88Draft.first_zero p beta v s tau r hport hz hY hn hrel',
 'ParentFields88Draft.projected_fields p v (ι r) hz',
 'rw [cast_parent v r]','rw [hf,ho.1,ho.2.1,ho.2.2]'):
 assert f in s,f
for root in range(1,20):
 v=list(range(1,15));w=v[:13];w[8]=root
 assert all(x>0 for x in w) and all(w[j]==v[j] for j in range(13) if j!=8)
rr=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
assert not rr.stderr and rr.stdout==receipt
print(json.dumps({'scope':'88-to-13 positive model-map source review; no Lean','prior_component_reviews':'pinned, not rerun'},sort_keys=True,indent=2))
