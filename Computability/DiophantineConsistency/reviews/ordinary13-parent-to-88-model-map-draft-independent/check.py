#!/usr/bin/env python3
"""Independent positive parent-to-88 model source review; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary13-parent-to-88-model-map-draft'
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,str(p);return b
s=pin(A/'ModelMapParentTo88.lean','121168903a5b87c6975f98f3f7d9383c5df846125bb4f7fff26a247a2efd8319').decode()
pin(A/'check_source.py','8ab4f0f49408abb22239efa809e60a1019aa2e0c4dd4df79bd9ff221f7118d5c')
receipt=pin(A/'observation.json','f0730ee76bd74d9ba305fda566a75721e19c766a26953d167303f3ed9b45d4d0')
r=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary13-parent-to-88-model-map-draft-independent/`.\n')
assert r.endswith(tail) and sha(r[:-len(tail)])=='fc31af1bf80acdf3c5bd4fa66ff84db7caec8c51897f915de8c9cf1c488487ed'
for name,ch,rh in (
 ('ordinary13-parent-transport-quotients-draft-independent','2fcfaebf6fbb2df8aabac391b2185045526e2330c23f2ffa7e237149968e9d38','6cb501f7c88bc31a170da8157dcbf08f178f12da66025bfbc81be53b400c8d69'),
 ('ordinary13-parent-four-fields-draft-independent','4bff480a682d2de17fd8156077b8a470b6131fbd698016e6618f9f469ce3f60c','650ba7a1177e1a52b47a89a4309e94b23b75279858e48151000eafa03d096757'),
 ('ordinary13-parent-to-88-guard-draft-independent','d2a414559b932add03f76dbb8de1316ee0d5761c9fa1fdf34da72397cf678238','c3bc70b526a47246b49b4b9c84aaeb92fc691d6b1d0c2987c0001884e160c075'),
 ('ordinary13-parent-to-88-first-draft-independent','1ab654fcb89e39666691fce8d3e162dd4ac404d30aca65615e158682bed243f8','052c3f69835d25c7e35283934b53b5a39cb47db353a4f84087af23c64bd0d4a4')):
 p=D/'reviews'/name;pin(p/'check.py',ch);pin(p/'result.json',rh)
for f in ('ParentTransportQuotientsDraft.quotient_bundle p v hb hv hz',
 'ParentTo88FirstDraft.first_zero p v s tau t hY\' hn\'',
 'ParentTo88GuardDraft.guard_of_balance p v (sigma v s tau) t hbal',
 'ParentFourFieldsDraft.fields_of_zero pi v hz',
 'target_positive v s tau t hv htau ht','rw [cast_target v s tau t]',
 'rw [hf,hm,ha,hs0,hg]'):
 assert f in s,f
for root in range(1,20):
 v=list(range(1,14));t=1;w=v[:8]+[root]+v[9:]+[t]
 assert len(w)==14 and all(x>0 for x in w)
 assert all(w[j]==v[j] for j in range(13) if j!=8)
rr=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
assert not rr.stderr and rr.stdout==receipt
print(json.dumps({'scope':'positive 13-parent to 88 model-map source review; no Lean','prior_component_reviews':'pinned, not rerun'},sort_keys=True,indent=2))
