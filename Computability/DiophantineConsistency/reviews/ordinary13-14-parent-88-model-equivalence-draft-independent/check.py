#!/usr/bin/env python3
"""Independent parent/88 natural-port model-iff source review; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary13-14-parent-88-model-equivalence-draft'
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,str(p);return b
s=pin(A/'Parent88Equivalence.lean','518a3b5f568c63c64cc7df0c45c8aaf813a44ad8a2bd7f114e59e6af185609eb').decode()
pin(A/'check_source.py','c33e0ccc34b45c9841205c0011c9e1abb3078016ae0ba091d25a03ac47b81cb6')
receipt=pin(A/'observation.json','7e36c968d85f757abfb525ee63bcf1641ed754a9f68c51b5ea0d9e0fec1c3238')
r=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary13-14-parent-88-model-equivalence-draft-independent/`.\n')
assert r.endswith(tail) and sha(r[:-len(tail)])=='4627b8776c1903710088a4efc6ea41486f7abea04eb78b82a45db7b3e08a75b8'
for name,ch,rh in (
 ('ordinary13-parent-to-88-model-map-draft-independent','10af0e1dddfe6245dc883036bc8802fb4decc12a6f2ddd84b43f1a05e9728c85','9f63ceb6a32ab9fda624896f76192876e10d90cd0ff1664cd1760c0c1f3f1f1b'),
 ('ordinary14-88-to-parent-model-map-draft-independent','3dcc35e5938eb71bd304c236137d36eb0608afeefbffcc4d88647a79dbec46b5','aff6aa752ae30f3a752aaa71d8ffe241288e6e72855257f8346dfe6bde885c31')):
 p=D/'reviews'/name;pin(p/'check.py',ch);pin(p/'result.json',rh)
for f in ('(p : Fin 4 → ℕ) (hb : 0<(p 0:V))','P88FourSquare.graph (fun j => (p j : ℤ))',
 'P88QuotientGuarded.graph (fun j => (p j : ℤ))',
 'ModelMapParentTo88Draft.positive_map p v hb hv hz',
 'ModelMap88ToParentDraft.positive_map (fun j => (p j : ℤ)) (p 0:V) w hb',
 '(P72Root.cast_port p 0) hw hz'):
 assert f in s,f
rr=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
assert not rr.stderr and rr.stdout==receipt
print(json.dumps({'scope':'13-parent/14 quotient-88 source iff review; no Lean','prior_component_reviews':'pinned, not rerun'},sort_keys=True,indent=2))
