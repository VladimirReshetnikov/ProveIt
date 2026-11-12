#!/usr/bin/env python3
"""Independent compact 78/86 source composition review; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-78-86-compact-model-composition-draft'
def sha(d):return hashlib.sha256(d).hexdigest()
def pin(p,h):
 d=p.read_bytes();assert sha(d)==h,str(p);return d
src=pin(A/'Compact78To86.lean','3965881715e791f1b7d3b1c554a26a44fb8f1892d0cbfbe224dcf0447f54590a').decode()
pin(A/'check_source.py','421350ab81a6cff86b30506c8effb92a23a24e04cf25f9061c1e28a9640632cd')
receipt=pin(A/'observation.json','e5c494bcc89d7c4261a85b75fc8861294b3143ac31392e4296f8b8a02a11163f')
readme=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-78-86-compact-model-composition-draft-independent/`.\n')
assert readme.endswith(tail) and sha(readme[:-len(tail)])=='b50c87b9d0bfcfbfc7cfade0fe0f3003565b1ab31b4f4df390b9a1a4176e92d9'
for path,h in {
 'ordinary14-78-85-compact-model-composition-draft/Compact78To85.lean':'342a34729351a7d3feb0407282edefdbdf2a58d3a20cfdeec74d65ba86d52abb',
 'ordinary14-85-86-model-equivalence-draft/ModelEquivalence85To86.lean':'f540a89b57f708e15f641f25e7a2a6bf774a8b68899d7dcd4643b34851480157',
}.items():pin(D/'research'/path,h)
ports=pin(D/'Lean/DiophantineConsistency/Compact44/CompactSymbolicPorts.lean','0fc8eb4f60e801b38a3a516cd23d9f44c1e9eda62609d34bd76764de7ac51414').decode()
assert 'def ports (β K L H : ℕ) : Fin 4 → ℕ := ![β,K,L,β+H]' in ports
for f in ('theorem positive_zero_iff (K : ℕ)',
 'ports CompactFixedBeta.betaNat K lowNat highNat',
 'P78AuxRoot.graph (fun j => (p j : ℤ))','P86ResidueGraph.graph (fun j => (p j : ℤ))',
 'C44Short15Facts.port_bounds (V:=V) CompactFixedBeta.betaNat K lowNat highNat',
 '(Compact78To85Draft.positive_zero_iff K).trans',
 '(ModelEquivalence8586Draft.positive_zero_iff_natural_ports p hb.1)'):
 assert f in src,f
def replay(script,result):
 r=subprocess.run([sys.executable,'-I','-S','-B',str(script)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
 assert not r.stderr and r.stdout==result
replay(A/'check_source.py',receipt)
for n in ('ordinary14-78-85-compact-model-composition-draft-independent','ordinary14-85-86-model-equivalence-draft-independent'):
 p=D/'reviews'/n;replay(p/'check.py',(p/'result.json').read_bytes())
print(json.dumps({'scope':'source interface and dependency review only; no Lean',
 'prelink_readme_sha256':sha(readme[:-len(tail)]),'independent_component_reviews':2},sort_keys=True,indent=2))
