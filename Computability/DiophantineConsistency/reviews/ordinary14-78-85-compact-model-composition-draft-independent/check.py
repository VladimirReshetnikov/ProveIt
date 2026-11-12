#!/usr/bin/env python3
"""Independent compact 78/85 source composition review; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-78-85-compact-model-composition-draft'
def sha(d):return hashlib.sha256(d).hexdigest()
def pin(p,h):
 d=p.read_bytes();assert sha(d)==h,str(p);return d
src=pin(A/'Compact78To85.lean','342a34729351a7d3feb0407282edefdbdf2a58d3a20cfdeec74d65ba86d52abb').decode()
pin(A/'check_source.py','a7bdf5457228f40eb11f618d396c7c0d1e2b9217b14a9ceb0818470cae7d47b1')
receipt=pin(A/'observation.json','07040c15039a6089a01b4be81e75bb6311220ce55feb3611582ce97d56e50b2a')
readme=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-78-85-compact-model-composition-draft-independent/`.\n')
assert readme.endswith(tail) and sha(readme[:-len(tail)])=='2bcd514afebdb014d8d25978ff430b605498c0e8592e387f47d01ea2b9481a7c'
for path,h in {
 'ordinary14-84-85-compact-model-equivalence-draft/CompactEquivalence.lean':'b7a3e58448aaf8683dd7d2438dc2d4673a24f4e3f6ec32749fcc2d2cbd3974ae',
 'ordinary14-84-to-78-model-composition-draft/ModelComposition.lean':'5d1fbd9bdf67df9d9c2c2a6d139d6decbd69753c6945dd4ca70dfff024eec84e',
}.items():pin(D/'research'/path,h)
ports=pin(D/'Lean/DiophantineConsistency/Compact44/CompactSymbolicPorts.lean','0fc8eb4f60e801b38a3a516cd23d9f44c1e9eda62609d34bd76764de7ac51414').decode()
assert 'def ports (β K L H : ℕ) : Fin 4 → ℕ := ![β,K,L,β+H]' in ports
for f in ('theorem positive_zero_iff (K : ℕ)',
 'ports CompactFixedBeta.betaNat K lowNat highNat',
 'P78AuxRoot.graph (fun j => (p j : ℤ))','P85QcubeGraph.graph (fun j => (p j : ℤ))',
 'C44Short15Facts.port_bounds (V:=V) CompactFixedBeta.betaNat K lowNat highNat',
 '(Model84To78CompositionDraft.positive_zero_iff_natural_ports p hb.1).symm.trans',
 '(CompactEquivalence8485Draft.positive_zero_iff K)'):
 assert f in src,f
def replay(script,result):
 r=subprocess.run([sys.executable,'-I','-S','-B',str(script)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
 assert not r.stderr and r.stdout==result
replay(A/'check_source.py',receipt)
for n in ('ordinary14-84-85-compact-model-equivalence-draft-independent','ordinary14-84-to-78-model-composition-draft-independent'):
 p=D/'reviews'/n;replay(p/'check.py',(p/'result.json').read_bytes())
print(json.dumps({'scope':'source interface and dependency review only; no Lean',
 'prelink_readme_sha256':sha(readme[:-len(tail)]),'independent_component_reviews':2},sort_keys=True,indent=2))
