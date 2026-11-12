#!/usr/bin/env python3
"""Check inert witness-order patch snapshots; does not run Lean."""
import hashlib,json
from pathlib import Path
D=Path(__file__).resolve().parents[2]
R=D.parents[1]
P=Path(__file__).resolve().parent
paths={
 'j_original': (D/'research/ordinary14-natural81-jshift-model-draft/Natural81JShift.lean','f8e6436236c850e013ea9b9f9bbfe2ce48c45625a1d58ac1865e0413d96a5ca6'),
 'j_patch': (P/'Natural81JShift.lean.src','697dcee2a09998b978870b34dd0c34dbe3e86051a74808f79d61ea9ea86ad198'),
 'p_original': (D/'research/ordinary14-natural-forced82-predecessor-draft/Predecessors82.lean','9b17307ba0245cf02d3f944510daab2560f34b1ba31f2b93323c279bf12d0d3e'),
 'p_patch': (P/'Predecessors82.lean.src','08ae139bb040b077bd8459ad879b8e229dcfdcdaabcc836c9ce0b72c1ecfe314'),
 'mathlib': (R/'.lake/packages/mathlib/Mathlib/Algebra/Order/Monoid/Unbundled/ExistsOfLE.lean','ec51021cf027765c0d1d9717db5beb56d8fe9a354feb2a18eb8a9233d8bf2e6c'),
 'example': (D/'Lean/DiophantineConsistency/ArithmeticOddOrdinateResidue.lean','cb4080289e247320fe8f5930c471ceb02c5ad01fc6cb73cbdd813468ade7fa7c')}
s={}
for k,(p,h) in paths.items():
 data=p.read_bytes(); assert hashlib.sha256(data).hexdigest()==h,k; s[k]=data.decode()
assert 'exists_add_of_le : ∀ {a b : α}, a ≤ b → ∃ c : α, b = a + c' in s['mathlib']
assert 'exact ⟨c, by rw [hc, add_comm]⟩' in s['example']
a='simpa [w] using hj'; b='simpa [w, add_comm] using hj'
assert s['j_original'].count(a)==1 and s['j_original'].replace(a,b)==s['j_patch']
a='  exact ⟨f, r, y, hf, hr, hy⟩'
b='  exact ⟨f, r, y, by simpa [add_comm] using hf, by simpa [add_comm] using hr,\n    by simpa [add_comm] using hy⟩'
assert s['p_original'].count(a)==1 and s['p_original'].replace(a,b)==s['p_patch']
print(json.dumps({'scope':'inert source alternatives and bounded declaration inspection; no Lean resolution or proof','originals_unchanged':2,'alternate_snapshots':2,'source_files_pinned':len(paths)},sort_keys=True,indent=2))
