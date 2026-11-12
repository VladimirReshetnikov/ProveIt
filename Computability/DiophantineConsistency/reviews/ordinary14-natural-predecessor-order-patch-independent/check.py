#!/usr/bin/env python3
"""Independently inspect inert patch deltas and witness orientations; no Lean."""
from pathlib import Path
import difflib,hashlib,json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2];P=D/'research/ordinary14-natural-predecessor-order-patch'
pins={
 str(P/'check.py'):'95ea3a0aaf28248729f73d5d14c3a766ff7124fd787b807e3db463a9bfc95c32',
 str(P/'result.json'):'0e92e2d1ede8f22075153c60b1bcefc80c583acfe28b93c3a4cdf88e50626b77',
 str(P/'Natural81JShift.lean.src'):'697dcee2a09998b978870b34dd0c34dbe3e86051a74808f79d61ea9ea86ad198',
 str(P/'Predecessors82.lean.src'):'08ae139bb040b077bd8459ad879b8e229dcfdcdaabcc836c9ce0b72c1ecfe314',
 str(D/'research/ordinary14-natural81-jshift-model-draft/Natural81JShift.lean'):'f8e6436236c850e013ea9b9f9bbfe2ce48c45625a1d58ac1865e0413d96a5ca6',
 str(D/'research/ordinary14-natural-forced82-predecessor-draft/Predecessors82.lean'):'9b17307ba0245cf02d3f944510daab2560f34b1ba31f2b93323c279bf12d0d3e',
 str(D/'research/ordinary14-natural-forced82-ring-bridge-draft/Natural82Model.lean'):'e10b5e7dcc6169fd4730f3bf4e9058081efa1ac4e628de382dcbfc2dcf244854',
 str(D/'research/ordinary14-natural81-endpoint-import-inventory/inventory.json'):'bfb90445976aed586a849295ddd5afa5c706b7da7c8b6519bb2bd022491e5f40',
 str(D/'Lean/DiophantineConsistency/ArithmeticOddOrdinateResidue.lean'):'cb4080289e247320fe8f5930c471ceb02c5ad01fc6cb73cbdd813468ade7fa7c',
 '/home/codex/src/Proofs/.lake/packages/mathlib/Mathlib/Algebra/Order/Monoid/Unbundled/ExistsOfLE.lean':'ec51021cf027765c0d1d9717db5beb56d8fe9a354feb2a18eb8a9233d8bf2e6c',
 '/tmp/ipra-foundation-guarded-v2-cjHUaJun/lib/FormalizedFormalLogic-Foundation/Foundation/FirstOrder/Arithmetic/PeanoMinus/Basic.lean':'856a38ddda30c1505f6d991e6033ef7c41ebc82418b503ab711dfe173dc72303',
}
s={}
for path,digest in pins.items():
 b=Path(path).read_bytes();assert hashlib.sha256(b).hexdigest()==digest,path;s[Path(path).name]=b.decode()
j=s['Natural81JShift.lean'];jp=s['Natural81JShift.lean.src'];p=s['Predecessors82.lean'];pp=s['Predecessors82.lean.src']
def diff(a,b):return [x for x in difflib.ndiff(a.splitlines(),b.splitlines()) if x.startswith(('- ','+ '))]
assert diff(j,jp)==['-       · simpa [w] using hj','+       · simpa [w, add_comm] using hj']
assert diff(p,pp)==['-   exact ⟨f, r, y, hf, hr, hy⟩','+   exact ⟨f, r, y, by simpa [add_comm] using hf, by simpa [add_comm] using hr,','+     by simpa [add_comm] using hy⟩']
assert 'exists_add_of_le : ∀ {a b : α}, a ≤ b → ∃ c : α, b = a + c' in s['ExistsOfLE.lean']
assert re.search(r'scoped instance : CanonicallyOrderedAdd M where\s+exists_add_of_le :=',s['Basic.lean'])
assert 'obtain ⟨c, hc⟩ := exists_add_of_le hA2' in s['ArithmeticOddOrdinateResidue.lean']
assert 'exact ⟨c, by rw [hc, add_comm]⟩' in s['ArithmeticOddOrdinateResidue.lean']
assert 'v81 0 = v82 0 + 1' in j and 'exists_add_of_le (pos_iff_one_le.mp' in j
assert '∃ f r y : V, v 3 = f + 1 ∧ v 8 = r + 1 ∧ v 11 = y + 1' in s['Natural82Model.lean']
assert p.count('exists_add_of_le (pos_iff_one_le.mp (pos_iff_ne_zero.mpr')==3
# The pinned endpoint inventory still refers to the original .lean files.
inv=json.loads(s['inventory.json']);rows={x['module']:x for x in inv['drafts_topological']}
assert rows['Natural81JShift']['path']=='research/ordinary14-natural81-jshift-model-draft/Natural81JShift.lean'
assert rows['Natural81JShift']['sha256']==pins[str(D/rows['Natural81JShift']['path'])]
assert rows['Predecessors82']['path']=='research/ordinary14-natural-forced82-predecessor-draft/Predecessors82.lean'
assert rows['Predecessors82']['sha256']==pins[str(D/rows['Predecessors82']['path'])]
assert all(path.endswith('.lean.src') for path in (str(P/'Natural81JShift.lean.src'),str(P/'Predecessors82.lean.src')))
for c in range(101):assert 1+c==c+1
print(json.dumps({'scope':'inert source byte deltas and bounded declaration inspection; no Lean name resolution or proof','pinned_files':len(pins),'original_modules_unchanged':2,'inert_alternatives':2,'witness_order_conversions':4,'natural_controls':101},sort_keys=True,indent=2))
