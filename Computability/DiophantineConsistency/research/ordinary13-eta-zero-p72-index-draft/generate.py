#!/usr/bin/env python3
"""Generate an unelaborated source-only eta-nonnegative index draft."""
from pathlib import Path
import hashlib, json, sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
here=Path(__file__).resolve().parent
root=here.parents[1]
src=root/'Lean/DiophantineConsistency/Compact44/P72Exact.lean'
b=src.read_bytes()
parent='a07730d92aefd39d86083d037f4772bacd7741788e2fff1f7669d33fa0ad05d3'
assert hashlib.sha256(b).hexdigest()==parent
s=b.decode()
part=s[s.index('private theorem large_of_six'):s.index('theorem exact_ordinary')]
def once(old,new):
 global part
 assert part.count(old)==1, (old,part.count(old))
 part=part.replace(old,new,1)
# Both public theorem binders lose only eta positivity; eta itself remains a model natural.
assert part.count('(hη : 0 < η) (hc : c = η + Y * k)')==2
part=part.replace('(hη : 0 < η) (hc : c = η + Y * k)','(hc : c = η + Y * k)')
once('  have hc0 : 0 < c := by rw [hc]; exact add_pos_of_pos_of_nonneg hη (Arithmetic.zero_le _)\n','')
once('  have hk0 : 0 < k := lt_of_lt_of_le (by simp) hRk\n', '''  have hk0 : 0 < k := lt_of_lt_of_le (by simp) hRk
  have hc0 : 0 < c := by
    rw [hc]
    exact add_pos_of_nonneg_of_pos (Arithmetic.zero_le _) (mul_pos hY0 hk0)
''')
once('''    k ≤ k * Y := le_mul_of_one_le_right (by simp) (le_trans (by simp : (1 : V) ≤ 2) hY2)
    _ < k * Y + η := lt_add_of_pos_right _ hη''','''    k = k * 1 := by ring
    _ < k * Y := mul_lt_mul_of_pos_left (lt_of_lt_of_le (by norm_num : (1 : V) < 2) hY2) hk0
    _ ≤ k * Y + η := le_add_of_nonneg_right (Arithmetic.zero_le _)''')
once('''    _ < k * Y + η := lt_add_of_pos_right _ hη
    _ = c := by rw [hc]; ring''','''    _ ≤ k * Y + η := le_add_of_nonneg_right (Arithmetic.zero_le _)
    _ = c := by rw [hc]; ring''')
once('index_window q X Y k R c a y0 n s μ m η hq3 hX hy0 hYq hη hc ha',
     'index_window q X Y k R c a y0 n s μ m η hq3 hX hy0 hYq hc ha')
once('''    _ ≤ k * Y := mul_le_mul (pos_iff_one_le.mp hk0) hY2 (by simp) (Arithmetic.zero_le _)) (le_of_lt (by
      calc k * Y < k * Y + η := lt_add_of_pos_right _ hη
        _ = c := by rw [hc]; ring))''','''    _ ≤ k * Y := mul_le_mul (pos_iff_one_le.mp hk0) hY2 (by simp) (Arithmetic.zero_le _)) (by
      calc k * Y ≤ k * Y + η := le_add_of_nonneg_right (Arithmetic.zero_le _)
        _ = c := by rw [hc]; ring)''')
assert 'hη' not in part
# index_close is intentionally copied unchanged, including all of its hypotheses.
header='''import DiophantineConsistency.Compact44.P72Exact

/-! Source-only draft derived from P72Exact. No Lean elaboration is claimed.
The eta argument is an arbitrary model natural, including zero. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
noncomputable section
namespace P72ExactEtaNaturalDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ModelDifferenceRing ArithmeticGcdNormalization ArithmeticPellRecurrence ArithmeticPellHalfIndex
open ArithmeticPellCongruences P72Mu
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

'''
out=(header+part+'end P72ExactEtaNaturalDraft\n').encode()
file=here/'P72ExactEtaNatural.lean.src'
if '--write' in sys.argv:
 file.write_bytes(out)
else:
 assert file.read_bytes()==out,'generated source differs'
print(json.dumps({'upstream_sha256':parent,'generated_sha256':hashlib.sha256(out).hexdigest(),'generation_matches':True,'lean_elaborated':False,'scope':'source transformation only; no model zero-map or equation reduction'},indent=2,sort_keys=True))
