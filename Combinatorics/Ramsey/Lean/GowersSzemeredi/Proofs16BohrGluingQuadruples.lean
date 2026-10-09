import GowersSzemeredi.Proofs16SelectedBohrGluing

/-! The same higher containment transfers an additive quadruple identity
from both anchor families to their four glued local maps. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem bohr_sum_extensions_preserve_quadruple {N : Nat} [NeZero N]
    (T U : Fin 4 → Finset (ZMod N)) (f g : Fin 4 → ZMod N → ZMod N)
    (B : Finset (ZMod N)) {r : Real} (hr : 0 ≤ r)
    (hf : ∀ i, IsFreimanLinearOn (bohr (T i) r) (f i))
    (hg : ∀ i, IsFreimanLinearOn (bohr (U i) r) (g i))
    (hf0 : ∀ i, f i 0 = 0) (hg0 : ∀ i, g i 0 = 0)
    (hfg : ∀ i, ∀ z ∈ bohr (T i) r, z ∈ bohr (U i) r → f i z = g i z)
    (hB : B ⊆ bohrQuarterSum (Finset.univ.biUnion T) (Finset.univ.biUnion U) r)
    (hleft : ∀ z ∈ bohr (Finset.univ.biUnion T) (r/4), f 0 z+f 1 z = f 2 z+f 3 z)
    (hright : ∀ z ∈ bohr (Finset.univ.biUnion U) (r/4), g 0 z+g 1 z = g 2 z+g 3 z) :
    let h := fun i => bohrSumExtension (T i) (U i) (f i) (g i) r
    ∀ z ∈ B, h 0 z+h 1 z = h 2 z+h 3 z := by
  dsimp only
  have h := bohr_sum_extensions_preserve_relation T U f g (fun j : Fin 4 => if j.val < 2 then (1 : ZMod N) else -1) B hr hf hg hf0 hg0 hfg hB
    (fun z hz => by norm_num [Fin.sum_univ_four]; linear_combination hleft z hz)
    (fun z hz => by norm_num [Fin.sum_univ_four]; linear_combination hright z hz)
  intro z hz
  have hz' := h z hz
  norm_num [Fin.sum_univ_four] at hz'
  linear_combination hz'

end LeanProofs.GowersSzemeredi
