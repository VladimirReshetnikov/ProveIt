import GowersSzemeredi.Proofs16BohrSumExtension
import GowersSzemeredi.Proofs16SmallImageRelations

/-! A selected containment supplies an actual normalized local extension.
Common sum representations preserve finite linear relations among such
extensions, with every intermediate point in a controlled Bohr domain. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem selected_bohr_sum_extension {N : Nat} [NeZero N]
    (T U D : Finset (ZMod N)) (f g : ZMod N → ZMod N) {r sigma : Real} (hr : 0 ≤ r)
    (hf : IsFreimanLinearOn (bohr T r) f) (hg : IsFreimanLinearOn (bohr U r) g)
    (hf0 : f 0 = 0) (hg0 : g 0 = 0)
    (hfg : ∀ z ∈ bohr T r, z ∈ bohr U r → f z = g z)
    (hD : bohr D sigma ⊆ bohrQuarterSum T U r) :
    let h := bohrSumExtension T U f g r
    IsFreimanLinearOn (bohr D sigma) h ∧ h 0 = 0 ∧
      (∀ z ∈ bohr T (r/4), h z = f z) ∧ (∀ z ∈ bohr U (r/4), h z = g z) := by
  refine ⟨?_,bohrSumExtension_restrict T U f g hr hf hg hf0 hg0 hfg⟩
  intro a b c d ha hb hc hd he
  exact bohrSumExtension_freiman T U f g hr hf hg hf0 hg0 hfg a b c d
    (hD ha) (hD hb) (hD hc) (hD hd) he

theorem bohr_sum_extensions_preserve_relation {N : Nat} [NeZero N] {I : Type*} [Fintype I]
    (T U : I → Finset (ZMod N)) (f g : I → ZMod N → ZMod N) (w : I → ZMod N)
    (B : Finset (ZMod N)) {r : Real} (hr : 0 ≤ r)
    (hf : ∀ i, IsFreimanLinearOn (bohr (T i) r) (f i))
    (hg : ∀ i, IsFreimanLinearOn (bohr (U i) r) (g i))
    (hf0 : ∀ i, f i 0 = 0) (hg0 : ∀ i, g i 0 = 0)
    (hfg : ∀ i, ∀ z ∈ bohr (T i) r, z ∈ bohr (U i) r → f i z = g i z)
    (hB : B ⊆ bohrQuarterSum (Finset.univ.biUnion T) (Finset.univ.biUnion U) r)
    (hleft : ∀ z ∈ bohr (Finset.univ.biUnion T) (r/4), ∑ i, w i*f i z = 0)
    (hright : ∀ z ∈ bohr (Finset.univ.biUnion U) (r/4), ∑ i, w i*g i z = 0) :
    ∀ z ∈ B, ∑ i, w i*bohrSumExtension (T i) (U i) (f i) (g i) r z = 0 := by
  intro z hz
  obtain ⟨p,hp,hpz⟩ := Finset.mem_image.mp (hB hz)
  obtain ⟨ha,hb⟩ := Finset.mem_product.mp hp
  have hs (i : I) : bohrSumExtension (T i) (U i) (f i) (g i) r z = f i p.1+g i p.2 := by
    rw [← hpz]
    exact bohrSumExtension_spec (T i) (U i) (f i) (g i) hr (hf i) (hg i) (hf0 i) (hg0 i) (hfg i)
      ((mem_bohr_family_union T (r/4) p.1).mp ha i) ((mem_bohr_family_union U (r/4) p.2).mp hb i)
  simp_rw [hs,mul_add]
  rw [Finset.sum_add_distrib,hleft p.1 ha,hright p.2 hb,add_zero]

end LeanProofs.GowersSzemeredi
