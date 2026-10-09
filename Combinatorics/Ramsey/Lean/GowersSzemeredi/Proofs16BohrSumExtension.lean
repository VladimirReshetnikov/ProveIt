import GowersSzemeredi.Proofs16CompatibleBohrSums

/-! Extend compatible local Freiman-linear maps to a sum domain. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def bohrQuarterSum {N : Nat} [NeZero N] (T U : Finset (ZMod N)) (r : Real) : Finset (ZMod N) :=
  ((bohr T (r/4)) ×ˢ bohr U (r/4)).image (fun p => p.1+p.2)

def bohrSumExtension {N : Nat} [NeZero N] (T U : Finset (ZMod N))
    (f g : ZMod N → ZMod N) (r : Real) (z : ZMod N) : ZMod N :=
  if h : ∃ p ∈ (bohr T (r/4)) ×ˢ bohr U (r/4), p.1+p.2 = z then
    f (Classical.choose h).1+g (Classical.choose h).2 else 0

/-- Every quarter-radius representation gives the chosen extension value. -/
theorem bohrSumExtension_spec {N : Nat} [NeZero N]
    (T U : Finset (ZMod N)) (f g : ZMod N → ZMod N) {r : Real} (hr : 0 ≤ r)
    (hf : IsFreimanLinearOn (bohr T r) f) (hg : IsFreimanLinearOn (bohr U r) g)
    (hf0 : f 0 = 0) (hg0 : g 0 = 0)
    (hfg : ∀ z ∈ bohr T r, z ∈ bohr U r → f z = g z)
    {a b : ZMod N} (ha : a ∈ bohr T (r/4)) (hb : b ∈ bohr U (r/4)) :
    bohrSumExtension T U f g r (a+b) = f a+g b := by
  have hex : ∃ p ∈ (bohr T (r/4)) ×ˢ bohr U (r/4), p.1+p.2 = a+b :=
    ⟨(a,b),Finset.mem_product.mpr ⟨ha,hb⟩,rfl⟩
  rw [bohrSumExtension,dif_pos hex]
  have hp := Classical.choose_spec hex
  exact compatible_bohr_sum_value_unique T U f g hr hf hg hf0 hg0 hfg
    (Finset.mem_product.mp hp.1).1 (Finset.mem_product.mp hp.1).2 ha hb hp.2

/-- The extension is Freiman-linear on the entire sum domain. -/
theorem bohrSumExtension_freiman {N : Nat} [NeZero N]
    (T U : Finset (ZMod N)) (f g : ZMod N → ZMod N) {r : Real} (hr : 0 ≤ r)
    (hf : IsFreimanLinearOn (bohr T r) f) (hg : IsFreimanLinearOn (bohr U r) g)
    (hf0 : f 0 = 0) (hg0 : g 0 = 0)
    (hfg : ∀ z ∈ bohr T r, z ∈ bohr U r → f z = g z) :
    IsFreimanLinearOn (bohrQuarterSum T U r) (bohrSumExtension T U f g r) := by
  intro x y z w hx hy hz hw heq
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hw
  have hs {a b : ZMod N} := bohrSumExtension_spec T U f g hr hf hg hf0 hg0 hfg (a := a) (b := b)
  rw [hs (Finset.mem_product.mp ha).1 (Finset.mem_product.mp ha).2,
    hs (Finset.mem_product.mp hb).1 (Finset.mem_product.mp hb).2,
    hs (Finset.mem_product.mp hc).1 (Finset.mem_product.mp hc).2,
    hs (Finset.mem_product.mp hd).1 (Finset.mem_product.mp hd).2]
  apply compatible_bohr_sum_quadruple T U f g hr hf hg hf0 hg0 hfg
    ![a.1,b.1,c.1,d.1] ![a.2,b.2,c.2,d.2] _ _ heq
  · intro i; fin_cases i
    · exact (Finset.mem_product.mp ha).1
    · exact (Finset.mem_product.mp hb).1
    · exact (Finset.mem_product.mp hc).1
    · exact (Finset.mem_product.mp hd).1
  · intro i; fin_cases i
    · exact (Finset.mem_product.mp ha).2
    · exact (Finset.mem_product.mp hb).2
    · exact (Finset.mem_product.mp hc).2
    · exact (Finset.mem_product.mp hd).2

/-- Normalization and both original maps are preserved on quarter domains. -/
theorem bohrSumExtension_restrict {N : Nat} [NeZero N]
    (T U : Finset (ZMod N)) (f g : ZMod N → ZMod N) {r : Real} (hr : 0 ≤ r)
    (hf : IsFreimanLinearOn (bohr T r) f) (hg : IsFreimanLinearOn (bohr U r) g)
    (hf0 : f 0 = 0) (hg0 : g 0 = 0)
    (hfg : ∀ z ∈ bohr T r, z ∈ bohr U r → f z = g z) :
    bohrSumExtension T U f g r 0 = 0 ∧
      (∀ z ∈ bohr T (r/4), bohrSumExtension T U f g r z = f z) ∧
      (∀ z ∈ bohr U (r/4), bohrSumExtension T U f g r z = g z) := by
  have h0T := zero_mem_bohr T (by positivity : 0 ≤ r/4)
  have h0U := zero_mem_bohr U (by positivity : 0 ≤ r/4)
  have hs {a b : ZMod N} := bohrSumExtension_spec T U f g hr hf hg hf0 hg0 hfg (a := a) (b := b)
  refine ⟨?_,?_,?_⟩
  · simpa only [hf0,hg0,add_zero] using hs h0T h0U
  · intro z hz
    simpa only [hg0,add_zero] using hs hz h0U
  · intro z hz
    simpa only [hf0,zero_add] using hs h0T hz

end LeanProofs.GowersSzemeredi
