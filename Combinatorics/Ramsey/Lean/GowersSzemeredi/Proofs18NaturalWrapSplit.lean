import GowersSzemeredi.Proofs18NaturalClipping

/-! A translate of an ordinary progression shorter than a modulus crosses
its wrap boundary at most once. The two pieces remain ordinary progressions. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Split natural representatives of a translated progression at its unique
possible modular wrap. Empty pieces are allowed and are proper. -/
theorem NatAP.exists_modular_translate_split (P : NatAP) (hP : P.IsProper)
    (N a : Nat) (ha : a < N) (hsub : P.carrier ⊆ Finset.range N) :
    ∃ Q R : NatAP, Q.IsProper ∧ R.IsProper ∧ Disjoint Q.carrier R.carrier ∧
      Q.carrier ∪ R.carrier = P.carrier.image (fun x => (a + x) % N) := by
  classical
  obtain ⟨P₀, hP₀, hc₀⟩ := P.exists_inter_Ico hP 0 (N - a)
  obtain ⟨P₁, hP₁, hc₁⟩ := P.exists_inter_Ico hP (N - a) N
  obtain ⟨Q, hQ, hQc⟩ := P₀.exists_image_add_sub hP₀ a 0 (by intros; omega)
  obtain ⟨R, hR, hRc⟩ := P₁.exists_image_add_sub hP₁ a N (by
    intro x hx
    rw [hc₁] at hx
    have := (Finset.mem_Ico.mp (Finset.mem_inter.mp hx).2).1
    omega)
  have hsplit : P₀.carrier ∪ P₁.carrier = P.carrier := by
    rw [hc₀, hc₁]
    ext x
    have hx : x ∈ P.carrier → x < N := fun h => Finset.mem_range.mp (hsub h)
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_Ico]
    constructor
    · tauto
    · intro h
      have hxN := hx h
      by_cases hxcut : x < N - a
      · exact Or.inl ⟨h, by omega⟩
      · exact Or.inr ⟨h, by omega⟩
  have hQimage : Q.carrier = P₀.carrier.image (fun x => (a + x) % N) := by
    rw [hQc]
    apply Finset.image_congr
    intro x hx
    rw [hc₀] at hx
    have hx' := (Finset.mem_Ico.mp (Finset.mem_inter.mp hx).2).2
    simp only [Nat.sub_zero, Nat.mod_eq_of_lt (by omega : a + x < N)]
  have hRimage : R.carrier = P₁.carrier.image (fun x => (a + x) % N) := by
    rw [hRc]
    apply Finset.image_congr
    intro x hx
    rw [hc₁] at hx
    have hx' := Finset.mem_Ico.mp (Finset.mem_inter.mp hx).2
    change a + x - N = (a + x) % N
    rw [Nat.mod_eq_sub_mod (by omega : N ≤ a + x), Nat.mod_eq_of_lt (by omega)]
  refine ⟨Q, R, hQ, hR, ?_, ?_⟩
  · apply Finset.disjoint_left.mpr
    intro x hxQ hxR
    rw [hQc] at hxQ
    rw [hRc] at hxR
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hxQ
    obtain ⟨v, hv, hvu⟩ := Finset.mem_image.mp hxR
    rw [hc₁] at hv
    have hvN := Finset.mem_Ico.mp (Finset.mem_inter.mp hv).2
    change a + v - N = a + u - 0 at hvu
    omega
  · rw [hQimage, hRimage, ← Finset.image_union, hsplit]

/-- Intersecting the two unwrapped pieces with a target interval still uses
at most two ordinary progressions and gives the exact intersection. -/
theorem NatAP.exists_modular_translate_inter (P : NatAP) (hP : P.IsProper)
    (N a L : Nat) (ha : a < N) (hsub : P.carrier ⊆ Finset.range N) :
    ∃ Q R : NatAP, Q.IsProper ∧ R.IsProper ∧ Disjoint Q.carrier R.carrier ∧
      Q.carrier ∪ R.carrier = (P.carrier.image (fun x => (a + x) % N)) ∩ Finset.range L := by
  obtain ⟨Q₀, R₀, hQ₀, hR₀, hdis, hcover⟩ := P.exists_modular_translate_split hP N a ha hsub
  obtain ⟨Q, hQ, hQc⟩ := Q₀.exists_inter_Ico hQ₀ 0 L
  obtain ⟨R, hR, hRc⟩ := R₀.exists_inter_Ico hR₀ 0 L
  refine ⟨Q, R, hQ, hR, ?_, ?_⟩
  · rw [hQc, hRc]
    exact hdis.mono Finset.inter_subset_left Finset.inter_subset_left
  · rw [hQc, hRc, ← Finset.union_inter_distrib_right, hcover, ← Finset.range_eq_Ico]

end LeanProofs.GowersSzemeredi
