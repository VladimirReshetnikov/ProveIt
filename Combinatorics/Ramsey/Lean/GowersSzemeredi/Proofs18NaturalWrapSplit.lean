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
  obtain ⟨P₀, hP₀, hc₀⟩ := P.exists_inter_Ico hP 0 (N - a)
  obtain ⟨P₁, hP₁, hc₁⟩ := P.exists_inter_Ico hP (N - a) N
  have hm₁ {x : Nat} (hx : x ∈ P₁.carrier) : N - a ≤ x ∧ x < N := by
    rw [hc₁] at hx
    exact Finset.mem_Ico.mp (Finset.mem_inter.mp hx).2
  obtain ⟨Q, hQ, hQc⟩ := P₀.exists_image_add_sub hP₀ a 0 fun _ _ => Nat.zero_le _
  obtain ⟨R, hR, hRc⟩ := P₁.exists_image_add_sub hP₁ a N fun x hx => by
    have := hm₁ hx
    omega
  refine ⟨Q, R, hQ, hR, ?_, ?_⟩
  · rw [hQc, hRc, Finset.disjoint_left]
    rintro _ hx hy
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v, hv, h⟩ := Finset.mem_image.mp hy
    have := hm₁ hv
    change a + v - N = a + u - 0 at h
    omega
  · rw [hQc, hRc, ← Finset.inter_eq_left.mpr hsub, Finset.range_eq_Ico,
      ← Finset.Ico_union_Ico_eq_Ico (Nat.zero_le (N - a)) (Nat.sub_le N a),
      Finset.inter_union_distrib_left, ← hc₀, ← hc₁, Finset.image_union]
    congr 1 <;> refine Finset.image_congr fun x hx => ?_
    · rw [hc₀] at hx
      have := (Finset.mem_Ico.mp (Finset.mem_inter.mp hx).2).2
      simp only [Nat.sub_zero, Nat.mod_eq_of_lt (by omega : a + x < N)]
    · have := hm₁ hx
      change a + x - N = (a + x) % N
      rw [Nat.mod_eq_sub_mod (by omega : N ≤ a + x), Nat.mod_eq_of_lt (by omega)]

end LeanProofs.GowersSzemeredi
