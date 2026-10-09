import GowersSzemeredi.Proofs16IndexPatternAveraging

/-! A common shift from a dense family of dense column slices. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Averaging ordered pairs in the slices produces a single centre used
by quantitatively many pairs of column and source point. -/
theorem exists_common_slice_shift {N : Nat} [NeZero N]
    (P : Finset (ZMod N)) (D : ZMod N → Finset (ZMod N))
    {delta lambda : Real} (_hd : 0 ≤ delta) (hl : 0 ≤ lambda)
    (hP : delta*N ≤ (P.card : Real))
    (hD : ∀ x ∈ P, lambda*N ≤ ((D x).card : Real)) :
    ∃ (t : ZMod N) (F : Finset (ZMod N × ZMod N)),
      delta*lambda^2*(N : Real)^2 ≤ F.card ∧
      ∀ p ∈ F, p.1 ∈ P ∧ p.2 ∈ D p.1 ∧ t ∈ D p.1 := by
  let S := P.biUnion (fun x => {x} ×ˢ (D x ×ˢ D x))
  have hcard : S.card = ∑ x ∈ P, (D x).card^2 := by
    rw [Finset.card_biUnion]
    · simp [pow_two]
    · intro x hx y hy hne
      apply Finset.disjoint_left.mpr
      intro p hp hq
      exact hne ((Finset.mem_singleton.mp (Finset.mem_product.mp hp).1).symm.trans
        (Finset.mem_singleton.mp (Finset.mem_product.mp hq).1))
  have hmass : delta*lambda^2*(N : Real)^3 ≤ S.card := by
    have hs : (S.card : Real) = ∑ x ∈ P, ((D x).card : Real)^2 := by exact_mod_cast hcard
    rw [hs]
    calc delta*lambda^2*(N : Real)^3 = (delta*N)*(lambda*N)^2 := by ring
      _ ≤ (P.card : Real)*(lambda*N)^2 := mul_le_mul_of_nonneg_right hP (sq_nonneg _)
      _ = ∑ _x ∈ P, (lambda*N)^2 := by simp
      _ ≤ ∑ x ∈ P, ((D x).card : Real)^2 := by
        apply Finset.sum_le_sum
        intro x hx
        exact pow_le_pow_left₀ (by positivity) (hD x hx) 2
  obtain ⟨t,ht⟩ := exists_large_label_fiber S (fun p => p.2.2)
  let E := S.filter (fun p => p.2.2 = t)
  let F := E.image (fun p => (p.1,p.2.1))
  have hF : F.card = E.card := by
    apply Finset.card_image_of_injOn
    intro p hp q hq he
    have ht' := (Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm
    have hp1 : p.1 = q.1 := congrArg (fun z : ZMod N × ZMod N => z.1) he
    have hp2 : p.2.1 = q.2.1 := congrArg (fun z : ZMod N × ZMod N => z.2) he
    exact Prod.ext hp1 (Prod.ext hp2 ht')
  have hcount : S.card ≤ N*F.card := by
    rw [hF]
    convert ht using 1
    simp only [ZMod.card]
    congr 1
    apply congrArg Finset.card
    ext p
    simp [E]
  refine ⟨t,F,?_,?_⟩
  · have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
    have hc : (S.card : Real) ≤ N*F.card := by exact_mod_cast hcount
    have h := hmass.trans hc
    apply (mul_le_mul_iff_right₀ hN).mp
    nlinarith only [h]
  · intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hqS,hqt⟩ := Finset.mem_filter.mp hq
    obtain ⟨x,hx,hq⟩ := Finset.mem_biUnion.mp hqS
    obtain ⟨hqx,hqD⟩ := Finset.mem_product.mp hq
    have he : q.1 = x := Finset.mem_singleton.mp hqx
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hqD
    exact ⟨he.symm ▸ hx,he.symm ▸ ha,he.symm ▸ (hqt ▸ hb)⟩

end LeanProofs.GowersSzemeredi
