import GowersSzemeredi.Proofs16FiniteAlphabetCover

/-! Sum the finite-alphabet affine obstruction over fibres of a rectangle.
The affine coefficients may depend arbitrarily on the first coordinate,
so the bound applies in particular to restrictions of bilinear graphs. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem finiteAlphabet_fibrewise_affine_cover {X F : Type*} [DecidableEq X] [Field F] [DecidableEq F]
    {q : Nat} (U : Finset X) (V S : Finset F) (H : Finset (X × F)) (f : F → F)
    (hf : ∀ y ∈ V, f y ∈ S) (a b : X → Fin q → F) (beta : Real) (hbeta : 0 ≤ beta)
    (hbalanced : ∀ c : F, ((V.filter (fun y => f y = c)).card : Real) ≤ beta * V.card)
    (hsub : H ⊆ U.product V)
    (hcover : ∀ p ∈ H, ∃ i : Fin q, f p.2 = a p.1 i * p.2 + b p.1 i) :
    (H.card : Real) ≤ U.card * q * (beta * V.card + S.card) := by
  classical
  let T (x : X) := V.filter (fun y => (x, y) ∈ H)
  let C (x : X) := ({x} : Finset X).product (T x)
  have hcover' : H ⊆ U.biUnion C := by
    intro p hp
    have hp' := Finset.mem_product.mp (hsub hp)
    exact Finset.mem_biUnion.mpr ⟨p.1, hp'.1,
      Finset.mem_product.mpr ⟨Finset.mem_singleton_self _, Finset.mem_filter.mpr ⟨hp'.2, hp⟩⟩⟩
  have hcard : (H.card : Real) ≤ ∑ x ∈ U, ((T x).card : Real) := by
    have hc := (Finset.card_le_card hcover').trans Finset.card_biUnion_le
    have he (x : X) : (C x).card = (T x).card := by simp [C]
    simp_rw [he] at hc
    exact_mod_cast hc
  have hrow (x : X) : ((T x).card : Real) ≤ q * (beta * V.card + S.card) := by
    have hT : T x ⊆ V := Finset.filter_subset _ _
    have ht : ∀ y ∈ T x, ∃ i ∈ (Finset.univ : Finset (Fin q)), f y = a x i * y + b x i := by
      intro y hy
      obtain ⟨i, hi⟩ := hcover (x, y) (Finset.mem_filter.mp hy).2
      exact ⟨i, Finset.mem_univ _, hi⟩
    simpa only [Finset.card_univ, Fintype.card_fin] using
      finiteAlphabet_affine_cover_bound V S (T x) f hf Finset.univ (a x) (b x) beta hbeta hbalanced hT ht
  calc
    _ ≤ ∑ x ∈ U, ((T x).card : Real) := hcard
    _ ≤ ∑ _x ∈ U, ((q : Real) * (beta * V.card + S.card)) := Finset.sum_le_sum (fun x _ => hrow x)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

theorem finiteAlphabet_fibrewise_cover_five_sixteenths {X F : Type*} [DecidableEq X] [Field F] [DecidableEq F]
    {q : Nat} (U : Finset X) (V S : Finset F) (H : Finset (X × F)) (f : F → F)
    (hf : ∀ y ∈ V, f y ∈ S) (a b : X → Fin q → F) (beta : Real) (hbeta : 0 ≤ beta)
    (hbalanced : ∀ c : F, ((V.filter (fun y => f y = c)).card : Real) ≤ beta * V.card)
    (hsub : H ⊆ U.product V)
    (hcover : ∀ p ∈ H, ∃ i : Fin q, f p.2 = a p.1 i * p.2 + b p.1 i)
    (hsmall : (q : Real) * beta ≤ 9 / 32)
    (hwidth : (q : Real) * S.card ≤ (V.card : Real) / 32) :
    (H.card : Real) ≤ (5 / 16 : Real) * U.card * V.card := by
  have hc := finiteAlphabet_fibrewise_affine_cover U V S H f hf a b beta hbeta hbalanced hsub hcover
  have hm := mul_le_mul_of_nonneg_right hsmall (Nat.cast_nonneg V.card)
  have hr : (q : Real) * (beta * V.card + S.card) ≤ (5 / 16 : Real) * V.card := by
    nlinarith only [hm, hwidth]
  have ht := mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg U.card)
  nlinarith only [hc, ht]

end LeanProofs.GowersSzemeredi
