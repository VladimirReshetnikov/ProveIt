import GowersSzemeredi.Proofs05PolynomialDiameter
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Affine substitution and height reduction for multilinear polynomials

A downward-closed finite family of coordinate subsets replaces the arbitrary
linear extension in the paper's height induction. Removing a maximal member
reduces its cardinality; all terms introduced by translation stay in the
family. The coefficient calculation works over every commutative ring.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
namespace LeanProofs.GowersSzemeredi

/-- A family contains every subset of each of its members. -/
def MonomialFamilyClosed {ι : Type*} (F : Finset (Finset ι)) : Prop :=
  ∀ S ∈ F, ∀ T, T ⊆ S → T ∈ F

/-- Evaluation of a square-free polynomial supported on a finite family. -/
def multiaffineEval {ι R : Type*} [CommRing R]
    (F : Finset (Finset ι)) (c : Finset ι → R) (x : ι → R) : R :=
  ∑ S ∈ F, c S * ∏ i ∈ S, x i

/-- Coefficients after the common-step substitution x_i = a_i + d*t_i. -/
def multiaffineAffineCoeff {ι R : Type*} [DecidableEq ι] [CommRing R]
    (F : Finset (Finset ι)) (c : Finset ι → R) (a : ι → R) (d : R)
    (T : Finset ι) : R :=
  d ^ T.card * ∑ S ∈ F, if T ⊆ S then c S * ∏ i ∈ S \ T, a i else 0

/-- Expand a single square-free monomial after affine substitution. -/
theorem multiaffine_monomial_affine {ι R : Type*} [DecidableEq ι] [CommRing R]
    (S : Finset ι) (a x : ι → R) (d : R) :
    (∏ i ∈ S, (a i + d * x i)) =
      ∑ T ∈ S.powerset, (d ^ T.card * ∏ i ∈ S \ T, a i) * ∏ i ∈ T, x i := by
  rw [show (fun i => a i + d * x i) = (fun i => d * x i + a i) by funext i; ring]
  rw [Finset.prod_add]
  apply Finset.sum_congr rfl
  intro T _
  rw [Finset.prod_mul_distrib, Finset.prod_const]
  ring

/-- The entire affine expansion remains in any downward-closed family. -/
theorem multiaffineEval_affine {ι R : Type*} [DecidableEq ι] [CommRing R]
    (F : Finset (Finset ι)) (hF : MonomialFamilyClosed F)
    (c : Finset ι → R) (a x : ι → R) (d : R) :
    multiaffineEval F c (fun i => a i + d * x i) =
      multiaffineEval F (multiaffineAffineCoeff F c a d) x := by
  unfold multiaffineEval
  calc
    (∑ S ∈ F, c S * ∏ i ∈ S, (a i + d * x i)) =
        ∑ S ∈ F, ∑ T ∈ S.powerset,
          c S * ((d ^ T.card * ∏ i ∈ S \ T, a i) * ∏ i ∈ T, x i) := by
      apply Finset.sum_congr rfl
      intro S _
      rw [multiaffine_monomial_affine, Finset.mul_sum]
    _ = ∑ S ∈ F, ∑ T ∈ F,
          if T ⊆ S then c S * ((d ^ T.card * ∏ i ∈ S \ T, a i) * ∏ i ∈ T, x i) else 0 := by
      apply Finset.sum_congr rfl
      intro S hS
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext T
        simp only [Finset.mem_powerset, Finset.mem_filter]
        exact ⟨fun h => ⟨hF S hS T h, h⟩, fun h => h.2⟩
      · intro T _; rfl
    _ = ∑ T ∈ F, ∑ S ∈ F,
          if T ⊆ S then c S * ((d ^ T.card * ∏ i ∈ S \ T, a i) * ∏ i ∈ T, x i) else 0 :=
      Finset.sum_comm
    _ = ∑ T ∈ F, multiaffineAffineCoeff F c a d T * ∏ i ∈ T, x i := by
      apply Finset.sum_congr rfl
      intro T _
      unfold multiaffineAffineCoeff
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro S _
      split_ifs <;> ring

/-- A maximal monomial receives no contributions from larger monomials. -/
theorem multiaffineAffineCoeff_maximal {ι R : Type*} [DecidableEq ι] [CommRing R]
    (F : Finset (Finset ι)) (A : Finset ι) (hA : A ∈ F)
    (hmax : ∀ S ∈ F, A ⊆ S → S = A)
    (c : Finset ι → R) (a : ι → R) (d : R) :
    multiaffineAffineCoeff F c a d A = c A * d ^ A.card := by
  unfold multiaffineAffineCoeff
  rw [Finset.sum_eq_single A]
  · simp [mul_comm]
  · intro S hS hSA
    have hnot : ¬ A ⊆ S := fun h => hSA (hmax S hS h)
    simp [hnot]
  · exact fun h => (h hA).elim

/-- Erasing a maximal monomial preserves downward closure. -/
theorem MonomialFamilyClosed.erase_maximal {ι : Type*} [DecidableEq ι]
    {F : Finset (Finset ι)} (hF : MonomialFamilyClosed F) (A : Finset ι)
    (hmax : ∀ S ∈ F, A ⊆ S → S = A) : MonomialFamilyClosed (F.erase A) := by
  intro S hS T hTS
  obtain ⟨hSA, hSF⟩ := Finset.mem_erase.mp hS
  apply Finset.mem_erase.mpr
  refine ⟨?_, hF S hSF T hTS⟩
  intro hTA
  subst T
  exact hSA (hmax S hSF hTS)

/-- Affine substitution splits into the maximal term and a polynomial with
one fewer permitted monomial. -/
theorem multiaffine_affine_height_drop {ι R : Type*} [DecidableEq ι] [CommRing R]
    (F : Finset (Finset ι)) (hF : MonomialFamilyClosed F)
    (A : Finset ι) (hA : A ∈ F) (hmax : ∀ S ∈ F, A ⊆ S → S = A)
    (c : Finset ι → R) (a x : ι → R) (d : R) :
    multiaffineEval F c (fun i => a i + d * x i) =
      c A * d ^ A.card * (∏ i ∈ A, x i) +
        multiaffineEval (F.erase A) (multiaffineAffineCoeff F c a d) x := by
  rw [multiaffineEval_affine F hF]
  unfold multiaffineEval
  rw [← Finset.add_sum_erase _ _ hA, multiaffineAffineCoeff_maximal F A hA hmax]

/-- Every finite nonempty family has a member maximal under inclusion. -/
theorem monomialFamily_exists_maximal {ι : Type*} [DecidableEq ι]
    (F : Finset (Finset ι)) (hF : F.Nonempty) :
    ∃ A ∈ F, ∀ S ∈ F, A ⊆ S → S = A := by
  obtain ⟨A, hA, hmax⟩ := F.exists_max_image Finset.card hF
  refine ⟨A, hA, ?_⟩
  intro S hS hAS
  exact (Finset.eq_of_subset_of_card_le hAS (hmax S hS)).symm

/-- Boolean monomial indices and subsets describe the same square-free terms. -/
def boolMonomialEquiv (k : Nat) : (Fin k → Bool) ≃ Finset (Fin k) where
  toFun e := Finset.univ.filter fun i => e i
  invFun S := fun i => decide (i ∈ S)
  left_inv e := by funext i; simp
  right_inv S := by ext i; simp

/-- Convert the catalogue's Boolean-indexed coefficients to subset indices. -/
theorem isMultilinear_iff_multiaffineEval {N k : Nat} (mu : Point N k → ZMod N) :
    IsMultilinear mu ↔ ∃ c : Finset (Fin k) → ZMod N,
      ∀ x, mu x = multiaffineEval Finset.univ c x := by
  classical
  have hprod (e : Fin k → Bool) (x : Point N k) :
      (∏ i ∈ boolMonomialEquiv k e, x i) = ∏ i, if e i then x i else 1 := by
    simp [boolMonomialEquiv, Finset.prod_filter]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨fun S => c ((boolMonomialEquiv k).symm S), ?_⟩
    intro x
    rw [hc, multiaffineEval, ← (boolMonomialEquiv k).sum_comp]
    apply Finset.sum_congr rfl
    intro e _
    simp only [Equiv.symm_apply_apply, hprod]
  · rintro ⟨c, hc⟩
    refine ⟨fun e => c (boolMonomialEquiv k e), ?_⟩
    intro x
    rw [hc, multiaffineEval, ← (boolMonomialEquiv k).sum_comp]
    apply Finset.sum_congr rfl
    intro e _
    rw [hprod]

/-- Any finitely supported square-free expression is multilinear in the
catalogue's sense. -/
theorem isMultilinear_multiaffineEval {N k : Nat}
    (F : Finset (Finset (Fin k))) (c : Finset (Fin k) → ZMod N) :
    IsMultilinear (multiaffineEval F c) := by
  classical
  apply (isMultilinear_iff_multiaffineEval _).2
  refine ⟨fun S => if S ∈ F then c S else 0, ?_⟩
  intro x
  unfold multiaffineEval
  simp only [ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  simp

/-- Bound a square-free term on an index box with coordinate upper bounds u. -/
theorem diameterAtMost_multiaffine_monomial {N k u : Nat} [NeZero N]
    (B : Finset (Fin k → Nat)) (S : Finset (Fin k)) (a : ZMod N)
    (hB : ∀ x ∈ B, ∀ i ∈ S, x i ≤ u) :
    diameterAtMost (B.image fun x => a * ∏ i ∈ S, (x i : ZMod N))
      (u ^ S.card * centeredAbs a) := by
  have hprod (x : Fin k → Nat) (hx : x ∈ B) : (∏ i ∈ S, x i) ≤ u ^ S.card := by
    calc
      (∏ i ∈ S, x i) ≤ ∏ _i ∈ S, u := Finset.prod_le_prod' (hB x hx)
      _ = u ^ S.card := Finset.prod_const _
  simpa only [Nat.cast_prod] using
    diameterAtMost_bounded_multiples B a (fun x => ∏ i ∈ S, x i) (u ^ S.card) hprod

end LeanProofs.GowersSzemeredi
