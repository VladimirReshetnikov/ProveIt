/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Polynomial.MultiaffinePolynomialBias

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem additiveBoxDifference_const_mul {R Z : Type*} [CommRing R]
    (n : ℕ) {X : Fin n → Type*} (a : R) (F : (∀ i, X i) → Z → R)
    (u v : ∀ i, X i) (z : Z) :
    additiveBoxDifference n (fun x t => a*F x t) u v z =
      a*additiveBoxDifference n F u v z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [additiveBoxDifference, ← mul_sub]
    exact ih _ (Fin.tail u) (Fin.tail v)

theorem additiveBoxDifference_booleanCoefficient {R Z α : Type*} [CommRing R]
    [DecidableEq α] (n : ℕ) {X : Fin n → Type*}
    (F : Finset α → (∀ i, X i) → Z → R) (s : Finset α)
    (u v : ∀ i, X i) (z : Z) :
    additiveBoxDifference n (fun x t => booleanCoefficient (fun r => F r x t) s) u v z =
      booleanCoefficient (fun r => additiveBoxDifference n (F r) u v z) s := by
  unfold booleanCoefficient
  rw [additiveBoxDifference_sum]
  simp_rw [additiveBoxDifference_const_mul]

theorem full_coefficient_eq_mixed_difference {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (hP : ∀ i, P.degreeOf i ≤ 1) :
    P.coeff (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin n))).val =
      additiveBoxDifference n (fun x (_ : Unit) => MvPolynomial.eval x P)
        (fun _ => 1) (fun _ => 0) () := by
  have he : (fun x (_ : Unit) => MvPolynomial.eval x P) =
      (fun x (_ : Unit) => multiaffineExpansion
        (fun S => P.coeff (SquarefreeIndex.ofFinset S).val) x) := by
    funext x t
    exact multiaffinePolynomial_eval P hP x
  rw [he]
  have h := multiaffineExpansion_box_difference n (X := fun _ => ℝ)
    (fun S (_ : Unit) => P.coeff (SquarefreeIndex.ofFinset S).val)
    (fun _ (x : ℝ) => x) (fun _ => 1) (fun _ => 0) ()
  simpa using h.symm

theorem affine_product_full_difference (n : ℕ) (a b : Fin n → ℝ) :
    additiveBoxDifference n (fun x (_ : Unit) => ∏ i, (a i*x i+b i))
      (fun _ => 1) (fun _ => 0) () = ∏ i, a i := by
  have h := additiveBoxDifference_product n (X := fun _ => ℝ) (fun _ : Unit => (1 : ℝ))
    (fun i (x : ℝ) => a i*x+b i) (fun _ => 1) (fun _ => 0) ()
  simpa using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem frozenBooleanBlock_full_difference {α : Type*} [Fintype α] [DecidableEq α]
    (n : ℕ) (label : Fin n → Option α) (c : Fin n → Option α → ℝ) (t : Finset α) :
    additiveBoxDifference n
      (fun x (_ : Unit) => booleanBlockValue (resampleGroupCoordinates label c x) t)
      (fun _ => 1) (fun _ => 0) () = ∏ i, (booleanFeature (label i) t : ℝ) := by
  simp_rw [booleanBlockValue_resample]
  exact affine_product_full_difference n _ _

theorem frozenBooleanJet_full_difference {α : Type*} [Fintype α] [DecidableEq α]
    (n : ℕ) (label : Fin n → Option α) (c : Fin n → Option α → ℝ)
    (S s : Finset α) (hlabel : ∀ a, (∃ i, label i = some a) ↔ a ∈ S) :
    additiveBoxDifference n
      (fun x (_ : Unit) => booleanCoefficient
        (fun t => booleanBlockValue (resampleGroupCoordinates label c x) t) s)
      (fun _ => 1) (fun _ => 0) () = if s=S then 1 else 0 := by
  rw [additiveBoxDifference_booleanCoefficient]
  simp_rw [frozenBooleanBlock_full_difference, booleanFeature_product label S hlabel]
  exact booleanCoefficient_monomial S s

theorem frozenBooleanPhase_full_difference {α : Type*} [Fintype α] [DecidableEq α]
    (n : ℕ) (label : Fin n → Option α) (c : Fin n → Option α → ℝ)
    (ξ : Finset α → ℝ) (S : Finset α)
    (hlabel : ∀ a, (∃ i, label i = some a) ↔ a ∈ S) :
    additiveBoxDifference n
      (fun x (_ : Unit) => booleanBlockPhase ξ (resampleGroupCoordinates label c x))
      (fun _ => 1) (fun _ => 0) () = ξ S := by
  unfold booleanBlockPhase
  rw [additiveBoxDifference_sum]
  simp_rw [additiveBoxDifference_const_mul,
    frozenBooleanJet_full_difference n label c S _ hlabel]
  simp

theorem frozenBooleanPhasePolynomial_coefficient {α : Type*} [Fintype α] [DecidableEq α]
    (n : ℕ) (label : Fin n → Option α) (c : Fin n → Option α → ℝ)
    (ξ : Finset α → ℝ) (S : Finset α)
    (hlabel : ∀ a, (∃ i, label i = some a) ↔ a ∈ S) :
    (frozenBooleanPhasePolynomial label c ξ).coeff
      (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin n))).val = ξ S := by
  rw [full_coefficient_eq_mixed_difference _ (frozenBooleanPhasePolynomial_degree label c ξ)]
  have he : (fun x (_ : Unit) => MvPolynomial.eval x (frozenBooleanPhasePolynomial label c ξ)) =
      (fun x (_ : Unit) => booleanBlockPhase ξ (resampleGroupCoordinates label c x)) := by
    funext x t
    exact frozenBooleanPhasePolynomial_eval label c ξ x
  rw [he]
  exact frozenBooleanPhase_full_difference n label c ξ S hlabel

end Erdos3

end

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators Classical

theorem full_mixed_difference_of_totalDegree {R : Type*} [CommRing R] {n : ℕ}
    (P : MvPolynomial (Fin n) R) (hP : P.totalDegree ≤ n) (u v : Fin n → R) :
    additiveBoxDifference n (fun x (_ : Unit) => eval x P) u v () =
      P.coeff (fullShiftExponent n) * ∏ i, (u i - v i) := by
  have he : (fun x (_ : Unit) => eval x P) =
      (fun x (_ : Unit) => ∑ d ∈ P.support, P.coeff d * ∏ i, x i ^ d i) := by
    funext x _
    conv_lhs => rw [P.as_sum]
    simp only [map_sum, eval_monomial, Finsupp.prod_pow]
  rw [he, additiveBoxDifference_sum]
  have hm (d : Fin n →₀ ℕ) :
      additiveBoxDifference n (fun x (_ : Unit) => P.coeff d * ∏ i, x i ^ d i) u v () =
        P.coeff d * ∏ i, (u i ^ d i - v i ^ d i) :=
    additiveBoxDifference_product n (fun _ : Unit => P.coeff d) (fun i x => x ^ d i) u v ()
  simp_rw [hm]
  rw [Finset.sum_eq_single (fullShiftExponent n)]
  · simp only [fullShiftExponent_apply, pow_one]
  · intro d hd hne
    obtain ⟨i, hi⟩ := (exponent_eq_full_or_missing d ((le_totalDegree hd).trans hP)).resolve_left hne
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp only [hi, pow_zero, sub_self]), mul_zero]
  · intro hnot
    rw [notMem_support_iff.mp hnot, zero_mul]

theorem full_coefficient_eq_mixed_difference_of_totalDegree {R : Type*} [CommRing R] {n : ℕ}
    (P : MvPolynomial (Fin n) R) (hP : P.totalDegree ≤ n) :
    P.coeff (fullShiftExponent n) =
      additiveBoxDifference n (fun x (_ : Unit) => eval x P) (fun _ => 1) (fun _ => 0) () := by
  rw [full_mixed_difference_of_totalDegree P hP]
  simp

theorem mixed_difference_eq_zero_of_totalDegree_lt {R : Type*} [CommRing R] {n : ℕ}
    (P : MvPolynomial (Fin n) R) (hP : P.totalDegree < n) (u v : Fin n → R) :
    additiveBoxDifference n (fun x (_ : Unit) => eval x P) u v () = 0 := by
  have hz : P.coeff (fullShiftExponent n) = 0 := by
    apply coeff_eq_zero_of_totalDegree_lt
    change P.totalDegree < (fullShiftExponent n).sum (fun _ e => e)
    rwa [fullShiftExponent_sum]
  rw [full_mixed_difference_of_totalDegree P hP.le, hz, zero_mul]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def diagonalMultiaffineScaling {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (s : Fin n → ℝ) : MvPolynomial (Fin n) ℝ :=
  subsetPolynomial (fun S => P.coeff (SquarefreeIndex.ofFinset S).val * ∏ i ∈ S, s i)

theorem diagonalMultiaffineScaling_degree {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (s : Fin n → ℝ) (i : Fin n) : (diagonalMultiaffineScaling P s).degreeOf i ≤ 1 :=
  subsetPolynomial_degree _ _

theorem diagonalMultiaffineScaling_top {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (s : Fin n → ℝ) :
    (diagonalMultiaffineScaling P s).coeff
      (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin n))).val =
      P.coeff (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin n))).val * ∏ i, s i := by
  exact subsetPolynomial_coefficient _ _

theorem diagonalMultiaffineScaling_eval {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (hP : ∀ i, P.degreeOf i ≤ 1) (s x : Fin n → ℝ) :
    MvPolynomial.eval x (diagonalMultiaffineScaling P s) =
      MvPolynomial.eval (fun i => s i*x i) P := by
  rw [diagonalMultiaffineScaling, subsetPolynomial_eval, multiaffinePolynomial_eval P hP]
  unfold multiaffineExpansion
  simp only [Finset.prod_ite_mem_eq]
  apply Finset.sum_congr rfl
  intro S _
  rw [Finset.prod_mul_distrib]
  ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical
open CircleFourier

theorem fullSquarefreeExponent_map_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) :
    (SquarefreeIndex.ofFinset (Finset.univ : Finset ι)).val.mapDomain e =
      (SquarefreeIndex.ofFinset (Finset.univ : Finset κ)).val := by
  ext j
  obtain ⟨i,rfl⟩ := e.surjective j
  rw [Finsupp.mapDomain_apply_of_injective e.injective]
  simp [SquarefreeIndex.ofFinset_apply]

theorem fin_multiaffine_polynomial_bias {n : ℕ} (P : MvPolynomial (Fin (n+1)) ℝ)
    (hP : ∀ i, P.degreeOf i ≤ 1) (N : Fin (n+1) → ℕ) (u : Fin (n+1) → ℝ)
    {ζ : ℝ} (hζ : 0 < ζ) (hN : ∀ i, multiaffineBiasBudget n ζ ≤ N i)
    (hbias : ζ ≤ ‖𝔼 x : ∀ i, Fin (N i),
      character ((MvPolynomial.eval (fun i => u i+((x i).val : ℝ)) P : ℝ) : CircleFourier.Circle)‖) :
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ multiaffineBiasBudget n ζ ∧
      ∃ m : ℤ, |P.coeff (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin (n+1)))).val-
        (m : ℝ)/q| ≤ multiaffineBiasBudget n ζ / ∏ i, (N i : ℝ) := by
  let e := _root_.finSuccEquiv n
  let Q := MvPolynomial.rename e P
  have hQ : ∀ j, Q.degreeOf j ≤ 1 := by
    intro j
    obtain ⟨i,rfl⟩ := e.surjective j
    rw [MvPolynomial.degreeOf_rename_of_injective e.injective]
    exact hP i
  have heval (x : ∀ i : Fin n, Fin (N i.succ)) (t : Fin (N 0)) :
      MvPolynomial.eval
        (fun j => Option.elim j (u 0+(t.val : ℝ)) (fun i => u i.succ+((x i).val : ℝ))) Q =
      MvPolynomial.eval
        (fun i => u i+(((Fin.cons t x : ∀ j : Fin (n+1), Fin (N j)) i).val : ℝ)) P := by
    rw [MvPolynomial.eval_rename]
    apply congrArg (fun z : Fin (n+1) → ℝ => MvPolynomial.eval z P)
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [e]
    · simp [e]
  rw [expect_dependent_fin_cons, Finset.expect_comm] at hbias
  simp_rw [← heval] at hbias
  have h := multiaffine_polynomial_bias Q hQ (fun i => N i.succ) (N 0)
    (fun i => u i.succ) (u 0) hζ (fun i => hN i.succ) (hN 0) hbias
  have hcoeff : Q.coeff (SquarefreeIndex.ofFinset (Finset.univ : Finset (Option (Fin n)))).val =
      P.coeff (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin (n+1)))).val := by
    rw [← fullSquarefreeExponent_map_equiv e, MvPolynomial.coeff_rename_mapDomain e e.injective]
  simpa only [hcoeff, Fin.prod_univ_succ] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical
open CircleFourier

theorem booleanBlockPhase_selected_entry {n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (N : Fin (n+1) → Option α → ℕ) (u : Fin (n+1) → Option α → ℝ)
    (ξ : Finset α → ℝ) (label : Fin (n+1) → Option α) (S : Finset α)
    (hlabel : ∀ a, (∃ i, label i = some a) ↔ a ∈ S)
    (hNpos : ∀ g r, 0 < N g r) {ζ : ℝ} (hζ : 0 < ζ)
    (hN : ∀ g, multiaffineBiasBudget n ζ ≤ N g (label g))
    (hbias : ζ ≤ ‖𝔼 x : ∀ g r, Fin (N g r),
      character ((booleanBlockPhase ξ (fun g r => u g r+((x g r).val : ℝ)) : ℝ) :
        CircleFourier.Circle)‖) :
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ multiaffineBiasBudget n ζ ∧
      ∃ m : ℤ, |ξ S-(m : ℝ)/q| ≤
        multiaffineBiasBudget n ζ / ∏ g, (N g (label g) : ℝ) := by
  let : ∀ g r, Nonempty (Fin (N g r)) := fun g r => ⟨⟨0,hNpos g r⟩⟩
  let F := fun x : ∀ g r, Fin (N g r) =>
    character ((booleanBlockPhase ξ (fun g r => u g r+((x g r).val : ℝ)) : ℝ) :
      CircleFourier.Circle)
  obtain ⟨c,hc⟩ := exists_frozen_group_bias label F hbias
  let b := fun g r => u g r+((c g r).val : ℝ)
  let P := frozenBooleanPhasePolynomial label b ξ
  have hphase (t : ∀ g, Fin (N g (label g))) :
      F (resampleGroupCoordinates label c t) =
        character ((MvPolynomial.eval (fun g => u g (label g)+((t g).val : ℝ)) P : ℝ) :
          CircleFourier.Circle) := by
    dsimp only [F,P]
    rw [frozenBooleanPhasePolynomial_eval]
    dsimp only [b]
    rw [intervalCoordinates_resample]
  simp_rw [hphase] at hc
  have h := fin_multiaffine_polynomial_bias P (frozenBooleanPhasePolynomial_degree label b ξ)
    (fun g => N g (label g)) (fun g => u g (label g)) hζ hN hc
  simpa only [P, frozenBooleanPhasePolynomial_coefficient (n+1) label b ξ S hlabel] using h

theorem booleanBlockPhase_entry_approximation {n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (N : Fin (n+1) → ℕ) (u : Fin (n+1) → Option α → ℝ) (ξ : Finset α → ℝ)
    (S : Finset α) (hS : S.card ≤ n+1) {ζ : ℝ} (hζ : 0 < ζ)
    (hN : ∀ g, multiaffineBiasBudget n ζ ≤ N g)
    (hbias : ζ ≤ ‖𝔼 x : ∀ g, Option α → Fin (N g),
      character ((booleanBlockPhase ξ (fun g r => u g r+((x g r).val : ℝ)) : ℝ) :
        CircleFourier.Circle)‖) :
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ multiaffineBiasBudget n ζ ∧
      ∃ m : ℤ, |ξ S-(m : ℝ)/q| ≤ multiaffineBiasBudget n ζ / ∏ g, (N g : ℝ) := by
  obtain ⟨label,hlabel⟩ := exists_padded_boolean_labels S (n+1) hS
  have hNp : ∀ g, 0 < N g := fun g => by
    exact_mod_cast (multiaffineBiasBudget_pos n hζ).trans_le (hN g)
  exact booleanBlockPhase_selected_entry (fun g _ => N g) u ξ label S hlabel
    (fun g _ => hNp g) hζ hN hbias

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical
open CircleFourier

theorem fin_multiaffine_strided_bias {n : ℕ} (P : MvPolynomial (Fin (n+1)) ℝ)
    (hP : ∀ i, P.degreeOf i ≤ 1) (N s : Fin (n+1) → ℕ) (hs : ∀ i, 0 < s i)
    (u : Fin (n+1) → ℝ) {ζ : ℝ} (hζ : 0 < ζ)
    (hN : ∀ i, multiaffineBiasBudget n ζ ≤ N i)
    (hbias : ζ ≤ ‖𝔼 x : ∀ i, Fin (N i),
      character ((MvPolynomial.eval (fun i => u i+(s i : ℝ)*((x i).val : ℝ)) P : ℝ) :
        CircleFourier.Circle)‖) :
    ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ multiaffineBiasBudget n ζ * ∏ i, (s i : ℝ) ∧
      ∃ m : ℤ, |P.coeff (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin (n+1)))).val-
        (m : ℝ)/D| ≤ multiaffineBiasBudget n ζ / ∏ i, ((s i : ℝ)*(N i : ℝ)) := by
  let A := diagonalMultiaffineScaling P (fun i => (s i : ℝ))
  have hsr : ∀ i, (0 : ℝ) < s i := fun i => by exact_mod_cast hs i
  have heval (x : ∀ i, Fin (N i)) :
      MvPolynomial.eval (fun i => u i/(s i : ℝ)+((x i).val : ℝ)) A =
      MvPolynomial.eval (fun i => u i+(s i : ℝ)*((x i).val : ℝ)) P := by
    rw [diagonalMultiaffineScaling_eval P hP]
    apply congrArg (fun z : Fin (n+1) → ℝ => MvPolynomial.eval z P)
    funext i
    rw [mul_add, mul_div_cancel₀ _ (hsr i).ne']
  obtain ⟨q,hq,hqQ,m,hm⟩ := fin_multiaffine_polynomial_bias A
    (diagonalMultiaffineScaling_degree P _) N (fun i => u i/(s i : ℝ)) hζ hN
    (by simpa only [heval] using hbias)
  let S := ∏ i, s i
  have hSp : 0 < S := Finset.prod_pos (fun i _ => hs i)
  have hSr : (0 : ℝ) < S := by exact_mod_cast hSp
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have happrox : |P.coeff (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin (n+1)))).val*
      (S : ℝ)-(m : ℝ)/q| ≤ multiaffineBiasBudget n ζ / ∏ i, (N i : ℝ) := by
    simpa only [A, diagonalMultiaffineScaling_top, S, Nat.cast_prod] using hm
  refine ⟨q*S,Nat.mul_pos hq hSp,?_,m,?_⟩
  · simpa only [Nat.cast_mul, S, Nat.cast_prod] using mul_le_mul_of_nonneg_right hqQ hSr.le
  · have he : P.coeff (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin (n+1)))).val-
        (m : ℝ)/(q*S : ℕ) =
        (P.coeff (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin (n+1)))).val*
          (S : ℝ)-(m : ℝ)/q)/S := by
      push_cast
      field_simp
    rw [he, abs_div, abs_of_pos hSr]
    apply (div_le_div_of_nonneg_right happrox hSr.le).trans_eq
    rw [div_div, Finset.prod_mul_distrib]
    simp only [S, Nat.cast_prod]
    congr 1
    ring

end Erdos3

end

section

namespace Erdos3

open CircleFourier
open scoped BigOperators Classical

theorem multilinear_slice_bias_approximation {M : Type*} [AddCommGroup M] [Module ℝ M]
    {n : ℕ} (F : MultilinearMap ℝ (fun _ : Fin (n + 1) => M) ℝ)
    (b w : Fin (n + 1) → M) (N s : Fin (n + 1) → ℕ)
    (hs : ∀ i, 0 < s i) (u : Fin (n + 1) → ℝ) {ζ : ℝ} (hζ : 0 < ζ)
    (hN : ∀ i, multiaffineBiasBudget n ζ ≤ N i)
    (hbias : ζ ≤ ‖𝔼 x : ∀ i, Fin (N i),
      character ((F (fun i => b i + (u i + (s i : ℝ) * ((x i).val : ℝ)) • w i) : ℝ) :
        CircleFourier.Circle)‖) :
    ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ multiaffineBiasBudget n ζ * ∏ i, (s i : ℝ) ∧
      ∃ m : ℤ, |F w - (m : ℝ) / D| ≤
        multiaffineBiasBudget n ζ / ∏ i, ((s i : ℝ) * (N i : ℝ)) := by
  have hb : ζ ≤ ‖𝔼 x : ∀ i, Fin (N i),
      character ((MvPolynomial.eval (fun i => u i + (s i : ℝ) * ((x i).val : ℝ))
        (multilinearSlicePolynomial F b w) : ℝ) : CircleFourier.Circle)‖ := by
    simpa only [multilinearSlicePolynomial_eval] using hbias
  have h := fin_multiaffine_strided_bias (multilinearSlicePolynomial F b w)
    (multilinearSlicePolynomial_degree F b w) N s hs u hζ hN hb
  simpa only [multilinearSlicePolynomial_top] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical
open CircleFourier

theorem booleanBlockPhase_strided_selected_entry {n : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α]
    (N s : Fin (n+1) → Option α → ℕ) (u : Fin (n+1) → Option α → ℝ)
    (ξ : Finset α → ℝ) (label : Fin (n+1) → Option α) (S : Finset α)
    (hlabel : ∀ a, (∃ i, label i = some a) ↔ a ∈ S)
    (hNpos : ∀ g r, 0 < N g r) (hs : ∀ g, 0 < s g (label g))
    {ζ : ℝ} (hζ : 0 < ζ) (hN : ∀ g, multiaffineBiasBudget n ζ ≤ N g (label g))
    (hbias : ζ ≤ ‖𝔼 x : ∀ g r, Fin (N g r),
      character ((booleanBlockPhase ξ (fun g r => u g r+(s g r : ℝ)*((x g r).val : ℝ)) : ℝ) :
        CircleFourier.Circle)‖) :
    ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ multiaffineBiasBudget n ζ * ∏ g, (s g (label g) : ℝ) ∧
      ∃ m : ℤ, |ξ S-(m : ℝ)/D| ≤ multiaffineBiasBudget n ζ /
        ∏ g, ((s g (label g) : ℝ)*(N g (label g) : ℝ)) := by
  let : ∀ g r, Nonempty (Fin (N g r)) := fun g r => ⟨⟨0,hNpos g r⟩⟩
  let F := fun x : ∀ g r, Fin (N g r) =>
    character ((booleanBlockPhase ξ (fun g r => u g r+(s g r : ℝ)*((x g r).val : ℝ)) : ℝ) :
      CircleFourier.Circle)
  obtain ⟨c,hc⟩ := exists_frozen_group_bias label F hbias
  let b := fun g r => u g r+(s g r : ℝ)*((c g r).val : ℝ)
  let P := frozenBooleanPhasePolynomial label b ξ
  have hphase (t : ∀ g, Fin (N g (label g))) :
      F (resampleGroupCoordinates label c t) =
        character ((MvPolynomial.eval
          (fun g => u g (label g)+(s g (label g) : ℝ)*((t g).val : ℝ)) P : ℝ) :
          CircleFourier.Circle) := by
    dsimp only [F,P]
    rw [frozenBooleanPhasePolynomial_eval]
    dsimp only [b]
    rw [progressionCoordinates_resample]
  simp_rw [hphase] at hc
  have h := fin_multiaffine_strided_bias P (frozenBooleanPhasePolynomial_degree label b ξ)
    (fun g => N g (label g)) (fun g => s g (label g)) hs (fun g => u g (label g)) hζ hN hc
  simpa only [P, frozenBooleanPhasePolynomial_coefficient (n+1) label b ξ S hlabel] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem stride_product_le {I : Type*} [Fintype I] (s : I → ℕ) {R : ℝ}
    (hs : ∀ i, (s i : ℝ) ≤ R) : (∏ i, (s i : ℝ)) ≤ R^Fintype.card I := by
  calc
    _ ≤ ∏ _i : I, R := Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _) (fun i _ => hs i)
    _ = _ := by simp

theorem stride_product_error_le {I : Type*} [Fintype I] (N s : I → ℕ)
    (hN : ∀ i, 0 < N i) (hs : ∀ i, 0 < s i) {C A : ℝ} (hC : 0 < C) (hA : 0 ≤ A) :
    A/(C*∏ i, ((s i : ℝ)*(N i : ℝ))) ≤ A/(C*∏ i, (N i : ℝ)) := by
  have hp : (0 : ℝ) < ∏ i, (N i : ℝ) :=
    Finset.prod_pos (fun i _ => by exact_mod_cast hN i)
  apply div_le_div_of_nonneg_left hA (mul_pos hC hp)
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _)
  intro i _
  have hsi : (1 : ℝ) ≤ s i := by exact_mod_cast hs i
  exact le_mul_of_one_le_left (Nat.cast_nonneg _) hsi

end Erdos3

end

end OAI
