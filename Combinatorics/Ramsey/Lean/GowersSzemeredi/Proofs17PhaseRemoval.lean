import GowersSzemeredi.Proofs03GowersCS
import GowersSzemeredi.Proofs17Phase
import Mathlib.Analysis.MeanInequalities

/-!
# Global polynomial phase removal

This module develops Proposition 17.2, whose assembled form
`proposition_17_2_holds` is in `Proofs17PhaseRemovalSide`.  We apply Lemma 17.1
to the multiaffine frequency `(y,x) ↦ y * sigma x`, identify the resulting
phased cube form with the original Fourier energy, and then use Lemma 3.8 and
AM--GM to select one of the polynomial phases.

`fourier_norm_sq_eq_difference_sum`, `isMultilinear_mul_first_coordinate`,
`prop172PhasedFamily`, `prop172_constantCubeForm_norm`,
`prop172_cubeForm_phased`, `prop172_energy_expansion`, `prop172_parity_phased`,
`prop172_phasedCubeProduct`, `prop172_phased_discValued` and
`proposition_17_2_holds` are in `Proofs17PhaseRemovalSide`, outside the final
route. -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

attribute [simp] exponential_add

attribute [simp] star_exponential

attribute [simp] cor57_norm_exponential

/-- Squaring a Fourier coefficient introduces one more difference variable. -/
lemma prop172_fourier_sq {N : Nat} [NeZero N]
    (g : ZMod N → Complex) (r : ZMod N) :
    ((‖fourier g r‖ ^ 2 : Real) : Complex) =
      ∑ y : ZMod N, ∑ s : ZMod N,
        difference g y s * exponential (-(y * r)) := by
  simp only [fourier, ZMod.dft_apply, smul_eq_mul]
  calc
    ((‖∑ s : ZMod N, exponential (-(s * r)) * g s‖ ^ 2 : Real) : Complex) =
        (∑ s : ZMod N, exponential (-(s * r)) * g s) *
          star (∑ t : ZMod N, exponential (-(t * r)) * g t) := by
      rw [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow]
    _ = ∑ s : ZMod N, ∑ t : ZMod N,
        (exponential (-(s * r)) * g s) *
          (star (g t) * exponential (t * r)) := by
      simp only [star_sum, star_mul, star_exponential, neg_neg]
      simp_rw [Finset.sum_mul, Finset.mul_sum]
    _ = ∑ s : ZMod N, ∑ y : ZMod N,
        (exponential (-(s * r)) * g s) *
          (star (g (s - y)) * exponential ((s - y) * r)) := by
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [← (Equiv.subLeft s).sum_comp]
      rfl
    _ = ∑ y : ZMod N, ∑ s : ZMod N,
        difference g y s * exponential (-(y * r)) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun s _ => ?_
      have hphase :
          exponential (-(s * r)) * exponential ((s - y) * r) =
            exponential (-(y * r)) := by
        rw [← exponential_add]
        congr 1
        ring
      rw [← hphase]
      unfold difference
      ring

private def prop172Monomial {N k : Nat} (e : Fin k → Bool) (x : Point N k) :
    ZMod N := ∏ i, if e i then x i else 1

private lemma prop172Monomial_cons {N k : Nat} (b : Bool) (e : Fin k → Bool)
    (z : Point N (k + 1)) :
    prop172Monomial (Fin.cons b e) z =
      (if b then z 0 else 1) * prop172Monomial e (Fin.tail z) := by
  simp [prop172Monomial, Fin.prod_univ_succ, Fin.tail]

/-- Multiplying a multiaffine function by a new first coordinate remains
multiaffine. -/
lemma prop172_multilinear_cons {N k : Nat}
    (sigma : Point N k → ZMod N) (hsigma : IsMultilinear sigma) :
    IsMultilinear (fun z : Point N (k + 1) => z 0 * sigma (Fin.tail z)) := by
  obtain ⟨c, hc⟩ := hsigma
  let c' : (Fin (k + 1) → Bool) → ZMod N := fun e =>
    if e 0 then c (Fin.tail e) else 0
  refine ⟨c', fun z => ?_⟩
  let T : (Fin (k + 1) → Bool) → ZMod N := fun e =>
    c' e * prop172Monomial e z
  have htrue (e : Fin k → Bool) :
      T (Fin.cons true e) =
        z 0 * (c e * prop172Monomial e (Fin.tail z)) := by
    simp [T, c', prop172Monomial_cons]
    ring
  have hfalse (e : Fin k → Bool) : T (Fin.cons false e) = 0 := by
    simp [T, c']
  change z 0 * sigma (Fin.tail z) = ∑ e, T e
  calc
    z 0 * sigma (Fin.tail z) =
        z 0 * ∑ e : Fin k → Bool,
          c e * prop172Monomial e (Fin.tail z) := by
      rw [hc]
      rfl
    _ = ∑ e : Fin k → Bool, T (Fin.cons true e) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [htrue]
    _ = ∑ e : Fin k → Bool, T (Fin.cons true e) +
        ∑ e : Fin k → Bool, T (Fin.cons false e) := by
      simp [hfalse]
    _ = ∑ p : Bool × (Fin k → Bool), T (Fin.cons p.1 p.2) := by
      rw [Fintype.sum_prod_type, Fintype.sum_bool]
    _ = ∑ e : Fin (k + 1) → Bool, T e := (Fin.consEquiv (fun _ : Fin (k + 1) => Bool)).sum_comp T

lemma prop172_boolWeight_cons {n : Nat}
    (b : Bool) (e : Fin n → Bool) :
    boolWeight (Fin.cons b e) = (if b then 1 else 0) + boolWeight e := by
  unfold boolWeight
  simp_rw [gcs_countWhere_eq_sum_ite]
  rw [Fin.sum_univ_succ]
  cases b <;> simp
  all_goals
    convert (@Finset.sum_boole (Fin n) Nat inferInstance
      (fun i : Fin n => e i = true)
      (fun i => Classical.propDecidable (e i = true))
      (Finset.univ : Finset (Fin n))).symm using 1
    all_goals simp only [Nat.cast_id]
  all_goals congr

lemma prop172_parityConj_cons_false {n : Nat}
    (e : Fin n → Bool) (z : Complex) :
    parityConj (Fin.cons false e) z = parityConj e z := by
  unfold parityConj
  rw [prop172_boolWeight_cons]
  simp

lemma prop172_parityConj_cons_true {n : Nat}
    (e : Fin n → Bool) (z : Complex) :
    parityConj (Fin.cons true e) z = star (parityConj e z) := by
  unfold parityConj
  rw [prop172_boolWeight_cons]
  have heven : Even (1 + boolWeight e) ↔ ¬Even (boolWeight e) := by
    rw [add_comm, Nat.even_add_one]
  by_cases h : Even (boolWeight e) <;> simp [heven, h]

lemma prop172_cubeArgument_cons {N n : Nat}
    (s r : ZMod N) (a : Point N n) (b : Bool) (e : Fin n → Bool) :
    cubeArgument s (Fin.cons r a) (Fin.cons b e) =
      s - (if b then r else 0) - ∑ i, if e i then a i else 0 := by
  unfold cubeArgument
  rw [Fin.sum_univ_succ]
  simp
  abel

/-- Closed cube-product formula for an iterated difference. -/
lemma prop172_cubeDifference_product {N d : Nat}
    (f : ZMod N → Complex) (x : Point N d) (s : ZMod N) :
    cubeDifference f x s =
      ∏ e : Fin d → Bool, parityConj e (f (cubeArgument s x e)) := by
  induction d generalizing s with
  | zero =>
      simp [cubeDifference, iteratedDifference, parityConj, boolWeight,
        cubeArgument, countWhere]
  | succ n ih =>
      let r : ZMod N := x 0
      let a : Point N n := Fin.tail x
      have hx : x = Fin.cons r a := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i <;> rfl
      rw [hx, cubeDifference_cons]
      simp only [difference, ih]
      let T : (Fin (n + 1) → Bool) → Complex := fun e =>
        parityConj e (f (cubeArgument s (Fin.cons r a) e))
      calc
        (∏ e : Fin n → Bool,
              parityConj e (f (cubeArgument s a e))) *
            star (∏ e : Fin n → Bool,
              parityConj e (f (cubeArgument (s - r) a e))) =
            (∏ e : Fin n → Bool, T (Fin.cons false e)) *
              ∏ e : Fin n → Bool, T (Fin.cons true e) := by
          rw [star_prod]
          congr 1
          · apply Finset.prod_congr rfl
            intro e _
            simp only [T]
            rw [prop172_parityConj_cons_false, prop172_cubeArgument_cons]
            simp only [Bool.false_eq_true, if_false, sub_zero]
            rfl
          · apply Finset.prod_congr rfl
            intro e _
            simp only [T]
            rw [prop172_parityConj_cons_true, prop172_cubeArgument_cons]
            simp only [if_true]
            rfl
        _ = ∏ p : Bool × (Fin n → Bool), T (Fin.cons p.1 p.2) := by
          rw [Fintype.prod_prod_type, Fintype.prod_bool, mul_comm]
        _ = ∏ e : Fin (n + 1) → Bool, T e :=
          (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).prod_comp T

lemma prop172_exponential_sum {N : Nat} [NeZero N]
    {I : Type*} (S : Finset I) (a : I → ZMod N) :
    exponential (∑ i ∈ S, a i) = ∏ i ∈ S, exponential (a i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert x S hx ih =>
      simp [hx, ih]

/-- A constant family in the multilinear cube form is the usual iterated
difference sum. -/
theorem constant_cubeForm_eq_sum_cubeDifference {N d : Nat} [NeZero N]
    (g : ZMod N → Complex) :
    cubeForm (d := d) (fun (_ : Fin d → Bool) => g) =
      ∑ x : Point N d, ∑ s : ZMod N, cubeDifference g x s := by
  unfold cubeForm
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun s _ => ?_
  exact (prop172_cubeDifference_product g x s).symm

/-- A cube difference is the product of its parity-conjugated vertices. -/
theorem cubeDifference_eq_parity_product {N d : Nat}
    (f : ZMod N → Complex) (x : Point N d) (s : ZMod N) :
    cubeDifference f x s =
      ∏ e : Fin d → Bool, parityConj e (f (cubeArgument s x e)) := by
  exact prop172_cubeDifference_product f x s

end LeanProofs.GowersSzemeredi
