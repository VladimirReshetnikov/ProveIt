import GowersSzemeredi.Proofs03Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# The Gowers--Cauchy--Schwarz inequality

This module proves Lemma 3.8.  A single Cauchy--Schwarz step duplicates the
functions on one face of the cube.  Iterating that step over every coordinate
turns the original mixed cube form into the geometric mean of its constant
vertex forms.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

private lemma gcs_parityConj_insert_false {n : Nat}
    (j : Fin (n + 1)) (e : Fin n → Bool) (z : Complex) :
    parityConj (j.insertNth false e) z = parityConj e z := by
  unfold parityConj
  rw [gcs_boolWeight_insertNth]
  simp

private lemma gcs_parityConj_insert_true {n : Nat}
    (j : Fin (n + 1)) (e : Fin n → Bool) (z : Complex) :
    parityConj (j.insertNth true e) z = star (parityConj e z) := by
  unfold parityConj
  rw [gcs_boolWeight_insertNth]
  have heven : Even (1 + boolWeight e) ↔ ¬ Even (boolWeight e) := by
    rw [add_comm, Nat.even_add_one]
  by_cases h : Even (boolWeight e) <;> simp [heven, h]

private lemma gcs_cubeArgument_insertNth {N n : Nat}
    (j : Fin (n + 1)) (r : ZMod N) (a : Point N n)
    (s : ZMod N) (b : Bool) (e : Fin n → Bool) :
    cubeArgument s (j.insertNth r a) (j.insertNth b e) =
      s - (if b then r else 0) - ∑ i, if e i then a i else 0 := by
  rw [cubeArgument, Fin.sum_univ_succAbove _ j]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  abel

/-- Product on one face of a cube after deleting coordinate `j`. -/
private def gcsHalf {N n : Nat}
    (f : (Fin (n + 1) → Bool) → ZMod N → Complex)
    (j : Fin (n + 1)) (b : Bool) (a : Point N n) (s : ZMod N) : Complex :=
  ∏ e : Fin n → Bool,
    parityConj e
      (f (j.insertNth b e) (s - ∑ i, if e i then a i else 0))

private lemma gcs_mixedCorrelation {N : Nat} [NeZero N]
    (F G : ZMod N → Complex) :
    (∑ r : ZMod N, ∑ s : ZMod N, F s * star (G (s - r))) =
      (∑ s : ZMod N, F s) * star (∑ t : ZMod N, G t) := by
  calc
    (∑ r : ZMod N, ∑ s : ZMod N, F s * star (G (s - r))) =
        ∑ s : ZMod N, ∑ r : ZMod N, F s * star (G (s - r)) := by
      rw [Finset.sum_comm]
    _ = ∑ s : ZMod N, ∑ t : ZMod N, F s * star (G t) := by
      apply Finset.sum_congr rfl
      intro s _
      simpa [Equiv.subLeft_apply] using
        (Equiv.sum_comp (Equiv.subLeft s) (fun t => F s * star (G t)))
    _ = (∑ s : ZMod N, F s) * star (∑ t : ZMod N, G t) := by
      simp only [star_sum, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]

private lemma cubeForm_eq_halfInner {N n : Nat} [NeZero N]
    (f : (Fin (n + 1) → Bool) → ZMod N → Complex)
    (j : Fin (n + 1)) :
    cubeForm f =
      ∑ a : Point N n,
        (∑ s : ZMod N, gcsHalf f j false a s) *
          star (∑ t : ZMod N, gcsHalf f j true a t) := by
  -- split each vertex product by the value of coordinate `j`
  have key (a : Point N n) (r s : ZMod N) :
      ∏ e : Fin (n + 1) → Bool, parityConj e (f e (cubeArgument s (j.insertNth r a) e)) =
        gcsHalf f j false a s * star (gcsHalf f j true a (s - r)) := by
    rw [← (Fin.insertNthEquiv (fun _ => Bool) j).prod_comp, Fintype.prod_prod_type,
      Fintype.prod_bool, mul_comm]
    simp only [Fin.insertNthEquiv, Equiv.coe_fn_mk, gcs_cubeArgument_insertNth,
      gcs_parityConj_insert_true, gcs_parityConj_insert_false, gcsHalf, star_prod, if_true,
      Bool.false_eq_true, if_false, sub_zero]
  -- and split each point `x` into its coordinate `r = x j` and the remaining coordinates `a`
  rw [cubeForm, ← (Fin.insertNthEquiv (fun _ => ZMod N) j).sum_comp, Fintype.sum_prod_type,
    sum_comm]
  refine sum_congr rfl fun a _ => ?_
  simp only [Fin.insertNthEquiv, Equiv.coe_fn_mk, key]
  exact gcs_mixedCorrelation _ _

/-- Duplicate one face-function across both values of coordinate `j`. -/
private def duplicateCoordinate {N n : Nat}
    (f : (Fin (n + 1) → Bool) → ZMod N → Complex)
    (j : Fin (n + 1)) (b : Bool) :
    (Fin (n + 1) → Bool) → ZMod N → Complex :=
  fun e => f (j.insertNth b (j.removeNth e))

private lemma gcsHalf_duplicateCoordinate {N n : Nat}
    (f : (Fin (n + 1) → Bool) → ZMod N → Complex)
    (j : Fin (n + 1)) (b b' : Bool) (a : Point N n) (s : ZMod N) :
    gcsHalf (duplicateCoordinate f j b) j b' a s = gcsHalf f j b a s := by
  unfold gcsHalf duplicateCoordinate
  apply Finset.prod_congr rfl
  intro e _
  simp

/-- The nonnegative quadratic face energy produced by one CS step. -/
private def gcsFaceEnergy {N n : Nat} [NeZero N]
    (f : (Fin (n + 1) → Bool) → ZMod N → Complex)
    (j : Fin (n + 1)) (b : Bool) : Real :=
  ∑ a : Point N n, ‖∑ s : ZMod N, gcsHalf f j b a s‖ ^ 2

private lemma cubeForm_duplicateCoordinate_eq {N n : Nat} [NeZero N]
    (f : (Fin (n + 1) → Bool) → ZMod N → Complex)
    (j : Fin (n + 1)) (b : Bool) :
    cubeForm (duplicateCoordinate f j b) = (gcsFaceEnergy f j b : Complex) := by
  rw [cubeForm_eq_halfInner (duplicateCoordinate f j b) j]
  simp only [gcsHalf_duplicateCoordinate f j b false,
    gcsHalf_duplicateCoordinate f j b true]
  unfold gcsFaceEnergy
  calc
    (∑ a : Point N n,
        (∑ s : ZMod N, gcsHalf f j b a s) *
          star (∑ t : ZMod N, gcsHalf f j b a t)) =
        ∑ a : Point N n,
          ((‖∑ s : ZMod N, gcsHalf f j b a s‖ ^ 2 : Real) : Complex) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow]
    _ = ((∑ a : Point N n,
          ‖∑ s : ZMod N, gcsHalf f j b a s‖ ^ 2 : Real) : Complex) := by
      rw [Complex.ofReal_sum]

private lemma norm_cubeForm_duplicateCoordinate {N n : Nat} [NeZero N]
    (f : (Fin (n + 1) → Bool) → ZMod N → Complex)
    (j : Fin (n + 1)) (b : Bool) :
    ‖cubeForm (duplicateCoordinate f j b)‖ = gcsFaceEnergy f j b := by
  rw [cubeForm_duplicateCoordinate_eq, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Duplicate a face along an arbitrary coordinate. -/
private def duplicateAt {N d : Nat}
    (f : (Fin d → Bool) → ZMod N → Complex) (j : Fin d) (b : Bool) :
    (Fin d → Bool) → ZMod N → Complex :=
  fun e => f (Function.update e j b)

private lemma cubeForm_oneCoordinate_sq_le' {N d : Nat} [NeZero N]
    (f : (Fin d → Bool) → ZMod N → Complex) (j : Fin d) :
    ‖cubeForm f‖ ^ 2 ≤
      ‖cubeForm (duplicateAt f j false)‖ *
        ‖cubeForm (duplicateAt f j true)‖ := by
  cases d with
  | zero => exact Fin.elim0 j
  | succ n =>
      have hdup (b : Bool) : duplicateAt f j b = duplicateCoordinate f j b := by
        funext e s
        simp only [duplicateAt, duplicateCoordinate, Fin.insertNth_removeNth]
      -- one Gowers--Cauchy--Schwarz step: the triangle inequality, then Cauchy--Schwarz in `a`
      rw [hdup, hdup, norm_cubeForm_duplicateCoordinate, norm_cubeForm_duplicateCoordinate,
        gcsFaceEnergy, gcsFaceEnergy, cubeForm_eq_halfInner f j]
      refine le_trans ?_ (sum_mul_sq_le_sq_mul_sq univ (fun a => ‖∑ s, gcsHalf f j false a s‖)
        fun a => ‖∑ s, gcsHalf f j true a s‖)
      gcongr
      exact (norm_sum_le _ _).trans_eq (by simp only [norm_mul, norm_star])

/-- Overwrite the first `n` coordinates of a Boolean cube vertex. -/
private def overwritePrefix {d : Nat} (n : Nat) (q : Fin n → Bool)
    (e : Fin d → Bool) : Fin d → Bool := fun i =>
  if hi : i.val < n then q ⟨i.val, hi⟩ else e i

/-- The family obtained after fixing the first `n` face choices. -/
private def prefixFamily {N d : Nat}
    (f : (Fin d → Bool) → ZMod N → Complex) (n : Nat)
    (q : Fin n → Bool) : (Fin d → Bool) → ZMod N → Complex :=
  fun e => f (overwritePrefix n q e)

private lemma overwritePrefix_succ {d n : Nat} (hn : n < d)
    (q : Fin n → Bool) (b : Bool) (e : Fin d → Bool) :
    overwritePrefix n q
        (Function.update e (⟨n, hn⟩ : Fin d) b) =
      overwritePrefix (n + 1) (Fin.snoc q b) e := by
  funext i
  by_cases hi : i.val < n
  · have hi' : i.val < n + 1 := by omega
    simp [overwritePrefix, hi, hi', Fin.snoc]
  · by_cases hin : i.val = n
    · have _ : i.val < n + 1 := by omega
      have hij : i = (⟨n, hn⟩ : Fin d) := Fin.ext hin
      simp [overwritePrefix, hij, Fin.snoc]
    · have hi' : ¬i.val < n + 1 := by omega
      have hij : i ≠ (⟨n, hn⟩ : Fin d) := by
        exact fun h => hin (Fin.ext_iff.mp h)
      simp [overwritePrefix, hi, hi', hij]

private lemma duplicate_prefixFamily {N d n : Nat} (hn : n < d)
    (f : (Fin d → Bool) → ZMod N → Complex)
    (q : Fin n → Bool) (b : Bool) :
    duplicateAt (prefixFamily f n q) (⟨n, hn⟩ : Fin d) b =
      prefixFamily f (n + 1) (Fin.snoc q b) := by
  funext e s
  exact congrArg (fun v => f v s) (overwritePrefix_succ hn q b e)

/-- Product of all cube forms after the first `n` face choices are fixed. -/
private def prefixProduct {N d : Nat} [NeZero N]
    (f : (Fin d → Bool) → ZMod N → Complex) (n : Nat) : Real :=
  ∏ q : Fin n → Bool, ‖cubeForm (prefixFamily f n q)‖

private lemma prefixProduct_sq_le_succ {N d n : Nat} [NeZero N]
    (f : (Fin d → Bool) → ZMod N → Complex) (hn : n < d) :
    prefixProduct f n ^ 2 ≤ prefixProduct f (n + 1) := by
  -- split the `(n + 1)`-prefixes by their last face choice, then use one CS step per prefix
  rw [prefixProduct, prefixProduct, ← (Fin.snocEquiv fun _ => Bool).prod_comp,
    Fintype.prod_prod_type, Fintype.prod_bool, ← prod_mul_distrib, ← prod_pow]
  refine prod_le_prod (fun q _ => sq_nonneg _) fun q _ => ?_
  simp only [Fin.snocEquiv, Equiv.coe_fn_mk, ← duplicate_prefixFamily hn]
  exact (cubeForm_oneCoordinate_sq_le' _ _).trans_eq (mul_comm _ _)

private lemma prefixProduct_power_le {N d n : Nat} [NeZero N]
    (f : (Fin d → Bool) → ZMod N → Complex) (hn : n ≤ d) :
    prefixProduct f 0 ^ ((2 : Nat) ^ n) ≤ prefixProduct f n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hnd : n < d := Nat.lt_of_succ_le hn
      have hih := ih (Nat.le_of_lt hnd)
      have hbase : 0 ≤ prefixProduct f 0 := by
        unfold prefixProduct
        positivity
      calc
        prefixProduct f 0 ^ ((2 : Nat) ^ (n + 1)) =
            (prefixProduct f 0 ^ ((2 : Nat) ^ n)) ^ 2 := by
          rw [Nat.pow_succ, pow_mul]
        _ ≤ prefixProduct f n ^ 2 :=
          pow_le_pow_left₀ (pow_nonneg hbase _) hih 2
        _ ≤ prefixProduct f (n + 1) := prefixProduct_sq_le_succ f hnd

private lemma prefixFamily_zero {N d : Nat}
    (f : (Fin d → Bool) → ZMod N → Complex) (q : Fin 0 → Bool) :
    prefixFamily f 0 q = f := rfl

private lemma prefixProduct_zero {N d : Nat} [NeZero N]
    (f : (Fin d → Bool) → ZMod N → Complex) :
    prefixProduct f 0 = ‖cubeForm f‖ := by
  unfold prefixProduct
  simp only [prefixFamily_zero]
  simp

private lemma prefixFamily_full {N d : Nat}
    (f : (Fin d → Bool) → ZMod N → Complex) (q : Fin d → Bool) :
    prefixFamily f d q = fun _ => f q := by
  funext e s
  apply congrArg (fun v => f v s)
  funext i
  simp [overwritePrefix, i.isLt]

private lemma prefixProduct_full {N d : Nat} [NeZero N]
    (f : (Fin d → Bool) → ZMod N → Complex) :
    prefixProduct f d = ∏ e : Fin d → Bool,
      ‖cubeForm (d := d) (fun (_ : Fin d → Bool) => f e)‖ := by
  unfold prefixProduct
  apply Finset.prod_congr rfl
  intro e _
  rw [prefixFamily_full]

private lemma cubeForm_power_le_product {N d : Nat} [NeZero N]
    (f : (Fin d → Bool) → ZMod N → Complex) :
    ‖cubeForm f‖ ^ ((2 : Nat) ^ d) ≤
      ∏ e : Fin d → Bool,
        ‖cubeForm (d := d) (fun (_ : Fin d → Bool) => f e)‖ := by
  simpa only [prefixProduct_zero, prefixProduct_full] using
    prefixProduct_power_le f (le_refl d)

/-- The homogeneous form of Gowers--Cauchy--Schwarz.  The paper states the
result for disc-valued functions, but the proof does not use that bound. -/
theorem gowers_cauchy_schwarz {N d : Nat} [NeZero N]
    (f : (Fin d → Bool) → ZMod N → Complex) :
    ‖cubeForm f‖ ≤ ∏ e : Fin d → Bool,
      ‖cubeForm (d := d) (fun (_ : Fin d → Bool) => f e)‖ ^
        ((1 : Real) / (2 : Real) ^ d) := by
  -- take the `2 ^ d`-th root of `cubeForm_power_le_product`
  have hG : ∀ e ∈ (Finset.univ : Finset (Fin d → Bool)),
      0 ≤ ‖cubeForm (d := d) (fun (_ : Fin d → Bool) => f e)‖ := fun _ _ => norm_nonneg _
  have h := Real.le_rpow_inv_iff_of_pos (norm_nonneg (cubeForm f)) (Finset.prod_nonneg hG)
    (by positivity : (0 : Real) < ((2 ^ d : Nat) : Real))
  rw [Real.rpow_natCast, ← Real.finsetProd_rpow _ _ hG] at h
  simpa only [one_div, Nat.cast_pow, Nat.cast_ofNat] using h.2 (cubeForm_power_le_product f)

/-- **Lemma 3.8 (Gowers--Cauchy--Schwarz).** -/
theorem lemma_3_8_holds : lemma_3_8 := by
  intro N d _ f _
  exact gowers_cauchy_schwarz f

end LeanProofs.GowersSzemeredi
