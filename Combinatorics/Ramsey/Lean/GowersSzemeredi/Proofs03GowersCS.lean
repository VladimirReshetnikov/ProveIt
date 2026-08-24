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

private lemma gcs_countWhere_eq_sum_ite {X : Type*} [Fintype X]
    (P : X → Prop) :
    countWhere P = ∑ x : X,
      @ite Nat (P x) (Classical.propDecidable (P x)) 1 0 := by
  classical
  unfold countWhere
  simp

private lemma gcs_boolWeight_insertNth {n : Nat}
    (j : Fin (n + 1)) (b : Bool) (e : Fin n → Bool) :
    boolWeight (j.insertNth b e) = (if b then 1 else 0) + boolWeight e := by
  classical
  unfold boolWeight
  rw [gcs_countWhere_eq_sum_ite, gcs_countWhere_eq_sum_ite]
  let ind : Bool → Nat := fun c => if c then 1 else 0
  have hind (c : Bool) :
      @ite Nat (c = true) (Classical.propDecidable (c = true)) 1 0 = ind c := by
    cases c <;> simp [ind]
  have hfun :
      (fun i : Fin (n + 1) =>
        ind ((j.insertNth b e : Fin (n + 1) → Bool) i)) =
        j.insertNth (ind b) (fun i : Fin n => ind (e i)) := by
    rw [Fin.eq_insertNth_iff]
    constructor
    · simp
    · funext i
      simp [Fin.removeNth_apply]
  calc
    (∑ i : Fin (n + 1),
        @ite Nat ((j.insertNth b e : Fin (n + 1) → Bool) i = true)
          (Classical.propDecidable _) 1 0) =
        ∑ i : Fin (n + 1),
          ind ((j.insertNth b e : Fin (n + 1) → Bool) i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact hind _
    _ = ∑ i : Fin (n + 1),
          (j.insertNth (ind b) (fun i : Fin n => ind (e i))) i := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrFun hfun i
    _ = ind b + ∑ i : Fin n, ind (e i) := Fin.sum_insertNth j _ _
    _ = (if b then 1 else 0) + ∑ i : Fin n, ind (e i) := by rfl
    _ = (if b then 1 else 0) +
        ∑ i : Fin n,
          @ite Nat (e i = true) (Classical.propDecidable _) 1 0 := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact (hind _).symm

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
  have hfun :
      (fun i : Fin (n + 1) =>
        if (j.insertNth b e : Fin (n + 1) → Bool) i then
          (j.insertNth r a : Point N (n + 1)) i else 0) =
        j.insertNth (if b then r else 0)
          (fun i : Fin n => if e i then a i else 0) := by
    rw [Fin.eq_insertNth_iff]
    constructor
    · simp
    · funext i
      simp [Fin.removeNth_apply]
  unfold cubeArgument
  rw [show (∑ i : Fin (n + 1),
      if (j.insertNth b e : Fin (n + 1) → Bool) i then
        (j.insertNth r a : Point N (n + 1)) i else 0) =
      ∑ i : Fin (n + 1),
        (j.insertNth (if b then r else 0)
          (fun i : Fin n => if e i then a i else 0)) i by
    apply Finset.sum_congr rfl
    intro i _
    exact congrFun hfun i]
  rw [Fin.sum_insertNth]
  abel

/-- Product on one face of a cube after deleting coordinate `j`. -/
private def gcsHalf {N n : Nat}
    (f : (Fin (n + 1) → Bool) → ZMod N → Complex)
    (j : Fin (n + 1)) (b : Bool) (a : Point N n) (s : ZMod N) : Complex :=
  ∏ e : Fin n → Bool,
    parityConj e
      (f (j.insertNth b e) (s - ∑ i, if e i then a i else 0))

private lemma gcs_cubeProduct_split {N n : Nat}
    (f : (Fin (n + 1) → Bool) → ZMod N → Complex)
    (j : Fin (n + 1)) (r : ZMod N) (a : Point N n) (s : ZMod N) :
    (∏ e : Fin (n + 1) → Bool,
      parityConj e (f e (cubeArgument s (j.insertNth r a) e))) =
      gcsHalf f j false a s * star (gcsHalf f j true a (s - r)) := by
  let T : (Fin (n + 1) → Bool) → Complex := fun e =>
    parityConj e (f e (cubeArgument s (j.insertNth r a) e))
  calc
    (∏ e : Fin (n + 1) → Bool,
      parityConj e (f e (cubeArgument s (j.insertNth r a) e))) =
        ∏ be : Bool × (Fin n → Bool), T (j.insertNth be.1 be.2) := by
      exact Fintype.prod_equiv
        (Fin.insertNthEquiv (fun _ : Fin (n + 1) => Bool) j).symm
        T (fun be => T (j.insertNth be.1 be.2)) (fun e =>
          congrArg T
            ((Fin.insertNthEquiv (fun _ : Fin (n + 1) => Bool) j).apply_symm_apply e).symm)
    _ = (∏ e : Fin n → Bool, T (j.insertNth true e)) *
        ∏ e : Fin n → Bool, T (j.insertNth false e) := by
      rw [Fintype.prod_prod_type, Fintype.prod_bool]
    _ = star (gcsHalf f j true a (s - r)) * gcsHalf f j false a s := by
      congr 1
      · rw [gcsHalf, star_prod]
        apply Finset.prod_congr rfl
        intro e _
        simp only [T]
        rw [gcs_cubeArgument_insertNth]
        simp only [if_true]
        rw [gcs_parityConj_insert_true]
      · rw [gcsHalf]
        apply Finset.prod_congr rfl
        intro e _
        simp only [T]
        rw [gcs_cubeArgument_insertNth]
        simp only [Bool.false_eq_true, if_false, sub_zero]
        rw [gcs_parityConj_insert_false]
    _ = gcsHalf f j false a s * star (gcsHalf f j true a (s - r)) :=
      mul_comm _ _

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
  let Q : Point N (n + 1) → Complex := fun x =>
    ∑ s : ZMod N,
      ∏ e : Fin (n + 1) → Bool,
        parityConj e (f e (cubeArgument s x e))
  calc
    cubeForm f = ∑ x : Point N (n + 1), Q x := by rfl
    _ = ∑ p : ZMod N × Point N n, Q (j.insertNth p.1 p.2) := by
      exact Fintype.sum_equiv
        (Fin.insertNthEquiv (fun _ : Fin (n + 1) => ZMod N) j).symm
        Q (fun p => Q (j.insertNth p.1 p.2)) (fun x =>
          congrArg Q
            ((Fin.insertNthEquiv (fun _ : Fin (n + 1) => ZMod N) j).apply_symm_apply x).symm)
    _ = ∑ r : ZMod N, ∑ a : Point N n,
        ∑ s : ZMod N,
          ∏ e : Fin (n + 1) → Bool,
            parityConj e
              (f e (cubeArgument s (j.insertNth r a) e)) := by
      rw [Fintype.sum_prod_type]
    _ = ∑ a : Point N n, ∑ r : ZMod N, ∑ s : ZMod N,
        gcsHalf f j false a s * star (gcsHalf f j true a (s - r)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro s _
      exact gcs_cubeProduct_split f j r a s
    _ = ∑ a : Point N n,
        (∑ s : ZMod N, gcsHalf f j false a s) *
          star (∑ t : ZMod N, gcsHalf f j true a t) := by
      apply Finset.sum_congr rfl
      intro a _
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

/-- One coordinate of the Gowers--Cauchy--Schwarz iteration. -/
private lemma cubeForm_oneCoordinate_sq_le {N n : Nat} [NeZero N]
    (f : (Fin (n + 1) → Bool) → ZMod N → Complex)
    (j : Fin (n + 1)) :
    ‖cubeForm f‖ ^ 2 ≤
      ‖cubeForm (duplicateCoordinate f j false)‖ *
        ‖cubeForm (duplicateCoordinate f j true)‖ := by
  let A : Point N n → Complex := fun a =>
    ∑ s : ZMod N, gcsHalf f j false a s
  let B : Point N n → Complex := fun a =>
    ∑ s : ZMod N, gcsHalf f j true a s
  have hform : cubeForm f = ∑ a : Point N n, A a * star (B a) := by
    simpa [A, B] using cubeForm_eq_halfInner f j
  have htriangle : ‖cubeForm f‖ ≤ ∑ a : Point N n, ‖A a‖ * ‖B a‖ := by
    rw [hform]
    calc
      ‖∑ a : Point N n, A a * star (B a)‖ ≤
          ∑ a : Point N n, ‖A a * star (B a)‖ := norm_sum_le _ _
      _ = ∑ a : Point N n, ‖A a‖ * ‖B a‖ := by
        apply Finset.sum_congr rfl
        intro a _
        rw [norm_mul, norm_star]
  have hcs : (∑ a : Point N n, ‖A a‖ * ‖B a‖) ^ 2 ≤
      (∑ a : Point N n, ‖A a‖ ^ 2) *
        ∑ a : Point N n, ‖B a‖ ^ 2 := by
    simpa using sum_mul_sq_le_sq_mul_sq
      (Finset.univ : Finset (Point N n)) (fun a => ‖A a‖) (fun a => ‖B a‖)
  calc
    ‖cubeForm f‖ ^ 2 ≤ (∑ a : Point N n, ‖A a‖ * ‖B a‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) htriangle 2
    _ ≤ (∑ a : Point N n, ‖A a‖ ^ 2) *
        ∑ a : Point N n, ‖B a‖ ^ 2 := hcs
    _ = ‖cubeForm (duplicateCoordinate f j false)‖ *
        ‖cubeForm (duplicateCoordinate f j true)‖ := by
      rw [norm_cubeForm_duplicateCoordinate, norm_cubeForm_duplicateCoordinate]
      simp only [A, B, gcsFaceEnergy]

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
      have hdup (b : Bool) :
          duplicateAt f j b = duplicateCoordinate f j b := by
        funext e s
        simp only [duplicateAt, duplicateCoordinate, Fin.insertNth_removeNth]
      rw [hdup false, hdup true]
      exact cubeForm_oneCoordinate_sq_le f j

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
    · have hi' : i.val < n + 1 := by omega
      have hij : i = (⟨n, hn⟩ : Fin d) := Fin.ext hin
      simp [overwritePrefix, hij, Fin.snoc]
    · have hi' : ¬i.val < n + 1 := by omega
      have hij : i ≠ (⟨n, hn⟩ : Fin d) := by
        intro h
        apply hin
        exact Fin.ext_iff.mp h
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
  unfold prefixProduct
  rw [← Finset.prod_pow]
  calc
    (∏ q : Fin n → Bool, ‖cubeForm (prefixFamily f n q)‖ ^ 2) ≤
        ∏ q : Fin n → Bool,
          (‖cubeForm (duplicateAt (prefixFamily f n q)
              (⟨n, hn⟩ : Fin d) false)‖ *
            ‖cubeForm (duplicateAt (prefixFamily f n q)
              (⟨n, hn⟩ : Fin d) true)‖) := by
      apply Finset.prod_le_prod
      · intro q _
        exact sq_nonneg _
      · intro q _
        exact cubeForm_oneCoordinate_sq_le' (prefixFamily f n q) ⟨n, hn⟩
    _ = ∏ q : Fin n → Bool,
          (‖cubeForm (prefixFamily f (n + 1) (Fin.snoc q false))‖ *
            ‖cubeForm (prefixFamily f (n + 1) (Fin.snoc q true))‖) := by
      apply Finset.prod_congr rfl
      intro q _
      rw [duplicate_prefixFamily, duplicate_prefixFamily]
    _ = (∏ q : Fin n → Bool,
          ‖cubeForm (prefixFamily f (n + 1) (Fin.snoc q false))‖) *
        ∏ q : Fin n → Bool,
          ‖cubeForm (prefixFamily f (n + 1) (Fin.snoc q true))‖ := by
      rw [Finset.prod_mul_distrib]
    _ = ∏ r : Fin (n + 1) → Bool,
          ‖cubeForm (prefixFamily f (n + 1) r)‖ := by
      let T : (Fin (n + 1) → Bool) → Real := fun r =>
        ‖cubeForm (prefixFamily f (n + 1) r)‖
      symm
      calc
        (∏ r : Fin (n + 1) → Bool, T r) =
            ∏ p : Bool × (Fin n → Bool), T (Fin.snoc p.2 p.1) := by
          exact Fintype.prod_equiv
            (Fin.snocEquiv (fun _ : Fin (n + 1) => Bool)).symm
            T (fun p => T (Fin.snoc p.2 p.1)) (fun r =>
              congrArg T
                ((Fin.snocEquiv (fun _ : Fin (n + 1) => Bool)).apply_symm_apply r).symm)
        _ = (∏ q : Fin n → Bool, T (Fin.snoc q true)) *
            ∏ q : Fin n → Bool, T (Fin.snoc q false) := by
          rw [Fintype.prod_prod_type, Fintype.prod_bool]
        _ = (∏ q : Fin n → Bool, T (Fin.snoc q false)) *
            ∏ q : Fin n → Bool, T (Fin.snoc q true) := mul_comm _ _

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
    prefixFamily f 0 q = f := by
  funext e s
  apply congrArg (fun v => f v s)
  funext i
  simp [overwritePrefix]

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
  let G : (Fin d → Bool) → Real := fun e =>
    ‖cubeForm (d := d) (fun (_ : Fin d → Bool) => f e)‖
  let R : Real := ∏ e : Fin d → Bool, G e
  let m : Nat := (2 : Nat) ^ d
  have hG (e : Fin d → Bool) : 0 ≤ G e := norm_nonneg _
  have hR : 0 ≤ R := Finset.prod_nonneg fun e _ => hG e
  have hm : m ≠ 0 := by positivity
  have hmpos : 0 < (m : Real) := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hpower : ‖cubeForm f‖ ^ m ≤ R := by
    simpa only [m, R, G] using cubeForm_power_le_product f
  have hroot : ‖cubeForm f‖ ≤ R ^ (m : Real)⁻¹ := by
    apply (Real.le_rpow_inv_iff_of_pos (norm_nonneg _) hR hmpos).2
    simpa only [Real.rpow_natCast] using hpower
  calc
    ‖cubeForm f‖ ≤ R ^ (m : Real)⁻¹ := hroot
    _ = ∏ e : Fin d → Bool, G e ^ (m : Real)⁻¹ := by
      exact (Real.finsetProd_rpow Finset.univ G (fun e _ => hG e) _).symm
    _ = ∏ e : Fin d → Bool,
        ‖cubeForm (d := d) (fun (_ : Fin d → Bool) => f e)‖ ^
          ((1 : Real) / (2 : Real) ^ d) := by
      simp only [G, m, one_div, Nat.cast_pow, Nat.cast_ofNat]

/-- **Lemma 3.8 (Gowers--Cauchy--Schwarz).** -/
theorem lemma_3_8_holds : lemma_3_8 := by
  intro N d _ f _
  exact gowers_cauchy_schwarz f

end LeanProofs.GowersSzemeredi
