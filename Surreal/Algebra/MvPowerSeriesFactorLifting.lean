import Surreal.Algebra.PolynomialFactorLinearization
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.MvPowerSeries.Inverse

/-!
# Coprime factor lifting with several formal parameters

This is the multivariate formal-parameter version of the coefficient recursion
`polynomial:eq:henselrecursion` toward `polynomial:thm:hensel` in
`docs/surcomplex/polynomial-algebra/article.tex`. The recursive corrections use
the already proved bounded Sylvester inverse. A nonlinear coefficient at a
multiindex only depends on strictly smaller total degrees. Each antidiagonal
is finite even without a finiteness assumption on the set of variables.

The result concerns formal power series. Evaluation at infinitesimal Hahn
series, support control, and lifting on the actual surreal field are separate.
-/

namespace Surreal.FinitePolynomial

open Polynomial

noncomputable section

variable {R σ : Type*} [CommRing R]

private def mvBoundedCorrectionProduct (p q : R[X])
    (h : degreeLT R p.natDegree) (k : degreeLT R q.natDegree) :
    degreeLT R (p.natDegree + q.natDegree) :=
  ⟨(h : R[X]) * (k : R[X]), mem_degreeLT.mpr (by
    by_cases hh : (h : R[X]) = 0
    · rw [hh, zero_mul, degree_zero]
      exact WithBot.bot_lt_coe _
    by_cases hk : (k : R[X]) = 0
    · rw [hk, mul_zero, degree_zero]
      exact WithBot.bot_lt_coe _
    have hd := (natDegree_lt_iff_degree_lt hh).mpr (mem_degreeLT.mp h.property)
    have kd := (natDegree_lt_iff_degree_lt hk).mpr (mem_degreeLT.mp k.property)
    exact degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr
      (natDegree_mul_le.trans_lt (Nat.add_lt_add hd kd))))⟩

/-- The finite pairs of nonzero multiindices adding to the prescribed index. -/
def mvFactorInterior (d : σ →₀ ℕ) : Finset ((σ →₀ ℕ) × (σ →₀ ℕ)) := by
  classical
  exact (Finset.antidiagonal d).filter fun b => b.1 ≠ 0 ∧ b.2 ≠ 0

theorem mem_mvFactorInterior {d : σ →₀ ℕ} {b : (σ →₀ ℕ) × (σ →₀ ℕ)} :
    b ∈ mvFactorInterior d ↔ b.1 + b.2 = d ∧ b.1 ≠ 0 ∧ b.2 ≠ 0 := by
  classical
  simp only [mvFactorInterior, Finset.mem_filter, Finset.mem_antidiagonal]

private theorem mvFactorInterior_degree_lt {d : σ →₀ ℕ}
    {b : (σ →₀ ℕ) × (σ →₀ ℕ)} (hb : b ∈ mvFactorInterior d) :
    Finsupp.degree b.1 < Finsupp.degree d ∧ Finsupp.degree b.2 < Finsupp.degree d := by
  obtain ⟨hadd, hfst, hsnd⟩ := mem_mvFactorInterior.mp hb
  have hdeg := congrArg Finsupp.degree hadd
  rw [map_add] at hdeg
  have hf : Finsupp.degree b.1 ≠ 0 := (Finsupp.degree_eq_zero_iff _).not.mpr hfst
  have hs : Finsupp.degree b.2 ≠ 0 := (Finsupp.degree_eq_zero_iff _).not.mpr hsnd
  omega

/-- The nonlinear coefficient uses only positive-degree correction indices. -/
def mvFactorLiftConvolution (p q : R[X])
    (c : (σ →₀ ℕ) → degreeLT R p.natDegree × degreeLT R q.natDegree) (d : σ →₀ ℕ) :
    degreeLT R (p.natDegree + q.natDegree) :=
  ∑ b ∈ mvFactorInterior d, mvBoundedCorrectionProduct p q (c b.1).1 (c b.2).2

/-- The unique recursive coefficient candidate. Its constant correction is zero;
all other coefficients come from the finite coprime-factor linear inverse. -/
def mvFactorLiftCoeff (p q : R[X]) (hp : p.Monic) (hpq : IsCoprime p q)
    (e : (σ →₀ ℕ) → degreeLT R (p.natDegree + q.natDegree)) (d : σ →₀ ℕ) :
    degreeLT R p.natDegree × degreeLT R q.natDegree := by
  classical
  exact if d = 0 then 0 else factorCorrection p q hp hpq
    (e d - ∑ b : mvFactorInterior d, mvBoundedCorrectionProduct p q
      (mvFactorLiftCoeff p q hp hpq e b.val.1).1
      (mvFactorLiftCoeff p q hp hpq e b.val.2).2)
termination_by Finsupp.degree d
decreasing_by
  · exact (mvFactorInterior_degree_lt b.property).1
  · exact (mvFactorInterior_degree_lt b.property).2

@[simp] theorem mvFactorLiftCoeff_zero (p q : R[X]) (hp : p.Monic) (hpq : IsCoprime p q)
    (e : (σ →₀ ℕ) → degreeLT R (p.natDegree + q.natDegree)) :
    mvFactorLiftCoeff p q hp hpq e 0 = 0 := by
  rw [mvFactorLiftCoeff]
  simp

theorem mvFactorLiftCoeff_eq (p q : R[X]) (hp : p.Monic) (hpq : IsCoprime p q)
    (e : (σ →₀ ℕ) → degreeLT R (p.natDegree + q.natDegree))
    {d : σ →₀ ℕ} (hd : d ≠ 0) :
    mvFactorLiftCoeff p q hp hpq e d = factorCorrection p q hp hpq
      (e d - mvFactorLiftConvolution p q (mvFactorLiftCoeff p q hp hpq e) d) := by
  classical
  rw [mvFactorLiftCoeff, if_neg hd]
  unfold mvFactorLiftConvolution
  apply congrArg (factorCorrection p q hp hpq)
  apply congrArg (fun z => e d - z)
  exact Finset.sum_coe_sort (mvFactorInterior d)
    (fun b => mvBoundedCorrectionProduct p q
      (mvFactorLiftCoeff p q hp hpq e b.1).1 (mvFactorLiftCoeff p q hp hpq e b.2).2)

private theorem mvFactorLiftConvolution_zero (p q : R[X])
    (c : (σ →₀ ℕ) → degreeLT R p.natDegree × degreeLT R q.natDegree) :
    mvFactorLiftConvolution p q c 0 = 0 := by
  apply Finset.sum_eq_zero
  intro b hb
  have h := (mvFactorInterior_degree_lt hb).1
  simp at h

private def mvCorrectionLeftSeries (p q : R[X])
    (c : (σ →₀ ℕ) → degreeLT R p.natDegree × degreeLT R q.natDegree) :
    MvPowerSeries σ R[X] := fun d => (c d).1

private def mvCorrectionRightSeries (p q : R[X])
    (c : (σ →₀ ℕ) → degreeLT R p.natDegree × degreeLT R q.natDegree) :
    MvPowerSeries σ R[X] := fun d => (c d).2

private theorem mvFactorLiftConvolution_eq_coeff_mul (p q : R[X])
    (c : (σ →₀ ℕ) → degreeLT R p.natDegree × degreeLT R q.natDegree) (hc : c 0 = 0)
    (d : σ →₀ ℕ) :
    (mvFactorLiftConvolution p q c d : R[X]) = MvPowerSeries.coeff d
      (mvCorrectionLeftSeries p q c * mvCorrectionRightSeries p q c) := by
  classical
  rw [MvPowerSeries.coeff_mul]
  simp only [mvFactorLiftConvolution, Submodule.coe_sum, mvBoundedCorrectionProduct,
    MvPowerSeries.coeff_apply, mvFactorInterior, mvCorrectionLeftSeries, mvCorrectionRightSeries]
  apply Finset.sum_filter_of_ne
  intro b _ hb
  constructor
  · intro h
    simp only [h, hc, Prod.fst_zero, ZeroMemClass.coe_zero, zero_mul] at hb
    exact hb rfl
  · intro h
    simp only [h, hc, Prod.snd_zero, ZeroMemClass.coe_zero, mul_zero] at hb
    exact hb rfl

/-- The coefficientwise bounded formal error. Its constant term is supplied
separately as zero when constructing a lift. -/
def mvFactorErrorSeries (p q : R[X])
    (e : (σ →₀ ℕ) → degreeLT R (p.natDegree + q.natDegree)) : MvPowerSeries σ R[X] :=
  fun d => e d

/-- The left correction, including its zero constant coefficient. -/
def mvFactorLiftLeftSeries (p q : R[X]) (hp : p.Monic) (hpq : IsCoprime p q)
    (e : (σ →₀ ℕ) → degreeLT R (p.natDegree + q.natDegree)) : MvPowerSeries σ R[X] :=
  mvCorrectionLeftSeries p q (mvFactorLiftCoeff p q hp hpq e)

/-- The right correction, including its zero constant coefficient. -/
def mvFactorLiftRightSeries (p q : R[X]) (hp : p.Monic) (hpq : IsCoprime p q)
    (e : (σ →₀ ℕ) → degreeLT R (p.natDegree + q.natDegree)) : MvPowerSeries σ R[X] :=
  mvCorrectionRightSeries p q (mvFactorLiftCoeff p q hp hpq e)

@[simp] theorem constantCoeff_mvFactorLiftLeftSeries (p q : R[X]) (hp : p.Monic)
    (hpq : IsCoprime p q) (e : (σ →₀ ℕ) → degreeLT R (p.natDegree + q.natDegree)) :
    MvPowerSeries.constantCoeff (mvFactorLiftLeftSeries p q hp hpq e) = 0 := by
  change ((mvFactorLiftCoeff p q hp hpq e 0).1 : R[X]) = 0
  rw [mvFactorLiftCoeff_zero]
  rfl

@[simp] theorem constantCoeff_mvFactorLiftRightSeries (p q : R[X]) (hp : p.Monic)
    (hpq : IsCoprime p q) (e : (σ →₀ ℕ) → degreeLT R (p.natDegree + q.natDegree)) :
    MvPowerSeries.constantCoeff (mvFactorLiftRightSeries p q hp hpq e) = 0 := by
  change ((mvFactorLiftCoeff p q hp hpq e 0).2 : R[X]) = 0
  rw [mvFactorLiftCoeff_zero]
  rfl

/-- The exact linear-plus-quadratic correction equation in all formal parameters. -/
theorem mvFactorLift_linearization (p q : R[X]) (hp : p.Monic) (hpq : IsCoprime p q)
    (e : (σ →₀ ℕ) → degreeLT R (p.natDegree + q.natDegree)) (he : e 0 = 0) :
    mvFactorLiftLeftSeries p q hp hpq e * MvPowerSeries.C q +
      MvPowerSeries.C p * mvFactorLiftRightSeries p q hp hpq e +
      mvFactorLiftLeftSeries p q hp hpq e * mvFactorLiftRightSeries p q hp hpq e =
        mvFactorErrorSeries p q e := by
  apply MvPowerSeries.ext
  intro d
  by_cases hd : d = 0
  · subst d
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff]
    simp only [map_add, map_mul, MvPowerSeries.constantCoeff_C,
      constantCoeff_mvFactorLiftLeftSeries, constantCoeff_mvFactorLiftRightSeries,
      zero_mul, mul_zero, add_zero]
    change 0 = (e 0 : R[X])
    rw [he]
    rfl
  · have hc := factorCorrection_spec p q hp hpq
      (e d - mvFactorLiftConvolution p q (mvFactorLiftCoeff p q hp hpq e) d)
    rw [← mvFactorLiftCoeff_eq p q hp hpq e hd] at hc
    simp only [Submodule.coe_sub] at hc
    simp only [map_add, MvPowerSeries.coeff_mul_C, MvPowerSeries.coeff_C_mul]
    change (mvFactorLiftCoeff p q hp hpq e d).1 * q +
      p * (mvFactorLiftCoeff p q hp hpq e d).2 +
      MvPowerSeries.coeff d (mvFactorLiftLeftSeries p q hp hpq e *
        mvFactorLiftRightSeries p q hp hpq e) = (e d : R[X])
    unfold mvFactorLiftLeftSeries mvFactorLiftRightSeries
    rw [← mvFactorLiftConvolution_eq_coeff_mul p q (mvFactorLiftCoeff p q hp hpq e)
      (mvFactorLiftCoeff_zero p q hp hpq e) d]
    exact (eq_sub_iff_add_eq).mp hc

/-- The first lifted factor with the prescribed constant polynomial. -/
def mvLiftedLeftFactor (p q : R[X]) (hp : p.Monic) (hpq : IsCoprime p q)
    (e : (σ →₀ ℕ) → degreeLT R (p.natDegree + q.natDegree)) : MvPowerSeries σ R[X] :=
  MvPowerSeries.C p + mvFactorLiftLeftSeries p q hp hpq e

/-- The second lifted factor with the prescribed constant polynomial. -/
def mvLiftedRightFactor (p q : R[X]) (hp : p.Monic) (hpq : IsCoprime p q)
    (e : (σ →₀ ℕ) → degreeLT R (p.natDegree + q.natDegree)) : MvPowerSeries σ R[X] :=
  MvPowerSeries.C q + mvFactorLiftRightSeries p q hp hpq e

theorem mvLiftedFactors_mul (p q : R[X]) (hp : p.Monic) (hpq : IsCoprime p q)
    (e : (σ →₀ ℕ) → degreeLT R (p.natDegree + q.natDegree)) (he : e 0 = 0) :
    mvLiftedLeftFactor p q hp hpq e * mvLiftedRightFactor p q hp hpq e =
      MvPowerSeries.C (p * q) + mvFactorErrorSeries p q e := by
  rw [← mvFactorLift_linearization p q hp hpq e he, map_mul]
  unfold mvLiftedLeftFactor mvLiftedRightFactor
  ring

@[simp] theorem constantCoeff_mvLiftedLeftFactor (p q : R[X]) (hp : p.Monic)
    (hpq : IsCoprime p q) (e : (σ →₀ ℕ) → degreeLT R (p.natDegree + q.natDegree)) :
    MvPowerSeries.constantCoeff (mvLiftedLeftFactor p q hp hpq e) = p := by
  simp [mvLiftedLeftFactor]

@[simp] theorem constantCoeff_mvLiftedRightFactor (p q : R[X]) (hp : p.Monic)
    (hpq : IsCoprime p q) (e : (σ →₀ ℕ) → degreeLT R (p.natDegree + q.natDegree)) :
    MvPowerSeries.constantCoeff (mvLiftedRightFactor p q hp hpq e) = q := by
  simp [mvLiftedRightFactor]

theorem degree_coeff_mvLiftedLeftFactor_lt (p q : R[X]) (hp : p.Monic)
    (hpq : IsCoprime p q) (e : (σ →₀ ℕ) → degreeLT R (p.natDegree + q.natDegree))
    {d : σ →₀ ℕ} (hd : d ≠ 0) :
    (MvPowerSeries.coeff d (mvLiftedLeftFactor p q hp hpq e)).degree < p.natDegree := by
  rw [mvLiftedLeftFactor, map_add, MvPowerSeries.coeff_C_of_ne_zero hd, zero_add]
  exact mem_degreeLT.mp (mvFactorLiftCoeff p q hp hpq e d).1.property

theorem degree_coeff_mvLiftedRightFactor_lt (p q : R[X]) (hp : p.Monic)
    (hpq : IsCoprime p q) (e : (σ →₀ ℕ) → degreeLT R (p.natDegree + q.natDegree))
    {d : σ →₀ ℕ} (hd : d ≠ 0) :
    (MvPowerSeries.coeff d (mvLiftedRightFactor p q hp hpq e)).degree < q.natDegree := by
  rw [mvLiftedRightFactor, map_add, MvPowerSeries.coeff_C_of_ne_zero hd, zero_add]
  exact mem_degreeLT.mp (mvFactorLiftCoeff p q hp hpq e d).2.property

/-- Total-degree induction proves uniqueness among all bounded coefficient
solutions, not only among candidates defined by the recursion. -/
theorem mvFactorLiftCoeff_unique (p q : R[X]) (hp : p.Monic) (hpq : IsCoprime p q)
    (e : (σ →₀ ℕ) → degreeLT R (p.natDegree + q.natDegree))
    (c : (σ →₀ ℕ) → degreeLT R p.natDegree × degreeLT R q.natDegree) (hc0 : c 0 = 0)
    (hc : ∀ d, d ≠ 0 → (c d).1 * q + p * (c d).2 +
      (mvFactorLiftConvolution p q c d : R[X]) = e d) (d : σ →₀ ℕ) :
    c d = mvFactorLiftCoeff p q hp hpq e d := by
  refine (measure Finsupp.degree).wf.induction (C := fun d =>
    c d = mvFactorLiftCoeff p q hp hpq e d) d ?_
  intro d ih
  by_cases hd : d = 0
  · simp only [hd, hc0, mvFactorLiftCoeff_zero]
  · have hconv : mvFactorLiftConvolution p q c d =
        mvFactorLiftConvolution p q (mvFactorLiftCoeff p q hp hpq e) d := by
      unfold mvFactorLiftConvolution
      apply Finset.sum_congr rfl
      intro b hb
      rw [ih b.1 (mvFactorInterior_degree_lt hb).1,
        ih b.2 (mvFactorInterior_degree_lt hb).2]
    rw [mvFactorLiftCoeff_eq p q hp hpq e hd]
    apply factorCorrection_unique
    change (c d).1 * q + p * (c d).2 = (e d : R[X]) -
      (mvFactorLiftConvolution p q (mvFactorLiftCoeff p q hp hpq e) d : R[X])
    rw [← hconv]
    exact (eq_sub_iff_add_eq).mpr (hc d hd)

/-- Uniqueness of bounded zero-constant correction series. -/
theorem mvFactorLiftSeries_unique (p q : R[X]) (hp : p.Monic) (hpq : IsCoprime p q)
    (e : (σ →₀ ℕ) → degreeLT R (p.natDegree + q.natDegree)) (A B : MvPowerSeries σ R[X])
    (hA0 : MvPowerSeries.constantCoeff A = 0) (hB0 : MvPowerSeries.constantCoeff B = 0)
    (hA : ∀ d, (MvPowerSeries.coeff d A).degree < p.natDegree)
    (hB : ∀ d, (MvPowerSeries.coeff d B).degree < q.natDegree)
    (heq : A * MvPowerSeries.C q + MvPowerSeries.C p * B + A * B = mvFactorErrorSeries p q e) :
    A = mvFactorLiftLeftSeries p q hp hpq e ∧ B = mvFactorLiftRightSeries p q hp hpq e := by
  let c : (σ →₀ ℕ) → degreeLT R p.natDegree × degreeLT R q.natDegree := fun d =>
    (⟨MvPowerSeries.coeff d A, mem_degreeLT.mpr (hA d)⟩,
      ⟨MvPowerSeries.coeff d B, mem_degreeLT.mpr (hB d)⟩)
  have hc0 : c 0 = 0 := by
    apply Prod.ext <;> apply Subtype.ext
    · exact hA0
    · exact hB0
  have hcA : mvCorrectionLeftSeries p q c = A := MvPowerSeries.ext fun d => rfl
  have hcB : mvCorrectionRightSeries p q c = B := MvPowerSeries.ext fun d => rfl
  have hc (d : σ →₀ ℕ) (_ : d ≠ 0) : (c d).1 * q + p * (c d).2 +
      (mvFactorLiftConvolution p q c d : R[X]) = e d := by
    rw [mvFactorLiftConvolution_eq_coeff_mul p q c hc0 d, hcA, hcB]
    have he := congrArg (MvPowerSeries.coeff d) heq
    simp only [map_add, MvPowerSeries.coeff_mul_C, MvPowerSeries.coeff_C_mul] at he
    exact he
  have hcoeff := mvFactorLiftCoeff_unique p q hp hpq e c hc0 hc
  constructor
  · apply MvPowerSeries.ext
    intro d
    exact congrArg (fun hk : degreeLT R p.natDegree × degreeLT R q.natDegree =>
      (hk.1 : R[X])) (hcoeff d)
  · apply MvPowerSeries.ext
    intro d
    exact congrArg (fun hk : degreeLT R p.natDegree × degreeLT R q.natDegree =>
      (hk.2 : R[X])) (hcoeff d)

/-- All factors with the prescribed constants and positive-coefficient degree
bounds coincide with the constructed formal factors. -/
theorem mvLiftedFactors_unique (p q : R[X]) (hp : p.Monic) (hpq : IsCoprime p q)
    (e : (σ →₀ ℕ) → degreeLT R (p.natDegree + q.natDegree)) (F G : MvPowerSeries σ R[X])
    (hF0 : MvPowerSeries.constantCoeff F = p) (hG0 : MvPowerSeries.constantCoeff G = q)
    (hF : ∀ d, d ≠ 0 → (MvPowerSeries.coeff d F).degree < p.natDegree)
    (hG : ∀ d, d ≠ 0 → (MvPowerSeries.coeff d G).degree < q.natDegree)
    (hmul : F * G = MvPowerSeries.C (p * q) + mvFactorErrorSeries p q e) :
    F = mvLiftedLeftFactor p q hp hpq e ∧ G = mvLiftedRightFactor p q hp hpq e := by
  let A := F - MvPowerSeries.C p
  let B := G - MvPowerSeries.C q
  have hA0 : MvPowerSeries.constantCoeff A = 0 := by simp only [A, map_sub, hF0,
    MvPowerSeries.constantCoeff_C, sub_self]
  have hB0 : MvPowerSeries.constantCoeff B = 0 := by simp only [B, map_sub, hG0,
    MvPowerSeries.constantCoeff_C, sub_self]
  have hA (d : σ →₀ ℕ) : (MvPowerSeries.coeff d A).degree < p.natDegree := by
    by_cases hd : d = 0
    · subst d
      rw [MvPowerSeries.coeff_zero_eq_constantCoeff, hA0, degree_zero]
      exact WithBot.bot_lt_coe _
    · simpa only [A, map_sub, MvPowerSeries.coeff_C_of_ne_zero hd, sub_zero] using hF d hd
  have hB (d : σ →₀ ℕ) : (MvPowerSeries.coeff d B).degree < q.natDegree := by
    by_cases hd : d = 0
    · subst d
      rw [MvPowerSeries.coeff_zero_eq_constantCoeff, hB0, degree_zero]
      exact WithBot.bot_lt_coe _
    · simpa only [B, map_sub, MvPowerSeries.coeff_C_of_ne_zero hd, sub_zero] using hG d hd
  have heq : A * MvPowerSeries.C q + MvPowerSeries.C p * B + A * B = mvFactorErrorSeries p q e := by
    calc
      _ = F * G - MvPowerSeries.C (p * q) := by dsimp [A, B]; rw [map_mul]; ring
      _ = _ := by rw [hmul]; abel
  obtain ⟨hA', hB'⟩ := mvFactorLiftSeries_unique p q hp hpq e A B hA0 hB0 hA hB heq
  constructor
  · rw [mvLiftedLeftFactor, ← hA']
    exact (add_sub_cancel _ _).symm
  · rw [mvLiftedRightFactor, ← hB']
    exact (add_sub_cancel _ _).symm

/-- Existence and uniqueness of bounded formal lifts in any set of parameters.
In particular this includes every finite parameter family and the empty family. -/
theorem existsUnique_mvFormal_factor_lift (p q : R[X]) (hp : p.Monic) (hpq : IsCoprime p q)
    (e : (σ →₀ ℕ) → degreeLT R (p.natDegree + q.natDegree)) (he : e 0 = 0) :
    ∃! FG : MvPowerSeries σ R[X] × MvPowerSeries σ R[X],
      MvPowerSeries.constantCoeff FG.1 = p ∧ MvPowerSeries.constantCoeff FG.2 = q ∧
      (∀ d, d ≠ 0 → (MvPowerSeries.coeff d FG.1).degree < p.natDegree) ∧
      (∀ d, d ≠ 0 → (MvPowerSeries.coeff d FG.2).degree < q.natDegree) ∧
      FG.1 * FG.2 = MvPowerSeries.C (p * q) + mvFactorErrorSeries p q e := by
  refine ⟨⟨mvLiftedLeftFactor p q hp hpq e, mvLiftedRightFactor p q hp hpq e⟩,
    ⟨constantCoeff_mvLiftedLeftFactor p q hp hpq e, constantCoeff_mvLiftedRightFactor p q hp hpq e,
      fun _ hd => degree_coeff_mvLiftedLeftFactor_lt p q hp hpq e hd,
      fun _ hd => degree_coeff_mvLiftedRightFactor_lt p q hp hpq e hd,
      mvLiftedFactors_mul p q hp hpq e he⟩, ?_⟩
  rintro ⟨F, G⟩ ⟨hF0, hG0, hF, hG, hmul⟩
  obtain ⟨h1, h2⟩ := mvLiftedFactors_unique p q hp hpq e F G hF0 hG0 hF hG hmul
  exact Prod.ext h1 h2

/-- Input-facing multivariate formal factorization for an arbitrary bounded
perturbation of the coprime constant product. No assumed lift or summability
condition is part of the hypotheses. -/
theorem existsUnique_mvFormal_factorization (p q : R[X]) (hp : p.Monic) (hpq : IsCoprime p q)
    (H : MvPowerSeries σ R[X]) (hH0 : MvPowerSeries.constantCoeff H = p * q)
    (hH : ∀ d, d ≠ 0 → (MvPowerSeries.coeff d H).degree < (p.natDegree + q.natDegree : ℕ)) :
    ∃! FG : MvPowerSeries σ R[X] × MvPowerSeries σ R[X],
      MvPowerSeries.constantCoeff FG.1 = p ∧ MvPowerSeries.constantCoeff FG.2 = q ∧
      (∀ d, d ≠ 0 → (MvPowerSeries.coeff d FG.1).degree < p.natDegree) ∧
      (∀ d, d ≠ 0 → (MvPowerSeries.coeff d FG.2).degree < q.natDegree) ∧ FG.1 * FG.2 = H := by
  classical
  let e : (σ →₀ ℕ) → degreeLT R (p.natDegree + q.natDegree) := fun d =>
    if hd : d = 0 then 0 else ⟨MvPowerSeries.coeff d H, mem_degreeLT.mpr (hH d hd)⟩
  have he : e 0 = 0 := by simp [e]
  have hshape : MvPowerSeries.C (p * q) + mvFactorErrorSeries p q e = H := by
    apply MvPowerSeries.ext
    intro d
    simp only [map_add, MvPowerSeries.coeff_C]
    by_cases hd : d = 0
    · subst d
      change p * q + (e 0 : R[X]) = MvPowerSeries.constantCoeff H
      rw [he, hH0, Submodule.coe_zero, add_zero]
    · rw [if_neg hd, zero_add]
      change (e d : R[X]) = MvPowerSeries.coeff d H
      simp only [e, dif_neg hd]
  simpa only [hshape] using existsUnique_mvFormal_factor_lift p q hp hpq e he

end

end Surreal.FinitePolynomial
