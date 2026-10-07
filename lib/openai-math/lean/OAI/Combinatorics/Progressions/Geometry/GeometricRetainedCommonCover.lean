import OAI.Combinatorics.Progressions.Estimates.CoefficientRowEvaluation
import OAI.Combinatorics.Progressions.Lattices.RetainedAffineCommonCover

namespace OAI

section

namespace Erdos3.VectorPolynomial

def geometricSiteBudget (m q : ℕ) (P : ℝ) : ℝ :=
  ((m : ℝ) + 1) * (P + 1) ^ (m + 1) + 2 ^ q

theorem geometricSiteBudget_nonneg (m q : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ geometricSiteBudget m q P := by
  unfold geometricSiteBudget
  positivity

theorem le_geometricSiteBudget (m q : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    P ≤ geometricSiteBudget m q P := by
  have hp : P + 1 ≤ (P + 1) ^ (m + 1) := by
    simpa using pow_le_pow_right₀ (by linarith : 1 ≤ P + 1) (show 1 ≤ m + 1 by omega)
  unfold geometricSiteBudget
  have hn : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have ht : (0 : ℝ) ≤ 2 ^ q := by positivity
  nlinarith

theorem degree_mul_le_geometricSiteBudget (m q : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    (m : ℝ) * (P + 1) ≤ geometricSiteBudget m q P := by
  have hp : P + 1 ≤ (P + 1) ^ (m + 1) := by
    simpa using pow_le_pow_right₀ (by linarith : 1 ≤ P + 1) (show 1 ≤ m + 1 by omega)
  calc
    _ ≤ ((m : ℝ) + 1) * (P + 1) ^ (m + 1) :=
      mul_le_mul (by linarith) hp (by linarith) (by positivity)
    _ ≤ geometricSiteBudget m q P := le_add_of_nonneg_right (by positivity)

theorem boundedCoefficientExponent_card_le_geometricSiteBudget {K : Type*} [Fintype K]
    (m q : ℕ) {h : ℕ} (hh : h ≤ m) {P : ℝ} (hP : 0 ≤ P)
    (hK : (Fintype.card K : ℝ) ≤ P) :
    (Fintype.card (BoundedCoefficientExponent K h) : ℝ) ≤ geometricSiteBudget m q P := by
  have hc : (Fintype.card (BoundedCoefficientExponent K h) : ℝ) ≤
      ((h : ℝ) + 1) * ((Fintype.card K : ℝ) + 1) ^ h := by
    exact_mod_cast boundedCoefficientExponent_card_le (K := K) h
  apply hc.trans
  calc
    _ ≤ ((m : ℝ) + 1) * (P + 1) ^ (m + 1) := by
      apply mul_le_mul (by exact_mod_cast Nat.add_le_add_right hh 1)
      · exact (pow_le_pow_left₀ (by positivity) (by linarith) h).trans
          (pow_le_pow_right₀ (by linarith) (by omega))
      · positivity
      · positivity
    _ ≤ geometricSiteBudget m q P := le_add_of_nonneg_right (by positivity)

theorem cubeSites_card_le_geometricSiteBudget (m q : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    (Fintype.card (Finset (Fin q)) : ℝ) ≤ geometricSiteBudget m q P := by
  simp only [Fintype.card_finset, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
  exact le_add_of_nonneg_left (by positivity)

noncomputable def exponentialSiteHeight (m : ℕ) (P : ℝ) : ℕ := ⌈Real.exp P⌉₊ ^ m

theorem exponentialSiteHeight_pos (m : ℕ) (P : ℝ) : 0 < exponentialSiteHeight m P := by
  exact pow_pos (Nat.ceil_pos.mpr (Real.exp_pos _)) _

theorem exponentialSiteHeight_le (m : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    (exponentialSiteHeight m P : ℝ) ≤ Real.exp ((m : ℝ) * (P + 1)) := by
  have hceil : (⌈Real.exp P⌉₊ : ℝ) ≤ Real.exp (P + 1) := by
    calc
      _ ≤ Real.exp P + 1 := (Nat.ceil_lt_add_one (Real.exp_pos P).le).le
      _ ≤ Real.exp P * 2 := by linarith [Real.one_le_exp hP]
      _ ≤ Real.exp P * Real.exp 1 :=
        mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (1 : ℝ)]) (Real.exp_pos P).le
      _ = Real.exp (P + 1) := (Real.exp_add _ _).symm
  simpa only [exponentialSiteHeight, Nat.cast_pow, Real.exp_nat_mul] using
    pow_le_pow_left₀ (Nat.cast_nonneg _) hceil m

theorem boundedSiteMatrix_height_of_exp {K S : Type*} (m : ℕ) {h : ℕ} (hh : h ≤ m)
    (site : S → K → ℤ) {P : ℝ}
    (hsite : ∀ s k, |(site s k : ℝ)| ≤ Real.exp P)
    (s : S) (d : BoundedCoefficientExponent K h) :
    RationalHeightLE (boundedSiteMatrix h site s d : ℚ) (exponentialSiteHeight m P) := by
  have hceil : 1 ≤ ⌈Real.exp P⌉₊ := Nat.ceil_pos.mpr (Real.exp_pos _)
  have hb : ∀ s k, (site s k).natAbs ≤ ⌈Real.exp P⌉₊ := by
    intro s k
    have he : ((site s k).natAbs : ℝ) ≤ (⌈Real.exp P⌉₊ : ℝ) := by
      simpa using (hsite s k).trans (Nat.le_ceil (Real.exp P))
    exact_mod_cast he
  exact (boundedSiteMatrix_height h site hceil hb s d).mono
    (Nat.pow_le_pow_right hceil hh)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Polynomial

theorem exists_geometricSiteBudget_absorption (m q a : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ P : ℝ, 0 ≤ P →
      (geometricSiteBudget m q P + a) ^ a ≤ (P + A) ^ A := by
  obtain ⟨A, hA, hb⟩ := exists_natPolynomial_eval_budget
    ((C (m + 1) * (X + 1) ^ (m + 1) + C (2 ^ q) + C a) ^ a)
  refine ⟨A, hA, ?_⟩
  intro P hP
  simpa [geometricSiteBudget, Polynomial.eval₂_pow] using hb P hP

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Polynomial

theorem exists_geometric_positive_cover_budget (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ P : ℝ, 0 ≤ P →
      (m : ℝ) * (geometricSiteBudget m q P + 2) ^ 36 ≤ (P + A) ^ A := by
  obtain ⟨A, hA, h⟩ := exists_natPolynomial_eval_budget
    (C m * (C (m + 1) * (X + 1) ^ (m + 1) + C (2 ^ q) + 2) ^ 36)
  refine ⟨A, hA, ?_⟩
  intro P hP
  simpa [geometricSiteBudget, Polynomial.eval₂_pow, Nat.cast_add] using h P hP

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

theorem exists_geometric_retained_common_cover (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {K : Type*} [Fintype K]
    (root : K → ℤ) (difference : Fin q → K → ℤ)
    {P : ℝ} (_hP : 0 ≤ P) (_hK : (Fintype.card K : ℝ) ≤ P)
    (_hsite : ∀ (s : Finset (Fin q)) k,
      |((affineSite root difference s (some k) : ℤ) : ℝ)| ≤ Real.exp P),
    ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ Real.exp ((P + A) ^ A) ∧
    ∀ {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (_hfrequency : ∀ j d, d.degree ≤ j.val + 1 → ∀ a,
      |(frequency j d a : ℝ)| ≤ Real.exp P)
    (_hretained : affineCubeModeFactors U root difference frequency),
    ∃ b : ∀ j, Matrix (Finset (Fin q)) (J j) ℤ,
      (∀ j s a, |(b j s a : ℝ)| ≤ Real.exp ((P + A) ^ A)) ∧
      ∀ (j : Fin m) (p : VectorPolynomial K ℝ (U j)),
        DegreeLE (1 : K → ℕ) (j.val + 1) p →
        CircleFourier.character
          (coefficientFunctional (fun d a => (frequency j d a : ℝ))
            (map (U j).subtype p) : CircleFourier.Circle) =
        subspaceArrayCharacter (U j) (b j)
          (QuotientAddGroup.mk' (subspaceArrayIntegerLattice (Finset (Fin q)) (U j))
            ((D : ℝ)⁻¹ • VectorPolynomial.siteEvaluation
              (fun s k => ((affineSite root difference s (some k) : ℤ) : ℝ)) p)) := by
  obtain ⟨A₀, _, hc⟩ := exists_retained_affine_common_cover m
  obtain ⟨A, hA, hb⟩ := exists_geometricSiteBudget_absorption m q A₀
  refine ⟨A, hA, ?_⟩
  intro K _ root difference P hP hK hsite
  have hbudget := hb P hP
  have hPP := le_geometricSiteBudget m q hP
  obtain ⟨D, hD, hDP, hrows⟩ := hc root difference
    (exponentialSiteHeight_pos m P)
    (fun j s d => boundedSiteMatrix_height_of_exp m (Nat.succ_le_of_lt j.isLt)
      (fun s k => affineSite root difference s (some k)) hsite s d)
    (geometricSiteBudget_nonneg m q hP)
    (fun j => boundedCoefficientExponent_card_le_geometricSiteBudget m q
      (Nat.succ_le_of_lt j.isLt) hP hK)
    (cubeSites_card_le_geometricSiteBudget m q hP)
    ((exponentialSiteHeight_le m hP).trans
      (Real.exp_le_exp.mpr (degree_mul_le_geometricSiteBudget m q hP)))
  refine ⟨D, hD, hDP.trans (Real.exp_le_exp.mpr hbudget), ?_⟩
  intro J _ U frequency hfrequency hretained
  obtain ⟨b, hbnd, hchar⟩ := hrows U frequency (Real.exp_pos P).le
    (Real.exp_le_exp.mpr hPP) hfrequency hretained
  exact ⟨b, fun j s a => (hbnd j s a).trans (Real.exp_le_exp.mpr hbudget), hchar⟩

end Erdos3.BooleanCubeKernel

end

end OAI
