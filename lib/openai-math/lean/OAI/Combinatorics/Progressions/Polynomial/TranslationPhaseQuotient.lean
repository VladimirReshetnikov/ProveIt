import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Complex.Circle
import Mathlib.GroupTheory.QuotientGroup.Defs
import OAI.Combinatorics.Progressions.Polynomial.CRTPolynomialChargeBound
import OAI.Combinatorics.Progressions.Polynomial.PolynomialCoefficientNormalization
import OAI.Combinatorics.Progressions.Polynomial.PolynomialTranslationActionCompatibility
import OAI.Combinatorics.Progressions.Polynomial.RealPolynomialMassBox

namespace OAI


namespace Erdos3

open MvPolynomial Module

variable {σ R : Type*} [CommRing R]

theorem weightedSupportLE_moduleFinite [Finite σ] (w : σ → ℕ)
    (hw : ∀ i, 0 < w i) (n : ℕ) : Module.Finite R (weightedSupportLE (R := R) w n) := by
  let : Fintype {a : σ →₀ ℕ | Finsupp.weight w a ≤ n} :=
    (Finsupp.finite_of_nat_weight_le w (fun i => (hw i).ne') n).fintype
  exact Module.Finite.of_basis (MvPolynomial.basisRestrictSupport R
    {a : σ →₀ ℕ | Finsupp.weight w a ≤ n})

theorem exponentSum_le_positive_weight (w : σ → ℕ) (hw : ∀ i, 0 < w i) (a : σ →₀ ℕ) :
    a.sum (fun _ n => n) ≤ Finsupp.weight w a := by
  simp only [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul]
  exact Finset.sum_le_sum (fun i _ => Nat.le_mul_of_pos_right (a i) (hw i))

theorem weightedSupportLE_finrank_le {K : Type*} [Field K] [Fintype σ]
    (w : σ → ℕ) (hw : ∀ i, 0 < w i) (n : ℕ) :
    finrank K (weightedSupportLE (R := K) w n) ≤ (Fintype.card σ + 1) ^ n := by
  classical
  let hs := Finsupp.finite_of_nat_weight_le w (fun i => (hw i).ne') n
  let : Fintype {a : σ →₀ ℕ | Finsupp.weight w a ≤ n} := hs.fintype
  have hcard := boundedExponentSet_card_le hs.toFinset n (fun a ha =>
    (exponentSum_le_positive_weight w hw a).trans (hs.mem_toFinset.mp ha))
  change finrank K (MvPolynomial.restrictSupport K
    {a : σ →₀ ℕ | Finsupp.weight w a ≤ n}) ≤ _
  rw [finrank_eq_card_basis (MvPolynomial.basisRestrictSupport K
    {a : σ →₀ ℕ | Finsupp.weight w a ≤ n})]
  simpa only [Set.Finite.card_toFinset] using hcard

end Erdos3


namespace Erdos3

open MvPolynomial

variable {B U : Type*}

noncomputable def translationPhaseArgument (D₀ : MvPolynomial B ℝ)
    (g : PolynomialTranslationGroupOver ℝ B) (β : B → ℝ) : ℝ :=
  eval β g.polynomial + eval (β - g.base) D₀

theorem translationPhaseArgument_mul (D₀ : MvPolynomial B ℝ)
    (g γ : PolynomialTranslationGroupOver ℝ B) (β : B → ℝ) :
    translationPhaseArgument D₀ (g * γ) (β + γ.base) =
      translationPhaseArgument D₀ g β + eval (β + γ.base) γ.polynomial := by
  simp only [translationPhaseArgument, PolynomialTranslationGroupOver.polynomial_mul,
    PolynomialTranslationGroupOver.base_mul, map_add, polynomialTranslate_eval_ring]
  have h₁ : (fun i => (β + γ.base) i + (-γ.base) i) = β := by ext i; simp
  have h₂ : β + γ.base - (g.base + γ.base) = β - g.base := by abel
  rw [h₁, h₂]
  ring

theorem eval_integer_polynomial_real (Q : MvPolynomial B ℤ) (β : B → ℤ) :
    eval (fun i => (β i : ℝ)) (MvPolynomial.map (Int.castRingHom ℝ) Q) =
      (eval β Q : ℝ) := by
  induction Q using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq, Int.cast_add]
  | mul_X p i hp => simp only [map_mul, map_X, eval_X, hp, Int.cast_mul]

theorem translationPhaseArgument_integer_character
    (χ : AddChar ℝ ℂ) (hχ : ∀ z : ℤ, χ (z : ℝ) = 1)
    (D₀ : MvPolynomial B ℝ) (g : PolynomialTranslationGroupOver ℝ B)
    (z β : B → ℤ) (Q : MvPolynomial B ℤ) :
    χ (translationPhaseArgument D₀
      (g * ⟨fun i => (z i : ℝ), MvPolynomial.map (Int.castRingHom ℝ) Q⟩)
      (fun i => ((β i + z i : ℤ) : ℝ))) =
        χ (translationPhaseArgument D₀ g (fun i => (β i : ℝ))) := by
  have hβ : (fun i => ((β i + z i : ℤ) : ℝ)) =
      (fun i => (β i : ℝ)) + (fun i => (z i : ℝ)) := by ext i; simp
  rw [hβ, translationPhaseArgument_mul, χ.map_add_eq_mul]
  have hQ : eval ((fun i => (β i : ℝ)) + (fun i => (z i : ℝ)))
      (MvPolynomial.map (Int.castRingHom ℝ) Q) = (eval (β + z) Q : ℝ) := by
    change eval (fun i => (β i : ℝ) + (z i : ℝ)) _ = _
    simpa only [Pi.add_apply, Int.cast_add] using eval_integer_polynomial_real Q (β + z)
  rw [hQ, hχ, mul_one]

theorem translationPhaseArgument_majorSymbol
    (D : MvPolynomial (U ⊕ B) ℝ) (D₀ : MvPolynomial B ℝ)
    (A : B → MvPolynomial U ℝ) (u : U → ℝ) (β : B → ℝ) :
    translationPhaseArgument D₀ (algebraicMajorSymbol D D₀ A u) β =
      eval (Sum.elim u β) D := by
  simp only [translationPhaseArgument, algebraicMajorSymbol, map_sub,
    polynomialTranslate_eval_ring, specializeMajorParameters_eval]
  have he : (fun i => β i + -eval u (A i)) = β - (fun i => eval u (A i)) := by
    ext i; simp [sub_eq_add_neg]
  rw [he]
  exact sub_add_cancel _ _

theorem translationPhaseArgument_fourier_integer
    (D₀ : MvPolynomial B ℝ) (g : PolynomialTranslationGroupOver ℝ B)
    (z β : B → ℤ) (Q : MvPolynomial B ℤ) :
    (Real.fourierChar (translationPhaseArgument D₀
      (g * ⟨fun i => (z i : ℝ), MvPolynomial.map (Int.castRingHom ℝ) Q⟩)
      (fun i => ((β i + z i : ℤ) : ℝ))) : ℂ) =
        (Real.fourierChar (translationPhaseArgument D₀ g (fun i => (β i : ℝ))) : ℂ) := by
  apply translationPhaseArgument_integer_character
    (Circle.coeHom.compAddChar Real.fourierChar) ?_
  intro z
  change (Circle.exp (2 * Real.pi * (z : ℝ)) : ℂ) = 1
  rw [mul_comm (2 * Real.pi), Circle.exp_intCast_mul]
  simp

noncomputable def translationPhaseFunction (D₀ : MvPolynomial B ℝ)
    (g : PolynomialTranslationGroupOver ℝ B) : ℂ :=
  Real.fourierChar (translationPhaseArgument D₀ g (fun i => (⌊g.base i + 1 / 2⌋ : ℝ)))

theorem translationPhaseFunction_integer_lattice
    (D₀ : MvPolynomial B ℝ) (g : PolynomialTranslationGroupOver ℝ B)
    (z : B → ℤ) (Q : MvPolynomial B ℤ) :
    translationPhaseFunction D₀
      (g * ⟨fun i => (z i : ℝ), MvPolynomial.map (Int.castRingHom ℝ) Q⟩) =
        translationPhaseFunction D₀ g := by
  unfold translationPhaseFunction
  have hfloor (i : B) : ⌊(g.base i + (z i : ℝ)) + 1 / 2⌋ =
      ⌊g.base i + 1 / 2⌋ + z i := by
    rw [show g.base i + (z i : ℝ) + 1 / 2 = (g.base i + 1 / 2) + z i by ring,
      Int.floor_add_intCast]
  simp only [PolynomialTranslationGroupOver.base_mul, Pi.add_apply, hfloor]
  exact translationPhaseArgument_fourier_integer D₀ g z (fun i => ⌊g.base i + 1 / 2⌋) Q

theorem translationPhaseFunction_norm (D₀ : MvPolynomial B ℝ)
    (g : PolynomialTranslationGroupOver ℝ B) : ‖translationPhaseFunction D₀ g‖ = 1 := by
  exact Circle.norm_coe _

theorem translationPhaseFunction_central
    (D₀ : MvPolynomial B ℝ) (g : PolynomialTranslationGroupOver ℝ B) (a : ℝ) :
    translationPhaseFunction D₀ (g * ⟨0, C a⟩) =
      translationPhaseFunction D₀ g * (Real.fourierChar a : ℂ) := by
  unfold translationPhaseFunction
  have hb : (g * (⟨0, C a⟩ : PolynomialTranslationGroupOver ℝ B)).base = g.base := by
    simp
  rw [hb]
  have ha := translationPhaseArgument_mul D₀ g
    (⟨0, C a⟩ : PolynomialTranslationGroupOver ℝ B) (fun i => (⌊g.base i + 1 / 2⌋ : ℝ))
  simp only [add_zero, eval_C] at ha
  rw [ha, Real.fourierChar.map_add_eq_mul]
  rfl

theorem translationPhaseFunction_on_chart
    (D₀ : MvPolynomial B ℝ) (g : PolynomialTranslationGroupOver ℝ B)
    (β : B → ℤ) (hβ : ∀ i, |g.base i - (β i : ℝ)| < 1 / 2) :
    translationPhaseFunction D₀ g =
      (Real.fourierChar (translationPhaseArgument D₀ g (fun i => (β i : ℝ))) : ℂ) := by
  have hf (i : B) : ⌊g.base i + 1 / 2⌋ = β i := by
    apply Int.floor_eq_iff.mpr
    have hi := (abs_lt.mp (hβ i))
    constructor <;> linarith
  simp only [translationPhaseFunction, hf]

theorem translationPhaseFunction_polynomial_input
    (D D₀ : MvPolynomial B ℝ) (x : B → ℝ) (β : B → ℤ)
    (hβ : ∀ i, |x i - (β i : ℝ)| < 1 / 2) :
    translationPhaseFunction D₀
      (⟨x, D - polynomialTranslate (-x) D₀⟩ : PolynomialTranslationGroupOver ℝ B) =
        (Real.fourierChar (eval (fun i => (β i : ℝ)) D) : ℂ) := by
  rw [translationPhaseFunction_on_chart D₀ _ β hβ]
  congr 2
  simp only [translationPhaseArgument, map_sub, polynomialTranslate_eval_ring]
  have he : (fun i => (β i : ℝ) + (-x) i) = (fun i => (β i : ℝ)) - x := by
    ext i
    simp [sub_eq_add_neg]
  rw [he, sub_add_cancel]

end Erdos3


namespace Erdos3

open MvPolynomial

variable {U X : Type*}

theorem real_grid_polynomial_residue_difference (R : MvPolynomial U ℝ)
    (q : ℕ) (hq : 0 < q) (hR : realPolynomialCoefficientGrid q R)
    (r v : U → ℤ) :
    ∃ k : ℤ,
      eval (fun i => ((r i + (q : ℤ) * v i : ℤ) : ℝ)) R -
        eval (fun i => (r i : ℝ)) R = (k : ℝ) := by
  obtain ⟨S, hS⟩ := (realPolynomialCoefficientGrid_iff q R).mp hR
  have heval (y : U → ℤ) : (eval y S : ℝ) =
      (q : ℝ) * eval (fun i => (y i : ℝ)) R := by
    rw [← eval_integer_polynomial_real, hS, map_mul, eval_C]
  obtain ⟨k, hk⟩ := integer_polynomial_sub_dvd S
    (fun i => r i + (q : ℤ) * v i) r (q : ℤ) (fun i => by
      exact ⟨v i, by ring⟩)
  refine ⟨k, ?_⟩
  apply mul_left_cancel₀ (show (q : ℝ) ≠ 0 by exact_mod_cast hq.ne')
  calc
    (q : ℝ) * (eval (fun i => ((r i + (q : ℤ) * v i : ℤ) : ℝ)) R -
        eval (fun i => (r i : ℝ)) R) =
        ((eval (fun i => r i + (q : ℤ) * v i) S - eval r S : ℤ) : ℝ) := by
      rw [Int.cast_sub, heval, heval, mul_sub]
    _ = (q : ℝ) * (k : ℝ) := by exact_mod_cast hk

theorem real_fourierChar_add_integer (t : ℝ) (k : ℤ) :
    (Real.fourierChar (t + (k : ℝ)) : ℂ) = (Real.fourierChar t : ℂ) := by
  rw [Real.fourierChar.map_add_eq_mul, Circle.coe_mul]
  have hk : (Real.fourierChar (k : ℝ) : ℂ) = 1 := by
    change (Circle.exp (2 * Real.pi * (k : ℝ)) : ℂ) = 1
    rw [mul_comm (2 * Real.pi), Circle.exp_intCast_mul]
    simp
  rw [hk, mul_one]

theorem real_fourierChar_sub_star (a b : ℝ) :
    (Real.fourierChar (a - b) : ℂ) =
      (Real.fourierChar a : ℂ) * star (Real.fourierChar b : ℂ) := by
  rw [Real.fourierChar.map_sub_eq_div, div_eq_mul_inv, Circle.coe_mul,
    Circle.coe_inv_eq_conj]
  rfl

noncomputable def residueAffinePolynomial (q : ℕ) (r : U → ℤ)
    (P : MvPolynomial U ℝ) : MvPolynomial U ℝ :=
  eval₂Hom C (fun i => C (r i : ℝ) + C (q : ℝ) * MvPolynomial.X i) P

theorem residueAffinePolynomial_eval (q : ℕ) (r v : U → ℤ)
    (P : MvPolynomial U ℝ) :
    eval (fun i => (v i : ℝ)) (residueAffinePolynomial q r P) =
      eval (fun i => ((r i + (q : ℤ) * v i : ℤ) : ℝ)) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [residueAffinePolynomial]
  | add P Q hP hQ => simpa only [residueAffinePolynomial, map_add] using congrArg₂ (· + ·) hP hQ
  | mul_X P i hP =>
    simp only [residueAffinePolynomial, map_mul, eval₂Hom_X', map_add, eval_C,
      eval_X, Int.cast_add, Int.cast_mul, Int.cast_natCast] at *
    rw [hP]

theorem residueAffinePolynomial_totalDegree_le (q : ℕ) (r : U → ℤ)
    (P : MvPolynomial U ℝ) (n : ℕ) (hP : P.totalDegree ≤ n) :
    (residueAffinePolynomial q r P).totalDegree ≤ n := by
  have hf (i : U) : (C (r i : ℝ) + C (q : ℝ) * MvPolynomial.X i).totalDegree ≤ 1 := by
    apply (totalDegree_add _ _).trans
    apply max_le
    · simp only [totalDegree_C]; omega
    · exact (totalDegree_mul _ _).trans (by
        simp only [totalDegree_C, totalDegree_X, Nat.zero_add, le_refl])
  simpa only [residueAffinePolynomial, Nat.mul_one] using
    polynomial_substitution_totalDegree_le P _ hf hP

noncomputable def localMajorLowerPhase (n q : ℕ) (r : U → ℤ)
    (P : MvPolynomial U ℝ) : MvPolynomial U ℝ :=
  residueAffinePolynomial q r (P - homogeneousComponent (n + 1) P)

theorem localMajorLowerPhase_totalDegree_le (n q : ℕ) (r : U → ℤ)
    (P : MvPolynomial U ℝ) (hP : P.totalDegree ≤ n + 1) :
    (localMajorLowerPhase n q r P).totalDegree ≤ n :=
  residueAffinePolynomial_totalDegree_le q r _ n (totalDegree_sub_top_component_le n P hP)

theorem localMajorLowerPhase_cancellation (n q : ℕ) (hq : 0 < q)
    (r v : U → ℤ) (P E R : MvPolynomial U ℝ)
    (htop : homogeneousComponent (n + 1) P = E + R)
    (hR : realPolynomialCoefficientGrid q R) :
    (Real.fourierChar (eval (fun i => ((r i + (q : ℤ) * v i : ℤ) : ℝ)) P) : ℂ) *
        star (Real.fourierChar (eval (fun i => (v i : ℝ))
          (localMajorLowerPhase n q r P)) : ℂ) =
      (Real.fourierChar
        (eval (fun i => ((r i + (q : ℤ) * v i : ℤ) : ℝ)) E +
          eval (fun i => (r i : ℝ)) R) : ℂ) := by
  rw [show localMajorLowerPhase n q r P =
    residueAffinePolynomial q r (P - homogeneousComponent (n + 1) P) from rfl,
    residueAffinePolynomial_eval, map_sub, htop, map_add]
  rw [← real_fourierChar_sub_star]
  rw [sub_sub_cancel]
  obtain ⟨k, hk⟩ := real_grid_polynomial_residue_difference R q hq hR r v
  have hr : eval (fun i => ((r i + (q : ℤ) * v i : ℤ) : ℝ)) R =
      eval (fun i => (r i : ℝ)) R + (k : ℝ) := by linarith
  rw [hr, ← add_assoc, real_fourierChar_add_integer]

theorem localMajorPhaseCorrelation [Fintype X]
    (p : FiniteProbabilityWeights X) (v : X → U → ℤ)
    (n q : ℕ) (hq : 0 < q) (r : U → ℤ)
    (P E R : MvPolynomial U ℝ) (hP : P.totalDegree ≤ n + 1)
    (htop : homogeneousComponent (n + 1) P = E + R)
    (hR : realPolynomialCoefficientGrid q R) (a ε : ℝ)
    (hslow : ∀ x, 0 < p.weight x →
      |eval (fun i => ((r i + (q : ℤ) * v x i : ℤ) : ℝ)) E - a| ≤ ε) :
    (localMajorLowerPhase n q r P).totalDegree ≤ n ∧
    1 - 2 * Real.pi * ε ≤ ‖p.complexMean (fun x =>
      (Real.fourierChar (eval (fun i => ((r i + (q : ℤ) * v x i : ℤ) : ℝ)) P) : ℂ) *
        star (Real.fourierChar (eval (fun i => (v x i : ℝ))
          (localMajorLowerPhase n q r P)) : ℂ))‖ := by
  refine ⟨localMajorLowerPhase_totalDegree_le n q r P hP, ?_⟩
  let f : X → ℂ := fun x =>
    (Real.fourierChar (eval (fun i => ((r i + (q : ℤ) * v x i : ℤ) : ℝ)) P) : ℂ) *
      star (Real.fourierChar (eval (fun i => (v x i : ℝ))
        (localMajorLowerPhase n q r P)) : ℂ)
  let c : ℂ := Real.fourierChar (a + eval (fun i => (r i : ℝ)) R)
  have hpoint (x : X) (hx : p.weight x ≠ 0) : ‖f x - c‖ ≤ 2 * Real.pi * ε := by
    dsimp only [f, c]
    rw [localMajorLowerPhase_cancellation n q hq r (v x) P E R htop hR]
    refine (real_fourierChar_norm_sub_le _ _).trans ?_
    rw [add_sub_add_right_eq_sub]
    exact mul_le_mul_of_nonneg_left (hslow x (lt_of_le_of_ne (p.nonneg x) (Ne.symm hx)))
      (by positivity)
  have havg := p.norm_complexMean_sub_le f (fun _ => c) (fun _ => 2 * Real.pi * ε) hpoint
  rw [p.complexMean_const, p.mean_const] at havg
  have hc : ‖c‖ = 1 := Circle.norm_coe _
  have hnorm := norm_le_norm_add_norm_sub (p.complexMean f) c
  rw [hc] at hnorm
  change 1 - 2 * Real.pi * ε ≤ ‖p.complexMean f‖
  linarith

end Erdos3


namespace Erdos3

open MvPolynomial
open scoped BigOperators

variable {σ τ : Type*}

noncomputable def floorIntegerPolynomial (D : MvPolynomial σ ℝ) : MvPolynomial σ ℤ :=
  .ofCoeff ((AddMonoidAlgebra.coeff D).mapRange Int.floor Int.floor_zero)

@[simp] theorem floorIntegerPolynomial_coeff (D : MvPolynomial σ ℝ) (a : σ →₀ ℕ) :
    (floorIntegerPolynomial D).coeff a = ⌊D.coeff a⌋ := rfl

noncomputable def fractionalCoefficientPolynomial (D : MvPolynomial σ ℝ) : MvPolynomial σ ℝ :=
  D - MvPolynomial.map (Int.castRingHom ℝ) (floorIntegerPolynomial D)

@[simp] theorem fractionalCoefficientPolynomial_coeff (D : MvPolynomial σ ℝ) (a : σ →₀ ℕ) :
    (fractionalCoefficientPolynomial D).coeff a = Int.fract (D.coeff a) := by
  simp only [fractionalCoefficientPolynomial, coeff_sub, coeff_map,
    floorIntegerPolynomial_coeff, Int.fract]
  rfl

theorem fractionalCoefficientPolynomial_bounds (D : MvPolynomial σ ℝ) (a : σ →₀ ℕ) :
    0 ≤ (fractionalCoefficientPolynomial D).coeff a ∧
      (fractionalCoefficientPolynomial D).coeff a < 1 := by
  rw [fractionalCoefficientPolynomial_coeff]
  exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

theorem floorIntegerPolynomial_isWeightedHomogeneous (D : MvPolynomial σ ℝ)
    (w : σ → ℕ) (d : ℕ) (hD : D.IsWeightedHomogeneous w d) :
    (floorIntegerPolynomial D).IsWeightedHomogeneous w d := by
  intro a ha
  apply hD
  intro hzero
  apply ha
  simp only [floorIntegerPolynomial_coeff, hzero, Int.floor_zero]

theorem fractionalCoefficientPolynomial_isWeightedHomogeneous (D : MvPolynomial σ ℝ)
    (w : σ → ℕ) (d : ℕ) (hD : D.IsWeightedHomogeneous w d) :
    (fractionalCoefficientPolynomial D).IsWeightedHomogeneous w d := by
  intro a ha
  apply hD
  intro hzero
  apply ha
  simp only [fractionalCoefficientPolynomial_coeff, hzero, Int.fract_zero]

theorem fractionalCoefficientPolynomial_mass_le_card (D : MvPolynomial σ ℝ) :
    realPolynomialMass (fractionalCoefficientPolynomial D) ≤
      ((fractionalCoefficientPolynomial D).support.card : ℝ) := by
  classical
  calc
    _ ≤ ∑ _a ∈ (fractionalCoefficientPolynomial D).support, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro a _
      rw [abs_of_nonneg (fractionalCoefficientPolynomial_bounds D a).1]
      exact (fractionalCoefficientPolynomial_bounds D a).2.le
    _ = _ := by simp

theorem fractionalCoefficientPolynomial_mass_le [Fintype σ] (D : MvPolynomial σ ℝ)
    (w : σ → ℕ) (hw : ∀ i, 0 < w i) (d : ℕ)
    (hD : D.IsWeightedHomogeneous w d) :
    realPolynomialMass (fractionalCoefficientPolynomial D) ≤
      ((Fintype.card σ : ℝ) + 1) ^ d := by
  refine (fractionalCoefficientPolynomial_mass_le_card D).trans ?_
  have hcard := boundedExponentSet_card_le (fractionalCoefficientPolynomial D).support d
    (fun a ha => (exponentSum_le_positive_weight w hw a).trans
      (le_of_eq (fractionalCoefficientPolynomial_isWeightedHomogeneous D w d hD
        (mem_support_iff.mp ha))))
  exact_mod_cast hcard

theorem floorIntegerPolynomial_add_fractionalCoefficientPolynomial (D : MvPolynomial σ ℝ) :
    MvPolynomial.map (Int.castRingHom ℝ) (floorIntegerPolynomial D) +
      fractionalCoefficientPolynomial D = D := by
  exact add_sub_cancel _ _

theorem fractionalCoefficientPolynomial_fourierChar (D : MvPolynomial σ ℝ) (z : σ → ℤ) :
    Real.fourierChar (eval (fun i => (z i : ℝ)) (fractionalCoefficientPolynomial D)) =
      Real.fourierChar (eval (fun i => (z i : ℝ)) D) := by
  have h := congrArg (fun P => Real.fourierChar (eval (fun i => (z i : ℝ)) P))
    (floorIntegerPolynomial_add_fractionalCoefficientPolynomial D)
  have hz : Real.fourierChar ((eval z (floorIntegerPolynomial D) : ℤ) : ℝ) = 1 := by
    apply Subtype.ext
    change (Circle.exp (2 * Real.pi * ((eval z (floorIntegerPolynomial D) : ℤ) : ℝ)) : ℂ) = 1
    rw [mul_comm (2 * Real.pi), Circle.exp_intCast_mul]
    simp
  simpa only [map_add, eval_integer_polynomial_real, Real.fourierChar.map_add_eq_mul,
    hz, one_mul] using h

theorem fractionalCoefficientPolynomial_integer_substitution (D : MvPolynomial σ ℝ)
    (f : σ → MvPolynomial τ ℤ) :
    aeval (fun i => MvPolynomial.map (Int.castRingHom ℝ) (f i)) D =
      MvPolynomial.map (Int.castRingHom ℝ)
        (eval₂ C f (floorIntegerPolynomial D)) +
      aeval (fun i => MvPolynomial.map (Int.castRingHom ℝ) (f i))
        (fractionalCoefficientPolynomial D) := by
  conv_lhs => rw [← floorIntegerPolynomial_add_fractionalCoefficientPolynomial D]
  rw [map_add]
  congr 1
  exact (map_eval₂ (Int.castRingHom ℝ) f (floorIntegerPolynomial D)).symm

theorem fractionalCoefficientPolynomial_integer_leading_component (D : MvPolynomial σ ℝ)
    (f : σ → MvPolynomial τ ℤ) (v : τ → ℕ) (n : ℕ) :
    weightedHomogeneousComponent v n
        (aeval (fun i => MvPolynomial.map (Int.castRingHom ℝ) (f i)) D) =
      MvPolynomial.map (Int.castRingHom ℝ)
        (weightedHomogeneousComponent v n (eval₂ C f (floorIntegerPolynomial D))) +
      weightedHomogeneousComponent v n
        (aeval (fun i => MvPolynomial.map (Int.castRingHom ℝ) (f i))
          (fractionalCoefficientPolynomial D)) := by
  classical
  rw [fractionalCoefficientPolynomial_integer_substitution, map_add]
  congr 1
  ext a
  simp only [coeff_weightedHomogeneousComponent, coeff_map]
  split_ifs <;> simp

theorem exists_major_polynomial_coefficient_reduction [Fintype σ]
    (D : MvPolynomial σ ℝ) (w : σ → ℕ) (hw : ∀ i, 0 < w i) (d : ℕ)
    (hD : D.IsWeightedHomogeneous w d) :
    ∃ (I : MvPolynomial σ ℤ) (Dred : MvPolynomial σ ℝ),
      I.IsWeightedHomogeneous w d ∧ Dred.IsWeightedHomogeneous w d ∧
      D = MvPolynomial.map (Int.castRingHom ℝ) I + Dred ∧
      (∀ a, 0 ≤ Dred.coeff a ∧ Dred.coeff a < 1) ∧
      realPolynomialMass Dred ≤ ((Fintype.card σ : ℝ) + 1) ^ d ∧
      ∀ z : σ → ℤ, Real.fourierChar (eval (fun i => (z i : ℝ)) Dred) =
        Real.fourierChar (eval (fun i => (z i : ℝ)) D) :=
  ⟨floorIntegerPolynomial D, fractionalCoefficientPolynomial D,
    floorIntegerPolynomial_isWeightedHomogeneous D w d hD,
    fractionalCoefficientPolynomial_isWeightedHomogeneous D w d hD,
    (floorIntegerPolynomial_add_fractionalCoefficientPolynomial D).symm,
    fractionalCoefficientPolynomial_bounds D,
    fractionalCoefficientPolynomial_mass_le D w hw d hD,
    fractionalCoefficientPolynomial_fourierChar D⟩

end Erdos3


namespace Erdos3

open MvPolynomial

variable {B : Type*}

theorem translationPhaseArgument_left_increment
    (D₀ : MvPolynomial B ℝ) (z g : PolynomialTranslationGroupOver ℝ B) (β : B → ℝ) :
    translationPhaseArgument D₀ (z * g) β - translationPhaseArgument D₀ g β =
      eval (β - g.base) z.polynomial +
        (eval (β - g.base - z.base) D₀ - eval (β - g.base) D₀) := by
  simp only [translationPhaseArgument, PolynomialTranslationGroupOver.polynomial_mul,
    PolynomialTranslationGroupOver.base_mul, map_add, polynomialTranslate_eval_ring]
  have h₁ : (fun i => β i + (-g.base) i) = β - g.base := by ext i; simp [sub_eq_add_neg]
  have h₂ : β - (z.base + g.base) = β - g.base - z.base := by abel
  rw [h₁, h₂]
  ring

theorem translationPhaseArgument_left_increment_bound [Fintype B]
    (D₀ : MvPolynomial B ℝ) (z g : PolynomialTranslationGroupOver ℝ B)
    (β : B → ℝ) {d : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    (hdegree : D₀.totalDegree ≤ d)
    (hres : ∀ i, |β i - g.base i| ≤ 1)
    (hnew : ∀ i, |β i - g.base i - z.base i| ≤ 1)
    (hbase : ∀ i, |z.base i| ≤ ε) (hmass : realPolynomialMass z.polynomial ≤ ε) :
    |translationPhaseArgument D₀ (z * g) β - translationPhaseArgument D₀ g β| ≤
      (1 + realPolynomialMass D₀ * Fintype.card B * d) * ε := by
  rw [translationPhaseArgument_left_increment]
  have hp : |eval (β - g.base) z.polynomial| ≤ ε := by
    have h := abs_aeval_le_mass_box z.polynomial (β - g.base) (B := 1)
      le_rfl hres (n := z.polynomial.totalDegree) le_rfl
    simpa only [MvPolynomial.aeval_eq_eval, one_pow, mul_one] using h.trans (by simpa only [MvPolynomial.aeval_eq_eval, one_pow, mul_one] using hmass)
  have hd : |eval (β - g.base - z.base) D₀ - eval (β - g.base) D₀| ≤
      realPolynomialMass D₀ * Fintype.card B * d * ε := by
    have hdiff (i : B) : |(β - g.base - z.base) i - (β - g.base) i| ≤ ε := by
      change |β i - g.base i - z.base i - (β i - g.base i)| ≤ ε
      rw [show β i - g.base i - z.base i - (β i - g.base i) = -z.base i by ring, abs_neg]
      exact hbase i
    have h := abs_aeval_sub_aeval_mass_box_bound D₀
      (β - g.base - z.base) (β - g.base) (B := 1) le_rfl hε hnew hres hdiff hdegree
    simpa only [MvPolynomial.aeval_eq_eval, one_pow, mul_one] using h
  calc
    _ ≤ |eval (β - g.base) z.polynomial| +
      |eval (β - g.base - z.base) D₀ - eval (β - g.base) D₀| := abs_add_le _ _
    _ ≤ ε + realPolynomialMass D₀ * Fintype.card B * d * ε := add_le_add hp hd
    _ = _ := by ring

end Erdos3


namespace Erdos3

open MvPolynomial

variable {B : Type*}

noncomputable def integerPolynomialTranslationSubgroup :
    Subgroup (PolynomialTranslationGroupOver ℝ B) :=
  (PolynomialTranslationGroupOver.map (B := B) (Int.castRingHom ℝ)).range

theorem translationPhaseFunction_integerSubgroup
    (D₀ : MvPolynomial B ℝ) (g γ : PolynomialTranslationGroupOver ℝ B)
    (hγ : γ ∈ integerPolynomialTranslationSubgroup) :
    translationPhaseFunction D₀ (g * γ) = translationPhaseFunction D₀ g := by
  obtain ⟨γ, rfl⟩ := hγ
  exact translationPhaseFunction_integer_lattice D₀ g γ.base γ.polynomial

noncomputable def translationQuotientPhase (D₀ : MvPolynomial B ℝ) :
    (PolynomialTranslationGroupOver ℝ B ⧸ integerPolynomialTranslationSubgroup) → ℂ :=
  Quotient.lift (translationPhaseFunction D₀) (fun g h hgh => by
    have hi := translationPhaseFunction_integerSubgroup D₀ g (g⁻¹ * h)
      (QuotientGroup.leftRel_apply.mp hgh)
    simpa only [mul_inv_cancel_left] using hi.symm)

@[simp] theorem translationQuotientPhase_mk (D₀ : MvPolynomial B ℝ)
    (g : PolynomialTranslationGroupOver ℝ B) :
    translationQuotientPhase D₀ (QuotientGroup.mk g) = translationPhaseFunction D₀ g := rfl

theorem translationQuotientPhase_norm (D₀ : MvPolynomial B ℝ)
    (g : PolynomialTranslationGroupOver ℝ B ⧸ integerPolynomialTranslationSubgroup) :
    ‖translationQuotientPhase D₀ g‖ = 1 := by
  refine Quotient.inductionOn g ?_
  exact translationPhaseFunction_norm D₀

theorem translationPhaseFunction_cover
    (Γ : Subgroup (PolynomialTranslationGroupOver ℝ B))
    (hΓ : Γ ≤ integerPolynomialTranslationSubgroup)
    (D₀ : MvPolynomial B ℝ) (g γ : PolynomialTranslationGroupOver ℝ B)
    (hγ : γ ∈ Γ) : translationPhaseFunction D₀ (g * γ) = translationPhaseFunction D₀ g :=
  translationPhaseFunction_integerSubgroup D₀ g γ (hΓ hγ)

end Erdos3

end OAI
