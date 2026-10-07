import OAI.Combinatorics.Progressions.Lattices.BufferedIntegerLift
import OAI.Combinatorics.Progressions.Lattices.WeightedTranslationResidueLattice

namespace OAI

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators

variable {m : ℕ}

noncomputable def bufferedTranslationTerm (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (g : PolynomialTranslationGroupOver ℝ (Fin m)) (β : Fin m → ℤ) : ℂ :=
  (Ψ.value (fun i => g.base i - (β i : ℝ)) : ℂ) *
    (Real.fourierChar (translationPhaseArgument D₀ g (fun i => (β i : ℝ))) : ℂ)

noncomputable def bufferedTranslationPhase (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (g : PolynomialTranslationGroupOver ℝ (Fin m)) : ℂ :=
  ∑' β : Fin m → ℤ, bufferedTranslationTerm Ψ D₀ g β

theorem bufferedTranslationTerm_nonzero_iff (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (g : PolynomialTranslationGroupOver ℝ (Fin m)) (β : Fin m → ℤ) :
    bufferedTranslationTerm Ψ D₀ g β ≠ 0 ↔
      Ψ.value (fun i => g.base i - (β i : ℝ)) ≠ 0 := by
  simp only [bufferedTranslationTerm, ne_eq, mul_eq_zero, Complex.ofReal_eq_zero,
    Circle.coe_ne_zero, or_false]

theorem bufferedTranslationTerm_unique (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (g : PolynomialTranslationGroupOver ℝ (Fin m)) (β γ : Fin m → ℤ)
    (hβ : bufferedTranslationTerm Ψ D₀ g β ≠ 0)
    (hγ : bufferedTranslationTerm Ψ D₀ g γ ≠ 0) : β = γ := by
  have hβ' := (bufferedTranslationTerm_nonzero_iff Ψ D₀ g β).mp hβ
  have hγ' := (bufferedTranslationTerm_nonzero_iff Ψ D₀ g γ).mp hγ
  exact (Ψ.buffered_lift_unique g.base β γ
    (fun i => (Ψ.support _ hβ' i).trans (by norm_num)) hγ').symm

theorem bufferedTranslationPhase_eq_chart (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (g : PolynomialTranslationGroupOver ℝ (Fin m)) (β : Fin m → ℤ)
    (hβ : ∀ i, |g.base i - (β i : ℝ)| ≤ 1 / 2) :
    bufferedTranslationPhase Ψ D₀ g = bufferedTranslationTerm Ψ D₀ g β := by
  classical
  apply tsum_eq_single β
  intro γ hγ
  by_contra hn
  exact hγ (Ψ.buffered_lift_unique g.base β γ hβ
    ((bufferedTranslationTerm_nonzero_iff Ψ D₀ g γ).mp hn))

theorem bufferedTranslationPhase_eq_on_support (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (g : PolynomialTranslationGroupOver ℝ (Fin m)) (β : Fin m → ℤ)
    (hβ : Ψ.value (fun i => g.base i - (β i : ℝ)) ≠ 0) :
    bufferedTranslationPhase Ψ D₀ g = bufferedTranslationTerm Ψ D₀ g β :=
  bufferedTranslationPhase_eq_chart Ψ D₀ g β
    (fun i => (Ψ.support _ hβ i).trans (by norm_num))

theorem bufferedTranslationPhase_norm_le_one (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (g : PolynomialTranslationGroupOver ℝ (Fin m)) :
    ‖bufferedTranslationPhase Ψ D₀ g‖ ≤ 1 := by
  rw [bufferedTranslationPhase_eq_chart Ψ D₀ g (nearestIntegerLift g.base)
    (nearestIntegerLift_close g.base)]
  simp only [bufferedTranslationTerm, norm_mul, Circle.norm_coe, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Ψ.nonneg _)]
  exact Ψ.le_one _

theorem bufferedTranslationPhase_eq_phaseFunction (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (g : PolynomialTranslationGroupOver ℝ (Fin m)) :
    bufferedTranslationPhase Ψ D₀ g =
      (Ψ.value (fun i => g.base i - (⌊g.base i + 1 / 2⌋ : ℝ)) : ℂ) *
        translationPhaseFunction D₀ g := by
  apply bufferedTranslationPhase_eq_chart Ψ D₀ g (fun i => ⌊g.base i + 1 / 2⌋)
  intro i
  apply abs_le.mpr
  have hl := Int.floor_le (g.base i + 1 / 2)
  have hu := Int.lt_floor_add_one (g.base i + 1 / 2)
  constructor <;> linarith

theorem bufferedTranslationPhase_majorSymbol {U : Type*} (Ψ : PatchKernel m)
    (D : MvPolynomial (U ⊕ Fin m) ℝ) (D₀ : MvPolynomial (Fin m) ℝ)
    (A : Fin m → MvPolynomial U ℝ) (u : U → ℝ) (β : Fin m → ℤ)
    (hβ : ∀ i, |eval u (A i) - (β i : ℝ)| ≤ 1 / 2) :
    bufferedTranslationPhase Ψ D₀ (algebraicMajorSymbol D D₀ A u) =
      (Ψ.value (fun i => eval u (A i) - (β i : ℝ)) : ℂ) *
        (Real.fourierChar (eval (Sum.elim u (fun i => (β i : ℝ))) D) : ℂ) := by
  rw [bufferedTranslationPhase_eq_chart Ψ D₀ _ β hβ]
  unfold bufferedTranslationTerm
  rw [translationPhaseArgument_majorSymbol]
  rfl

theorem bufferedTranslationPhase_majorSymbol_on_support {U : Type*} (Ψ : PatchKernel m)
    (D : MvPolynomial (U ⊕ Fin m) ℝ) (D₀ : MvPolynomial (Fin m) ℝ)
    (A : Fin m → MvPolynomial U ℝ) (u : U → ℝ) (β : Fin m → ℤ)
    (hβ : Ψ.value (fun i => eval u (A i) - (β i : ℝ)) ≠ 0) :
    bufferedTranslationPhase Ψ D₀ (algebraicMajorSymbol D D₀ A u) =
      (Ψ.value (fun i => eval u (A i) - (β i : ℝ)) : ℂ) *
        (Real.fourierChar (eval (Sum.elim u (fun i => (β i : ℝ))) D) : ℂ) :=
  bufferedTranslationPhase_majorSymbol Ψ D D₀ A u β
    (fun i => (Ψ.support _ hβ i).trans (by norm_num))

theorem bufferedTranslationTerm_integer_lattice (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (g : PolynomialTranslationGroupOver ℝ (Fin m))
    (γ : PolynomialTranslationGroupOver ℤ (Fin m)) (β : Fin m → ℤ) :
    bufferedTranslationTerm Ψ D₀
      (g * PolynomialTranslationGroupOver.map (Int.castRingHom ℝ) γ) (β + γ.base) =
        bufferedTranslationTerm Ψ D₀ g β := by
  unfold bufferedTranslationTerm
  have hweight : (fun i =>
      (g * PolynomialTranslationGroupOver.map (Int.castRingHom ℝ) γ).base i -
        ((β + γ.base) i : ℝ)) = (fun i => g.base i - (β i : ℝ)) := by
    funext i
    simp only [PolynomialTranslationGroupOver.base_mul, Pi.add_apply,
      PolynomialTranslationGroupOver.map_base, Int.cast_add]
    change g.base i + (γ.base i : ℝ) - ((β i : ℝ) + (γ.base i : ℝ)) = _
    ring
  rw [hweight]
  congr 1
  exact translationPhaseArgument_fourier_integer D₀ g γ.base β γ.polynomial

theorem bufferedTranslationPhase_integer_lattice (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (g : PolynomialTranslationGroupOver ℝ (Fin m))
    (γ : PolynomialTranslationGroupOver ℤ (Fin m)) :
    bufferedTranslationPhase Ψ D₀
      (g * PolynomialTranslationGroupOver.map (Int.castRingHom ℝ) γ) =
        bufferedTranslationPhase Ψ D₀ g := by
  unfold bufferedTranslationPhase
  have he := (Equiv.addRight γ.base).tsum_eq (bufferedTranslationTerm Ψ D₀
    (g * PolynomialTranslationGroupOver.map (Int.castRingHom ℝ) γ))
  refine he.symm.trans (tsum_congr fun β => ?_)
  exact bufferedTranslationTerm_integer_lattice Ψ D₀ g γ β

theorem bufferedTranslationPhase_integerSubgroup (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (g γ : PolynomialTranslationGroupOver ℝ (Fin m))
    (hγ : γ ∈ integerPolynomialTranslationSubgroup) :
    bufferedTranslationPhase Ψ D₀ (g * γ) = bufferedTranslationPhase Ψ D₀ g := by
  obtain ⟨γ, rfl⟩ := hγ
  exact bufferedTranslationPhase_integer_lattice Ψ D₀ g γ

theorem bufferedTranslationPhase_central (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (g : PolynomialTranslationGroupOver ℝ (Fin m)) (a : ℝ) :
    bufferedTranslationPhase Ψ D₀ (g * ⟨0, C a⟩) =
      bufferedTranslationPhase Ψ D₀ g * (Real.fourierChar a : ℂ) := by
  rw [bufferedTranslationPhase_eq_phaseFunction, bufferedTranslationPhase_eq_phaseFunction,
    translationPhaseFunction_central]
  have hb : (g * (⟨0, C a⟩ : PolynomialTranslationGroupOver ℝ (Fin m))).base = g.base := by simp
  rw [hb, mul_assoc]

noncomputable def bufferedTranslationQuotientPhase (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ) :
    (PolynomialTranslationGroupOver ℝ (Fin m) ⧸ integerPolynomialTranslationSubgroup) → ℂ :=
  Quotient.lift (bufferedTranslationPhase Ψ D₀) (fun g h hgh => by
    have hi := bufferedTranslationPhase_integerSubgroup Ψ D₀ g (g⁻¹ * h)
      (QuotientGroup.leftRel_apply.mp hgh)
    simpa only [mul_inv_cancel_left] using hi.symm)

@[simp] theorem bufferedTranslationQuotientPhase_mk (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ) (g : PolynomialTranslationGroupOver ℝ (Fin m)) :
    bufferedTranslationQuotientPhase Ψ D₀ (QuotientGroup.mk g) = bufferedTranslationPhase Ψ D₀ g := rfl

theorem bufferedTranslationQuotientPhase_norm_le_one (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (g : PolynomialTranslationGroupOver ℝ (Fin m) ⧸ integerPolynomialTranslationSubgroup) :
    ‖bufferedTranslationQuotientPhase Ψ D₀ g‖ ≤ 1 := by
  refine Quotient.inductionOn g ?_
  exact bufferedTranslationPhase_norm_le_one Ψ D₀

end Erdos3

end

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators

variable {m : ℕ} (M : ℕ)

noncomputable def twistedBufferedTranslationTerm (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
    (g : PolynomialTranslationGroupOver ℝ (Fin m)) (β : Fin m → ℤ) : ℂ :=
  T (fun i => g.base i - (β i : ℝ)) (fun i => (β i : ZMod M)) *
    bufferedTranslationTerm Ψ D₀ g β

noncomputable def twistedBufferedTranslationPhase (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
    (g : PolynomialTranslationGroupOver ℝ (Fin m)) : ℂ :=
  ∑' β : Fin m → ℤ, twistedBufferedTranslationTerm M Ψ D₀ T g β

theorem twistedBufferedTranslationTerm_unique (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
    (g : PolynomialTranslationGroupOver ℝ (Fin m)) (β γ : Fin m → ℤ)
    (hβ : twistedBufferedTranslationTerm M Ψ D₀ T g β ≠ 0)
    (hγ : twistedBufferedTranslationTerm M Ψ D₀ T g γ ≠ 0) : β = γ :=
  bufferedTranslationTerm_unique Ψ D₀ g β γ
    (mul_ne_zero_iff.mp hβ).2 (mul_ne_zero_iff.mp hγ).2

theorem twistedBufferedTranslationPhase_eq_chart (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
    (g : PolynomialTranslationGroupOver ℝ (Fin m)) (β : Fin m → ℤ)
    (hβ : ∀ i, |g.base i - (β i : ℝ)| ≤ 1 / 2) :
    twistedBufferedTranslationPhase M Ψ D₀ T g = twistedBufferedTranslationTerm M Ψ D₀ T g β := by
  classical
  apply tsum_eq_single β
  intro γ hγ
  by_contra hn
  have hb := (mul_ne_zero_iff.mp hn).2
  exact hγ (Ψ.buffered_lift_unique g.base β γ hβ
    ((bufferedTranslationTerm_nonzero_iff Ψ D₀ g γ).mp hb))

theorem twistedBufferedTranslationTerm_norm_le_one (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ) (hT : ∀ x r, ‖T x r‖ ≤ 1)
    (g : PolynomialTranslationGroupOver ℝ (Fin m)) (β : Fin m → ℤ) :
    ‖twistedBufferedTranslationTerm M Ψ D₀ T g β‖ ≤ 1 := by
  have hb : ‖bufferedTranslationTerm Ψ D₀ g β‖ ≤ 1 := by
    simp only [bufferedTranslationTerm, norm_mul, Circle.norm_coe, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Ψ.nonneg _)]
    exact Ψ.le_one _
  rw [twistedBufferedTranslationTerm, norm_mul]
  exact (mul_le_mul (hT _ _) hb (norm_nonneg _) (by norm_num)).trans (by norm_num)

theorem twistedBufferedTranslationPhase_norm_le_one (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ) (hT : ∀ x r, ‖T x r‖ ≤ 1)
    (g : PolynomialTranslationGroupOver ℝ (Fin m)) :
    ‖twistedBufferedTranslationPhase M Ψ D₀ T g‖ ≤ 1 := by
  rw [twistedBufferedTranslationPhase_eq_chart M Ψ D₀ T g (nearestIntegerLift g.base)
    (nearestIntegerLift_close g.base)]
  exact twistedBufferedTranslationTerm_norm_le_one M Ψ D₀ T hT g _

theorem twistedBufferedTranslationPhase_majorSymbol {U : Type*} (Ψ : PatchKernel m)
    (D : MvPolynomial (U ⊕ Fin m) ℝ) (D₀ : MvPolynomial (Fin m) ℝ)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
    (A : Fin m → MvPolynomial U ℝ) (u : U → ℝ) (β : Fin m → ℤ)
    (hβ : ∀ i, |eval u (A i) - (β i : ℝ)| ≤ 1 / 2) :
    twistedBufferedTranslationPhase M Ψ D₀ T (algebraicMajorSymbol D D₀ A u) =
      T (fun i => eval u (A i) - (β i : ℝ)) (fun i => (β i : ZMod M)) *
        (Ψ.value (fun i => eval u (A i) - (β i : ℝ)) : ℂ) *
        (Real.fourierChar (eval (Sum.elim u (fun i => (β i : ℝ))) D) : ℂ) := by
  rw [twistedBufferedTranslationPhase_eq_chart M Ψ D₀ T _ β hβ]
  unfold twistedBufferedTranslationTerm bufferedTranslationTerm
  rw [translationPhaseArgument_majorSymbol, mul_assoc]
  rfl

theorem twistedBufferedTranslationTerm_integer_lattice (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
    (g : PolynomialTranslationGroupOver ℝ (Fin m))
    (γ : PolynomialTranslationGroupOver ℤ (Fin m))
    (hγ : γ ∈ integerTranslationResidueSubgroup M) (β : Fin m → ℤ) :
    twistedBufferedTranslationTerm M Ψ D₀ T
      (g * PolynomialTranslationGroupOver.map (Int.castRingHom ℝ) γ) (β + γ.base) =
        twistedBufferedTranslationTerm M Ψ D₀ T g β := by
  rw [twistedBufferedTranslationTerm, bufferedTranslationTerm_integer_lattice]
  have hx : (fun i =>
      (g * PolynomialTranslationGroupOver.map (Int.castRingHom ℝ) γ).base i -
        ((β + γ.base) i : ℝ)) = (fun i => g.base i - (β i : ℝ)) := by
    funext i
    simp only [PolynomialTranslationGroupOver.base_mul, Pi.add_apply,
      PolynomialTranslationGroupOver.map_base, Int.cast_add]
    change g.base i + (γ.base i : ℝ) - ((β i : ℝ) + (γ.base i : ℝ)) = _
    ring
  have hr : (fun i => ((β + γ.base) i : ZMod M)) = (fun i => (β i : ZMod M)) := by
    funext i
    simp only [Pi.add_apply, Int.cast_add, hγ i, add_zero]
  rw [hx, hr]
  rfl

theorem twistedBufferedTranslationPhase_integer_lattice (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
    (g : PolynomialTranslationGroupOver ℝ (Fin m))
    (γ : PolynomialTranslationGroupOver ℤ (Fin m))
    (hγ : γ ∈ integerTranslationResidueSubgroup M) :
    twistedBufferedTranslationPhase M Ψ D₀ T
      (g * PolynomialTranslationGroupOver.map (Int.castRingHom ℝ) γ) =
        twistedBufferedTranslationPhase M Ψ D₀ T g := by
  unfold twistedBufferedTranslationPhase
  have he := (Equiv.addRight γ.base).tsum_eq (twistedBufferedTranslationTerm M Ψ D₀ T
    (g * PolynomialTranslationGroupOver.map (Int.castRingHom ℝ) γ))
  exact he.symm.trans (tsum_congr fun β =>
    twistedBufferedTranslationTerm_integer_lattice M Ψ D₀ T g γ hγ β)

theorem twistedBufferedTranslationPhase_residueCover (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
    (g γ : PolynomialTranslationGroupOver ℝ (Fin m))
    (hγ : γ ∈ integerPolynomialTranslationResidueCover M) :
    twistedBufferedTranslationPhase M Ψ D₀ T (g * γ) =
      twistedBufferedTranslationPhase M Ψ D₀ T g := by
  obtain ⟨γ, hγ, rfl⟩ := hγ
  exact twistedBufferedTranslationPhase_integer_lattice M Ψ D₀ T g γ hγ

theorem twistedBufferedTranslationTerm_central (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
    (g : PolynomialTranslationGroupOver ℝ (Fin m)) (a : ℝ) (β : Fin m → ℤ) :
    twistedBufferedTranslationTerm M Ψ D₀ T (g * ⟨0, C a⟩) β =
      twistedBufferedTranslationTerm M Ψ D₀ T g β * (Real.fourierChar a : ℂ) := by
  unfold twistedBufferedTranslationTerm bufferedTranslationTerm
  have hb : (g * (⟨0, C a⟩ : PolynomialTranslationGroupOver ℝ (Fin m))).base = g.base := by simp
  rw [hb]
  have ha := translationPhaseArgument_mul D₀ g
    (⟨0, C a⟩ : PolynomialTranslationGroupOver ℝ (Fin m)) (fun i => (β i : ℝ))
  simp only [add_zero, eval_C] at ha
  rw [ha, Real.fourierChar.map_add_eq_mul]
  simp only [Circle.coe_mul, mul_assoc]

theorem twistedBufferedTranslationPhase_central (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
    (g : PolynomialTranslationGroupOver ℝ (Fin m)) (a : ℝ) :
    twistedBufferedTranslationPhase M Ψ D₀ T (g * ⟨0, C a⟩) =
      twistedBufferedTranslationPhase M Ψ D₀ T g * (Real.fourierChar a : ℂ) := by
  unfold twistedBufferedTranslationPhase
  simp_rw [twistedBufferedTranslationTerm_central]
  exact tsum_mul_right

noncomputable def twistedBufferedTranslationQuotientPhase (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ) :
    (PolynomialTranslationGroupOver ℝ (Fin m) ⧸ integerPolynomialTranslationResidueCover M) → ℂ :=
  Quotient.lift (twistedBufferedTranslationPhase M Ψ D₀ T) (fun g h hgh => by
    have hi := twistedBufferedTranslationPhase_residueCover M Ψ D₀ T g (g⁻¹ * h)
      (QuotientGroup.leftRel_apply.mp hgh)
    simpa only [mul_inv_cancel_left] using hi.symm)

@[simp] theorem twistedBufferedTranslationQuotientPhase_mk (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
    (g : PolynomialTranslationGroupOver ℝ (Fin m)) :
    twistedBufferedTranslationQuotientPhase M Ψ D₀ T (QuotientGroup.mk g) =
      twistedBufferedTranslationPhase M Ψ D₀ T g := rfl

theorem twistedBufferedTranslationQuotientPhase_norm_le_one (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ) (hT : ∀ x r, ‖T x r‖ ≤ 1)
    (g : PolynomialTranslationGroupOver ℝ (Fin m) ⧸ integerPolynomialTranslationResidueCover M) :
    ‖twistedBufferedTranslationQuotientPhase M Ψ D₀ T g‖ ≤ 1 := by
  refine Quotient.inductionOn g ?_
  exact twistedBufferedTranslationPhase_norm_le_one M Ψ D₀ T hT

end Erdos3

end

end OAI
