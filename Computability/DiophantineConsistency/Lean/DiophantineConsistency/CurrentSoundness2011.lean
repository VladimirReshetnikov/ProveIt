import DiophantineConsistency.CurrentMarkedWindow2011
import DiophantineConsistency.WangTiles942Soundness
import DiophantineConsistency.DecimalMachineZFC

/-!
# Consistency excludes positive zeros of the actual maintained equation

The literal polynomial supplies its original marked tile word. The actual
tile language forces a halt of the literal decimal machine, whose existing
closed endpoint yields a syntactic ZFC refutation. This proves the forward
consistency-to-unsolvability implication, not its converse or an internal-ZFC
formalization. The three accepted thirteen-variable forms inherit it through
their already proved arithmetic restoration maps.
-/

namespace DiophantineConsistency.CurrentSoundness2011

open SetTheory SetTheory.BusyBeaver.ZFC LeanProofs.BoundedZFCConsistency
open CurrentPolynomialWindow2011 CurrentCarrierArithmetic2011

set_option Elab.async false
set_option maxRecDepth 10000

/-- A zero of the literal fourteen-variable polynomial yields a halt of
the actual blank machine. No window, tiling, run or calibration is assumed. -/
theorem polynomial_zero_blank_halts (v : Fin 14 → ℤ) (hv : ∀ j, 0 < v j)
    (hz : MvPolynomial.eval v polynomial = 0) :
    KDenseBridge.BlankHalts DecimalMachine215.machine := by
  obtain ⟨N,hN,hw⟩ := CurrentMarkedWindow2011.polynomial_zero_marked_window v hv hz
  letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  letI : NeZero (N*2011) := ⟨Nat.ne_of_gt (Nat.mul_pos hN (by decide))⟩
  obtain ⟨x,c,carry,digits,_,a,_,ha,_,_⟩ := hw
  exact WangTiles942Soundness.marked_blank_halts ha

/-- The existing syntactic axiom predicate and literal false formula are
unchanged; this conclusion is not a replacement consistency predicate. -/
theorem polynomial_zero_zfc_refutation (v : Fin 14 → ℤ) (hv : ∀ j, 0 < v j)
    (hz : MvPolynomial.eval v polynomial = 0) : BProv ZFCax_s [] Form.fBot :=
  DecimalMachineZFC.blank_halts_iff_zfc_refutation.mp (polynomial_zero_blank_halts v hv hz)

theorem conZFC_no_polynomial_zero (hc : ConZFC) (v : Fin 14 → ℤ)
    (hv : ∀ j, 0 < v j) : MvPolynomial.eval v polynomial ≠ 0 := by
  intro hz
  exact (DecimalMachineZFC.blank_nonhalting_iff_conZFC.mpr hc)
    (polynomial_zero_blank_halts v hv hz)

/-- Existence formulation for the maintained14-variable polynomial. -/
theorem conZFC_no_positive_zero (hc : ConZFC) : ¬ PositiveZero polynomial := by
  rintro ⟨v,hv,hz⟩
  exact conZFC_no_polynomial_zero hc v hv hz

private theorem polynomial65_eq :
    polynomial65 (CurrentKernel2011.K : ℤ) = polynomial := rfl

/-- All three literal thirteen-variable frontiers have the same fixed
kernel and masks; no new controller or machine premise is introduced. -/
theorem conZFC_no_thirteen_positive_zero (hc : ConZFC) :
    ¬ PositiveZero (polynomial69 (CurrentKernel2011.K : ℤ)) ∧
    ¬ PositiveZero (polynomial70 (CurrentKernel2011.K : ℤ)) ∧
    ¬ PositiveZero (polynomial71 (CurrentKernel2011.K : ℤ)) := by
  have hK : (0 : ℤ) < (CurrentKernel2011.K : ℤ) := by
    exact_mod_cast CurrentKernel2011.K_pos
  have h65 : ¬ PositiveZero (polynomial65 (CurrentKernel2011.K : ℤ)) := by
    rw [polynomial65_eq]
    exact conZFC_no_positive_zero hc
  have h69 : ¬ PositiveZero (polynomial69 (CurrentKernel2011.K : ℤ)) :=
    fun h => h65 ((positive_zero_65_iff_69 _ hK).mpr h)
  have h70 : ¬ PositiveZero (polynomial70 (CurrentKernel2011.K : ℤ)) :=
    fun h => h69 ((positive_zero_69_iff_70 _).mpr h)
  exact ⟨h69,h70,fun h => h70 ((positive_zero_70_iff_71 _).mpr h)⟩

end DiophantineConsistency.CurrentSoundness2011
