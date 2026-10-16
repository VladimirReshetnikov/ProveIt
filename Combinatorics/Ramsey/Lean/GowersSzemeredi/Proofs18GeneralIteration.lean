import GowersSzemeredi.Proofs18GeneralIterationStep
import GowersSzemeredi.Proofs18DensityIterationGrowth

/-! Complete finite iteration from an explicit function discrepancy bound.
The resulting closed threshold exposes exactly what remains to be compared
with the source's quantitative Szemeredi threshold. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def intervalDiscrepancyClosedThreshold (k : Nat) (delta beta sigma T : Real) : Real :=
  densityIterationClosedThreshold (intervalDiscrepancyStepThreshold k delta beta T)
    (beta / (8 * boundaryRefinementConstant (beta / 64))) (sigma / 16) ⌈(beta / 8)⁻¹⌉₊

/-- Iterate with fixed constants until the density would exceed one.
The only unproved input is the displayed function discrepancy hypothesis. -/
theorem FunctionDiscrepancyBound.interval_szemeredi_closed
    {k : Nat} {delta beta sigma T : Real} (hk : 2 ≤ k) (hδ : 0 < delta)
    (hβ : 0 < beta) (hσ : 0 < sigma)
    (hbound : FunctionDiscrepancyBound (k - 2) (intervalUniformityParameter delta k) beta sigma T)
    (L : Nat) (hL : intervalDiscrepancyClosedThreshold k delta beta sigma T ≤ L)
    (B : Finset (Fin L)) (hcard : delta * L ≤ B.card) : HasNatAP (B.image Fin.val) k := by
  have hC : 0 < boundaryRefinementConstant (beta / 64) := section5LocalRefinementConstant_pos _ _
  have hg : 0 < beta / 8 := by positivity
  have hc : 0 < beta / (8 * boundaryRefinementConstant (beta / 64)) := by positivity
  have hρ : 0 < sigma / 16 := by positivity
  have hsteps : (beta / 8)⁻¹ ≤ (⌈(beta / 8)⁻¹⌉₊ : Real) := Nat.le_ceil _
  have hm := mul_le_mul_of_nonneg_right hsteps hg.le
  rw [inv_mul_cancel₀ hg.ne'] at hm
  exact hasNatAP_of_density_iteration hg.le hc hρ
    (hbound.interval_density_step hk hδ hβ hσ) _ L
    ((densityIterationThreshold_le_closed hc hρ _).trans hL) B delta le_rfl hcard (by linarith)

/-- Transfer a theorem on Fin N to the source's interval {1,...,N} without
changing density or length thresholds. -/
theorem hasNatAP_Icc_of_fin_interval {N k : Nat} {delta : Real}
    (hfin : ∀ B : Finset (Fin N), delta * N ≤ B.card → HasNatAP (B.image Fin.val) k)
    (A : Finset Nat) (hA : A ⊆ Finset.Icc 1 N) (hcard : delta * N ≤ A.card) : HasNatAP A k := by
  classical
  let Q : NatAP := ⟨1, 1, N⟩
  have hQ : Q.IsProper := Q.isProper_of_step_pos (by change 0 < (1 : Nat); decide)
  apply Q.hasNatAP_of_pullback hQ A
  apply hfin
  rw [Q.card_pullback hQ]
  have hAQ : A ⊆ Q.carrier := by
    intro x hx
    have hxI := Finset.mem_Icc.mp (hA hx)
    refine Finset.mem_image.mpr ⟨⟨x - 1, ?_⟩, Finset.mem_univ _, ?_⟩
    · change x - 1 < N
      omega
    · change 1 + (x - 1) * 1 = x
      omega
  simpa only [Finset.inter_eq_left.mpr hAQ] using hcard

/-- Quantitative Szemeredi on the source's natural interval, conditional
on the explicit discrepancy input, with a proved closed length threshold. -/
theorem FunctionDiscrepancyBound.natural_szemeredi_closed
    {k : Nat} {delta beta sigma T : Real} (hk : 2 ≤ k) (hδ : 0 < delta)
    (hβ : 0 < beta) (hσ : 0 < sigma)
    (hbound : FunctionDiscrepancyBound (k - 2) (intervalUniformityParameter delta k) beta sigma T)
    (N : Nat) (hN : intervalDiscrepancyClosedThreshold k delta beta sigma T ≤ N)
    (A : Finset Nat) (hA : A ⊆ Finset.Icc 1 N) (hcard : delta * N ≤ A.card) : HasNatAP A k :=
  hasNatAP_Icc_of_fin_interval (fun B hB => hbound.interval_szemeredi_closed hk hδ hβ hσ N hN B hB)
    A hA hcard

end LeanProofs.GowersSzemeredi
