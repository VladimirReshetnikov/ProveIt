import DiophantineConsistency.Sign26ZeroExtraction
import DiophantineConsistency.Sign26GapRepresentative

/-! SOURCE-ONLY: combine seed Nt extraction and conditional representative. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign26SeedGap
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem exists_gap (p : Fin 4 → ℤ) (beta K : V) (v : Fin 27 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)
    (hp1 : ((p 1 : ℤ) : DiffRing V) = ι K)
    (hbeta : 1 ≤ beta) (hz : InternalZero (SharingSeed26Sextic.seed p) v) :
    ∃ gap : V, ι gap =
      (((p 0 : ℤ) : DiffRing V) * (ι (v 1) + 1)) *
        (((p 0 : ℤ) : DiffRing V) * (ι (v 1) + 1) + 1) + (ι (v 3) + 1) -
      (((p 0 : ℤ) : DiffRing V) * (ι (v 1) + 1)) * (ι (v 2) + 1) := by
  have hNt := Sign26ZeroExtraction.nt_eq p v hz
  rw [hp0, hp1] at hNt
  have hgap := Sign26GapRepresentative.exists_gap beta K (v 1) (v 2) (v 3) (v 4) (v 9) hbeta hNt
  rw [hp0]
  exact hgap
end DiophantineConsistency.Sign26SeedGap
#print axioms DiophantineConsistency.Sign26SeedGap.exists_gap
