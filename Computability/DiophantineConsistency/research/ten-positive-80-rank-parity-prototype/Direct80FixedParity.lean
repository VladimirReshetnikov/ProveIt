import Direct80FixedBetaOdd
import Direct80GraphParity

/-! Fixed beta supplies the oddness premise of the graph parity theorem. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Direct80FixedParity
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ArithmeticGcdNormalization CompactFixedBeta
open TenPositive80Graph TenPositive80Factors
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_fixed_even_and_unit (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hfixed : p 0=betaNat) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j) (hz : InternalZero (graph (integerPorts p)).output v) :
    (∃w : V, q p v=2*w) ∧ Bez (b p v) (mu p v*mu p v) 1 := by
  have hb : 0<(p 0:V) := by
    rw [hfixed]
    exact (CompactFixedBeta.bounds (1:V) (by simp)).1
  have hodd : ∃u : V, (p 0:V)=2*u+1 := by
    rw [hfixed]
    exact Direct80FixedBetaOdd.beta_odd_model
  exact Direct80GraphParity.graph_even_and_unit p v hb hl hh hv hz hodd

#print axioms Direct80FixedParity.graph_fixed_even_and_unit
end Direct80FixedParity
