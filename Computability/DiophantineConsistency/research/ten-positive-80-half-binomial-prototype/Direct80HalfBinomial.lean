import Direct80SandwichBoth
import ScaledPellRounding

/-! Half-binomial identity from the actual scaled 80-graph zero. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Direct80HalfBinomial
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ArithmeticBinomPascal
open TenPositive80Graph TenPositive80Factors TenPositive80NaturalRank
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_half_binomial (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hbeta31 : (31:V)≤(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j) (hz : InternalZero (graph (integerPorts p)).output v)
    (hbetaodd : ∃u : V, (p 0:V)=2*u+1) :
    ∃ r z : V, 0<r ∧ rankNat p v=2*r+1 ∧ X p v=Exp.exp (2*r+1) ∧
      2*Y p v=binom (2*r) r+z*X p v := by
  obtain ⟨r,hr,hR,hX,hlow,hup⟩ :=
    TenPositive80SandwichBoth.graph_sandwich_both p v hbeta31 hl hh hv hz hbetaodd
  obtain ⟨z,hbin⟩ := ScaledPellRounding.extract (X p v) (Y p v) r (v 8) (v 9)
    (k v) (c p v) hr hX rfl rfl (hv 8) (hv 9) hlow hup
  exact ⟨r,z,hr,hR,hX,hbin⟩

#print axioms Direct80HalfBinomial.graph_half_binomial
end Direct80HalfBinomial
