import DiophantineConsistency.FreeJConcreteDigitsClient
import DiophantineConsistency.CompactLowExact
import DiophantineConsistency.CompactLowEven
import DiophantineConsistency.CompactHighResidue
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactSymbolicGraphSaturation
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs Ordinary12FreeJ
open ArithmeticBinaryPopulation ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Conditional on *both* symbolic mask port equalities and all remaining
    graph and radix hypotheses; no retained-port calibration is claimed. -/
theorem graph_saturation (p : Fin 4 → ℕ) (v : Fin 12 → V) (N HP : V)
    (hb : 0<(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀ j,0<v j) (hz : InternalZero (literal (fun j => (p j:ℤ))) v)
    (hbeta : (46:V)≤(p 0:V)) (hN : 0<N)
    (hq : 1+v 0*(p 0:V)=Exp.exp ((67*8807)*N))
    (hJ : v 0=rep (67*8807) N)
    (hlow : (p 2:V)=CompactConcreteIncrement.mask)
    (hhigh : HP=((Nat.ofDigits (2^67) CompactHighPopulation.highDigits : ℕ):V))
    (hport : (p 3:V)=HP+(p 0:V)) (hHPJ : 1≤HP*v 0) :
    let q : V := 1+v 0*(p 0:V)
    NoCarry (q-v 1-v 2-1) ((p 2:V)*v 0+1) ∧
      NoCarry (v 1) (HP*v 0-1) := by
  have hHP : HP<Exp.exp (67*8807) := by
    rw [hhigh]
    exact CompactHighPopulation.model_lt
  have hMC2 : (p 2:V)%2=0 := by
    rw [hlow]
    exact CompactLowEven.low_even
  have hHP8 : HP%8=4 := by
    rw [hhigh]
    exact CompactHighResidue.model_mod_eight
  have hsum : population (p 2:V)+population HP=67*8807 := by
    rw [hlow,hhigh]
    change population ((Nat.ofDigits (2^67) (CompactListMask.digits (2^67) 8807 1063 CompactConcreteMask.support) : ℕ):V)+_=_
    rw [CompactLowExact.model_population,CompactHighPopulation.model_population]
    norm_num
  have hMC : (p 2:V)<Exp.exp (67*8807) := by
    rw [hlow]
    exact CompactConcreteMask.model_lt
  exact FreeJSaturationClient.graph_saturation p v (67*8807) N HP hb hl hh hv hz
    hbeta (by norm_num) hN hq hJ hport hMC hHP hMC2 hHP8 hsum hHPJ
end CompactSymbolicGraphSaturation
#print axioms CompactSymbolicGraphSaturation.graph_saturation
