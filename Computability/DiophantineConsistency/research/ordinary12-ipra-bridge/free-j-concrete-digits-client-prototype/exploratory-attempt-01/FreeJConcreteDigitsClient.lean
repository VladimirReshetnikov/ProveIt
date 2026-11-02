import DiophantineConsistency.FreeJSaturationClient
import DiophantineConsistency.CompactConcreteIncrement
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FreeJConcreteDigitsClient
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs Ordinary12FreeJ
open ArithmeticBinaryPopulation ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The equality to the symbolic low mask and all other saturation inputs are
explicit. No retained MC or graph-port calibration is asserted here. -/
theorem graph_digits (p : Fin 4 → ℕ) (v : Fin 12 → V) (N HP : V)
    (hb : 0<(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀ j,0<v j) (hz : InternalZero (literal (fun j => (p j:ℤ))) v)
    (hbeta : (46:V)≤(p 0:V)) (hN : 0<N)
    (hq : 1+v 0*(p 0:V)=Exp.exp ((67*8807)*N))
    (hJ : v 0=rep (67*8807) N)
    (hlow : (p 2:V)=CompactConcreteIncrement.mask)
    (hport : (p 3:V)=HP+(p 0:V))
    (hHP : HP<Exp.exp (67*8807))
    (hMC2 : (p 2:V)%2=0) (hHP8 : HP%8=4)
    (hsum : population (p 2:V)+population HP=67*8807) (hHPJ : 1≤HP*v 0) :
    let q : V := 1+v 0*(p 0:V)
    let C : V := q-v 1-v 2
    dig 67 C 0=1 ∧ ∀ k < 8807*N, dig 67 C k≤3 := by
  let q : V := 1+v 0*(p 0:V)
  let C : V := q-v 1-v 2
  have hMC : (p 2:V)<Exp.exp (67*8807) := by
    rw [hlow]
    exact CompactConcreteMask.model_lt
  obtain ⟨hnc,_⟩ := FreeJSaturationClient.graph_saturation p v (67*8807) N HP hb hl hh hv hz
    hbeta (by norm_num) hN hq hJ hport hMC hHP hMC2 hHP8 hsum hHPJ
  have hC : 1≤C := by
    apply pos_iff_one_le.mp
    simpa only [C,tsub_tsub] using (FreeJFirstTransport.freej_first_factor_transport p v hb hv hz).2
  have hnc' : NoCarry (C-1) (CompactConcreteIncrement.mask * rep (67*8807) N + 1) := by
    simpa only [C,hlow,hJ] using hnc
  exact CompactConcreteIncrement.recipe_digits N C hN hC hnc'
end FreeJConcreteDigitsClient
#print axioms FreeJConcreteDigitsClient.graph_digits
