import DiophantineConsistency.Sign33ConstructorEllRetry

/-! P-unit norm transport under an explicit tau representative. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33ForwardNormP
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 SharingGateModel
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem norm_p_of_core (ports : Fin 4 → V) (u : Fin 14 → V)
    (gap tau inner value negative : V)
    (htau : let d := Carrier65.core (fun j => ι (ports j)) (fun j => ι (u j+1))
      ι tau = d.tau)
    (hp : let d := Carrier65.core (fun j => ι (ports j)) (fun j => ι (u j+1))
      d.P = 1) :
    let v : Fin 34 → V := Fin.cons (1 : V) (SharingForward33.witnessCoordinates ports u gap tau inner value negative)
    ι (v 27)*ι (v 27)-ι (v 21)*(ι (v 21)+((ι (v 11)+1)+(ι (v 12)+1))) = 1 := by
  let d := Carrier65.core (fun j => ι (ports j)) (fun j => ι (u j+1))
  let v : Fin 34 → V := Fin.cons (1 : V) (SharingForward33.witnessCoordinates ports u gap tau inner value negative)
  have hell : ι (v 21) = d.ell := Sign33ConstructorEllRetry.ell_of_core ports u gap tau inner value negative
  have hk : d.k = ((ι (v 11)+1)+(ι (v 12)+1)) := by
    simp [d, v, Carrier65.core, SharingForward33.witnessCoordinates,
      SharingForward38.witnessCoordinates, map_add]
  have ht : ι (v 27) = d.tau := by
    simpa [v, SharingForward33.witnessCoordinates] using htau
  change d.tau ^ 2 - d.ell*(d.ell+d.k) = 1 at hp
  rw [pow_two, ←ht, ←hell, hk] at hp
  exact hp
end DiophantineConsistency.Sign33ForwardNormP
#print axioms DiophantineConsistency.Sign33ForwardNormP.norm_p_of_core
