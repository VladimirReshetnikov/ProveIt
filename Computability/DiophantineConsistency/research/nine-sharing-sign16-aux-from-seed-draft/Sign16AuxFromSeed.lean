import DiophantineConsistency.Sign16InnerFromSeed
import DiophantineConsistency.Sign16AbsDiffIngredient

/-! SOURCE-ONLY non-circular auxiliary norm extracted from sign16 seed zero. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign16AuxFromSeed
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 SharingSeed16Degree112 Sign16SharedValues
open ArithmeticPellHalfIndex
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem auxiliary_of_seed (p : Fin 4 → ℤ) (beta K MC MF : V) (v : Fin 17 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)
    (hp1 : ((p 1 : ℤ) : DiffRing V) = ι K)
    (hp2 : ((p 2 : ℤ) : DiffRing V) = ι MC)
    (hp3 : ((p 3 : ℤ) : DiffRing V) = ι MF)
    (hb : 0 < beta) (hMC : MC < beta) (hMF : MF < 2 * beta)
    (hz : InternalZero (seed p) v) :
    let f := v 5 + 1
    let c := C beta v
    let T := v 7 + 1
    let r := Sign16RankValue.Rank beta MC MF v
    let S := Scale beta v
    let y := v 13 + 1
    let u := absdiff (f*f*c*T) (f*f*r+c)
    S*S*u*u + y*y = 1 + S*S*y*y := by
  dsimp only
  have hi := Sign16InnerFromSeed.inner_of_seed p beta K MC MF v hp0 hp1 hp2 hp3 hb hMC hMF hz
  have hn := Sign16RowPremises.signed_na_of_seed p v hz
  change (ι (v 13) + 1) * (ι (v 13) + 1) -
    ((shared35 p).evalRing (fun i => ι (v i)) * (shared35 p).evalRing (fun i => ι (v i))) *
    ((ι (v 13) + 1) * (ι (v 13) + 1) -
      ((ι (v 5) + 1) * (ι (v 5) + 1) * ι (v 16) - (shared18 p).evalRing (fun i => ι (v i))) *
      ((ι (v 5) + 1) * (ι (v 5) + 1) * ι (v 16) - (shared18 p).evalRing (fun i => ι (v i)))) - 1 = 0 at hn
  rw [Sign16SharedValues.scale_eval p beta v hp0, Sign16SharedValues.c_eval p beta v hp0] at hn
  apply Sign16AbsDiffIngredient.auxiliary_norm_of_signed _ _ _ _ _ _ _ hi
  simpa only [map_add, map_one] using hn
end DiophantineConsistency.Sign16AuxFromSeed
#print axioms DiophantineConsistency.Sign16AuxFromSeed.auxiliary_of_seed
