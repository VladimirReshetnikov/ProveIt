import DiophantineConsistency.Sign15NaRow
import DiophantineConsistency.Sign15SignedValue
import DiophantineConsistency.Sign15SignedAux
import DiophantineConsistency.Sign15ScalarWindow

/-! SOURCE-ONLY auxiliary norm directly from sign15 seed, no inner witness. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign15AuxFromSeed
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 SharingSeed15Degree124 Sign15SharedValues
open ArithmeticPellHalfIndex
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem auxiliary_of_seed (p : Fin 4 → ℤ) (beta K MC MF : V) (v : Fin 16 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)
    (hp1 : ((p 1 : ℤ) : DiffRing V) = ι K)
    (hp2 : ((p 2 : ℤ) : DiffRing V) = ι MC)
    (hp3 : ((p 3 : ℤ) : DiffRing V) = ι MF)
    (hb : 0 < beta) (hMC : MC < beta) (hMF : MF < 2 * beta)
    (hz : InternalZero (seed p) v) :
    let f := v 5 + 1
    let c := C beta v
    let T := v 7 + 1
    let r := Sign15RankValue.Rank beta MC MF v
    let S := Scale beta v
    let y := v 13 + 1
    let u := absdiff (f*f*c*T) (f*f*r+c)
    S*S*u*u + y*y = 1 + S*S*y*y := by
  dsimp only
  have hq := Sign15ScalarWindow.q_bound_of_seed p beta K MC MF v hp0 hp1 hb hMC hMF hz
  have hn := Sign15NaRow.signed_na_of_seed p v hz
  change (ι (v 13) + 1) * (ι (v 13) + 1) -
    ((shared38 p).evalRing (fun i => ι (v i)) * (shared38 p).evalRing (fun i => ι (v i))) *
    ((ι (v 13) + 1) * (ι (v 13) + 1) -
      (shared33 p).evalRing (fun i => ι (v i)) * (shared33 p).evalRing (fun i => ι (v i))) - 1 = 0 at hn
  rw [Sign15SharedValues.scale_eval p beta v hp0,
    Sign15SignedValue.signed_eval p beta MC MF v hp0 hp2 hp3 hq] at hn
  apply Sign15SignedAux.auxiliary_norm_of_signed _ _ _ _ _ _
  simpa only [map_add, map_one] using hn
end DiophantineConsistency.Sign15AuxFromSeed
#print axioms DiophantineConsistency.Sign15AuxFromSeed.auxiliary_of_seed
