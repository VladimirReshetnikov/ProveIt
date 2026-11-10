import DiophantineConsistency.Source34.Source34FieldMatch
import DiophantineConsistency.Mixed121.Mixed121TileMatch

/-! # Neighbouring tiles match as Wang tiles, at source34

`Mixed121TileMatch` at the source34 tuple. The label arithmetic
(`Mixed121TileMatch.bits_eq`, `digit_south`, `digit_north`, `digit_east`,
`digit_west`, `labels`, `label_eq`) concerns only the shared 943 tiles and
their radix-four digits, and is used directly. Only the chain link
`graph_tile_match` is re-declared over `Source34FieldMatch`: for every block
`h` with tile `i`, temporal predecessor tile `j` and spatial neighbour tile
`l`, `south(i) = north(j)` and `east(i) = west(l)`. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Source34TileMatch
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ArithmeticWindowDigits ArithmeticCyclicWord ArithmeticRepunit ArithmeticPackingBlocks
open Mixed121BlockWord (row)
open Mixed121TileMatch (label_eq labels digit_south digit_north digit_east digit_west)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

attribute [local irreducible] Compact943Data.rows Mixed121Flatten.selectors Mixed121Flatten.copies
attribute [local irreducible] Source34Ports.betaNat Source34Ports.lowNat Source34Ports.highNat
  Source34Kernel.paramKernel Mixed121Kernel.rho

theorem graph_tile_match (v : Fin 12 → V) (hv : ∀ j, 0 < v j)
    (hz : CompactLeafFacts.LeafFacts Source34Ports.ports v) :
    let p := Source34Ports.ports
    let q : V := 1+v 0*(p 0:V)
    let C : V := q-v 1-v 2
    ∃ N W s : V, 0<N ∧ q=Exp.exp ((121*8801)*N) ∧ s<N ∧
      Blocks 10 (row C N 1) N W ∧
      (∀ h<N, row C N 1 h<943 ∧ row C N 1 h≠1) ∧
      ∀ h<N, ∃ i j l : Fin 943,
        row C N 1 h=(i.val:V) ∧ row C N 1 (cyc N h s)=(j.val:V) ∧
        row C N 1 (cyc N h 1)=(l.val:V) ∧
        (Compact943Data.row i).2.2.2=(Compact943Data.row j).2.1 ∧
        (Compact943Data.row i).2.2.1=(Compact943Data.row l).1 := by
  obtain ⟨N,W,s,hN,hq,hs,hW,hbound,hfields⟩ := Source34FieldMatch.graph_field_match v hv hz
  refine ⟨N,W,s,hN,hq,hs,hW,hbound,?_⟩
  intro h hh
  obtain ⟨i,j,l,hi,hj,hl,hvert,hhor⟩ := hfields h hh
  refine ⟨i,j,l,hi,hj,hl,?_,?_⟩
  · apply label_eq _ _ (labels i).2.2.2 (labels j).2.1
    intro u hu
    have := hvert u hu
    rw [digit_south _ u hu, digit_north _ u hu] at this
    exact this
  · apply label_eq _ _ (labels i).2.2.1 (labels l).1
    intro u hu
    have := hhor u hu
    rw [digit_east _ u hu, digit_west _ u hu] at this
    exact this
end Source34TileMatch
#print axioms Source34TileMatch.graph_tile_match
