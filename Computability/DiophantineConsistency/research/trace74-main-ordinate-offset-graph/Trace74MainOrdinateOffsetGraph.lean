import Trace74MainOrdinateOffsetResidue
import Trace74VariableWidthTwoSevenths

/-! Positive offset residue for the same fixed-symbolic graph tuple. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74MainOrdinateOffsetGraph
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75 ArithmeticPellRecurrence
open Trace75Factors Trace74Pell Trace74MainOrdinateOffsetResidue
open Trace74VariableWidthTwoSevenths CompactFixedBeta
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local irreducible] CompactFixedBeta.betaNat

/-- The main ordinate of the same positive graph tuple has the exact
offset residue and positive split. -/
theorem graph_offset_residue (p : Fin 4 → ℕ) (v : Fin 10 → V) (r : V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hc : c p v=ycoord r (A p v-1)) :
    0<v 8 ∧ v 8<k v ∧ (v 8)%(Y p v)=r%(Y p v) := by
  have hq : 0<q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  have hY : 0<Y p v := mul_pos (mul_pos (mul_pos hq hq) hq) (hv 6)
  exact tuple_offset_interval_residue p v r hY (hv 8) (hv 9) hc

/-- One linked fixed-symbolic index pair retains both no-cap separations
and the main ordinate's positive offset residue. -/
theorem fixed_exists_offset_indices (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hp0 : p 0=betaNat) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j))=0) :
    ∃ n r : V, 7≤n ∧ 2*ycoord n (2*(firstParam p v-1)+1)=k v ∧
      k v%(q p v)^4=(2*n)%(q p v)^4 ∧
      11≤r ∧ n+3<r ∧ n+min (n/4) 118013<r ∧
      n+min ((2*n)/7) 32781<r ∧ r<2*n ∧ r%2=1 ∧
      c p v=ycoord r (A p v-1) ∧
      0<v 8 ∧ v 8<k v ∧ (v 8)%(Y p v)=r%(Y p v) := by
  obtain ⟨n,r,hn,hny,hmod,hr11,hnr,hquarter,htwosev,hr2,hodd,hc⟩ :=
    fixed_exists_both_indices p v hp0 hv hz
  have hb : 0<(p 0:V) := by
    rw [hp0]
    exact lt_of_lt_of_le (by norm_num : (0:V)<31) Trace74FixedBeta31.beta_ge_31
  exact ⟨n,r,hn,hny,hmod,hr11,hnr,hquarter,htwosev,hr2,hodd,hc,
    graph_offset_residue p v r hb hv hc⟩

#print axioms Trace74MainOrdinateOffsetGraph.graph_offset_residue
#print axioms Trace74MainOrdinateOffsetGraph.fixed_exists_offset_indices
end Trace74MainOrdinateOffsetGraph
