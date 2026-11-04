import Trace74VariableWidthQuarterFloor
import Trace74Width3FixedGlobal

/-! A clean fractional index bound and same-pair existential client. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74VariableWidthFractionalClient
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75 ArithmeticPellRecurrence
open Trace75Factors Trace74Pell Trace74VariableWidthQuarterFloor Trace74Width3FixedGlobal CompactFixedBeta
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local irreducible] CompactFixedBeta.betaNat

/-- Model division gives the strict fractional form of the floor bound. -/
theorem five_four_of_floor (n r : V) (h : n+n/4<r) : 5*n<4*r := by
  have hs : n+n/4+1≤r := lt_iff_succ_le.mp h
  have hd : 4*(n/4)+n%4=n := div_add_mod n 4
  have hm : n%4<4 := mod_lt n (by norm_num)
  have hsR := ι_le_ι.mpr hs
  have hdR := congrArg (ι : V →+* DiffRing V) hd
  have hmR := ι_lt_ι.mpr hm
  simp only [map_add,map_one] at hsR
  simp only [map_add,map_mul,map_ofNat] at hdR
  simp only [map_ofNat] at hmR
  have ht : (5:DiffRing V)*ι n<4*ι r := by linarith
  apply ι_lt_ι.mp
  simpa only [map_mul,map_ofNat] using ht

/-- Same-zero fixed-symbolic fractional separation under the explicit
upper bound on the first index. -/
theorem fixed_graph_fractional (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (n r : V) (hp0 : p 0=betaNat) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j))=0)
    (hn : (4:V)≤n) (h8 : 8*n≤((67:V)*8807))
    (hny : 2*ycoord n (2*(firstParam p v-1)+1)=k v)
    (hc : Trace75Factors.c p v=ycoord r (A p v-1)) : 5*n<4*r :=
  five_four_of_floor n r (fixed_graph_floor_separation p v n r hp0 hv hz hn h8 hny hc)

/-- The already-linked pair retains its ordinate and residue data; the
fractional conclusion is conditional on that pair's first-index bound. -/
theorem fixed_exists_fractional_indices (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hp0 : p 0=betaNat) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j))=0) :
    ∃ n r : V, 7≤n ∧ 2*ycoord n (2*(firstParam p v-1)+1)=k v ∧
      k v%(q p v)^4=(2*n)%(q p v)^4 ∧
      11≤r ∧ n+3<r ∧ r<2*n ∧ r%2=1 ∧
      Trace75Factors.c p v=ycoord r (A p v-1) ∧
      (8*n≤((67:V)*8807) → 5*n<4*r) := by
  obtain ⟨n,r,hn,hny,hmod,hr11,hnr,hr2,hodd,hc⟩ :=
    fixed_exists_width3_global p v hp0 hv hz
  refine ⟨n,r,hn,hny,hmod,hr11,hnr,hr2,hodd,hc,?_⟩
  intro h8
  have hn4 : (4:V)≤n := le_trans (by norm_num) hn
  exact fixed_graph_fractional p v n r hp0 hv hz hn4 h8 hny hc

#print axioms Trace74VariableWidthFractionalClient.five_four_of_floor
#print axioms Trace74VariableWidthFractionalClient.fixed_graph_fractional
#print axioms Trace74VariableWidthFractionalClient.fixed_exists_fractional_indices
end Trace74VariableWidthFractionalClient
