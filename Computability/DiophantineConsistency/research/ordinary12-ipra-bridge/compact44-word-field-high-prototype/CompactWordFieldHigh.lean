import CompactWordPhysicalFieldParity
import CompactWordHorizontalParity
import CompactWordMarkerParity
import DiophantineConsistency.FieldHighModel
import DiophantineConsistency.FieldMarkerHigh

/-! Actual high-mask no-carry on all compact field and marker phases. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactWordFieldHigh
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticWindowDigits ArithmeticPacking ArithmeticBinaryCarry
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts CompactMarkedTransport
open CompactConstructedWord CompactBaseLowNoCarry
open CompactWordPhysicalFieldParity CompactWordHorizontalParity CompactWordMarkerParity
attribute [local irreducible] paramKernel rho highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem even_noCarry_one (x : V) (h : x%2=0) : NoCarry x 1 :=
  (noCarry_comm _ _).2 (one_noCarry_even x h)

/-- Every vertical field or marker phase is disjoint from the high mask. -/
theorem vertical_fields (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    {N s j p : V} (hw : CompactWord row N s) (hN : 1<N) (hs : s<N)
    (hbool : ∀ j, dummy j ≤ 1) (hj : j<N) (hlo : 1013≤p) (hhi : p<1023) :
    NoCarry (dig 67 (blk 590069 (paramKernel rho : V) N s (cellWord row dummy) j) p)
      (dig 67 (highNat : V) p) := by
  obtain ⟨m, rfl⟩ := eq_nat_of_lt_nat (n:=1023) hhi
  have hmlo : 1013≤m := by exact_mod_cast hlo
  have hmhi : m<1023 := by exact_mod_cast hhi
  let u := m-1013
  have hu : u<10 := by dsimp [u]; omega
  have he : m=1013+u := by dsimp [u]; omega
  by_cases hu9 : u<9
  · rw [he, FieldHighModel.vertical_digit u hu9]
    exact even_noCarry_one _ (vertical_even row dummy hw hN hs hbool hj u hu9)
  · have hu' : u=9 := by omega
    have hm : m=1022 := by omega
    rw [hm]
    simp only [Nat.cast_ofNat]
    rw [FieldMarkerHigh.vertical_digit]
    exact even_noCarry_one _ (vertical_marker_even row dummy hw hN hs hbool hj)

/-- Every horizontal field or marker phase is disjoint from the high mask. -/
theorem horizontal_fields (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    {N s j p : V} (hw : CompactWord row N s) (hN : 1<N) (hs : s<N)
    (hbool : ∀ j, dummy j ≤ 1) (hj : j<N) (hlo : 1065≤p) (hhi : p<1074) :
    NoCarry (dig 67 (blk 590069 (paramKernel rho : V) N s (cellWord row dummy) j) p)
      (dig 67 (highNat : V) p) := by
  obtain ⟨m, rfl⟩ := eq_nat_of_lt_nat (n:=1074) hhi
  have hmlo : 1065≤m := by exact_mod_cast hlo
  have hmhi : m<1074 := by exact_mod_cast hhi
  let u := m-1065
  have hu : u<9 := by dsimp [u]; omega
  have he : m=1065+u := by dsimp [u]; omega
  by_cases hu8 : u<8
  · rw [he, FieldHighModel.horizontal_digit u hu8]
    exact even_noCarry_one _ (horizontal_even row dummy hw hN hs hbool hj u hu8)
  · have hu' : u=8 := by omega
    have hm : m=1073 := by omega
    rw [hm]
    simp only [Nat.cast_ofNat]
    rw [FieldMarkerHigh.horizontal_digit]
    exact even_noCarry_one _ (horizontal_marker_even row dummy hw hN hs hbool hj)

#print axioms CompactWordFieldHigh.vertical_fields
#print axioms CompactWordFieldHigh.horizontal_fields
end CompactWordFieldHigh
