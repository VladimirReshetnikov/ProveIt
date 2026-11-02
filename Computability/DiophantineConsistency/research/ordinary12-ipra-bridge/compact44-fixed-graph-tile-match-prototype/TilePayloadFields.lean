import DiophantineConsistency.FixedGraphFieldMatch
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace TilePayloadFields
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticStandardCasts
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def val (w n e s : ℕ) : ℕ := w+256*n+131072*e+33554432*s+127*17179869184

theorem natural_fields (w n e s : ℕ) (hw : w<256) (hn : n<512) (he : e<256) (hs : s<512) :
    val w n e s / 2^25 % 2^9=s ∧ val w n e s / 2^8 % 2^9=n ∧
    val w n e s / 2^17 % 2^8=e ∧ val w n e s / 2^0 % 2^8=w := by
  norm_num only [show 2^25=33554432 by decide,show 2^9=512 by decide,
    show 2^8=256 by decide,show 2^17=131072 by decide,pow_zero,Nat.div_one]
  unfold val
  omega
theorem slice_cast (v a m : ℕ) : BinarySliceEqual.slice (v:V) (a:V) (m:V) = ((v/2^a%2^m:ℕ):V) := by
  unfold BinarySliceEqual.slice
  rw [cast_exp,cast_exp,←cast_div,←cast_mod]

theorem tile_fields (i : Fin 943) :
    BinarySliceEqual.slice (Compact943Decoder.tileValue (V:=V) i) 25 9=((Compact943Data.row i).2.2.2:V) ∧
    BinarySliceEqual.slice (Compact943Decoder.tileValue (V:=V) i) 8 9=((Compact943Data.row i).2.1:V) ∧
    BinarySliceEqual.slice (Compact943Decoder.tileValue (V:=V) i) 17 8=((Compact943Data.row i).2.2.1:V) ∧
    BinarySliceEqual.slice (Compact943Decoder.tileValue (V:=V) i) 0 8=((Compact943Data.row i).1:V) := by
  let r := Compact943Data.row i
  have hval : Compact943Decoder.tileValue (V:=V) i = (val r.1 r.2.1 r.2.2.1 r.2.2.2:V) := by
    simp only [Compact943Decoder.tileValue,CompactTilePayload.value,val,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,r]
  obtain ⟨hw,hn,he,hs⟩ := Compact943Data.row_bounds i
  have hnats := natural_fields r.1 r.2.1 r.2.2.1 r.2.2.2 hw hn he hs
  rw [hval]
  have hsouth := slice_cast (V:=V) (val r.1 r.2.1 r.2.2.1 r.2.2.2) 25 9
  have hnorth := slice_cast (V:=V) (val r.1 r.2.1 r.2.2.1 r.2.2.2) 8 9
  have heast := slice_cast (V:=V) (val r.1 r.2.1 r.2.2.1 r.2.2.2) 17 8
  have hwest := slice_cast (V:=V) (val r.1 r.2.1 r.2.2.1 r.2.2.2) 0 8
  simp only [Nat.cast_ofNat,hnats.1] at hsouth
  simp only [Nat.cast_ofNat,hnats.2.1] at hnorth
  simp only [Nat.cast_ofNat,hnats.2.2.1] at heast
  simp only [Nat.cast_ofNat,hnats.2.2.2] at hwest
  exact ⟨hsouth,hnorth,heast,hwest⟩
#print axioms TilePayloadFields.natural_fields
#print axioms TilePayloadFields.tile_fields
end TilePayloadFields
