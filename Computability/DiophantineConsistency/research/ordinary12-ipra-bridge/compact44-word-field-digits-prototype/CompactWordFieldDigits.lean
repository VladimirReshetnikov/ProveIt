import CompactConstructedWord
import CompactWordColorBits

/-! The constructed word carries matched edge bits in the concrete slots. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactWordFieldDigits
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticWindowDigits
open CompactSymbolicKernel CompactForwardCellInputs CompactWordCellClient
open CompactMarkedTransport CompactConstructedWord CompactWordColorBits
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem south_position (u : Fin 9) :
    position ⟨25+u.val, by have := u.isLt; omega⟩ = 983+u.val := by
  fin_cases u <;> decide

theorem north_position (u : Fin 9) :
    position ⟨8+u.val, by have := u.isLt; omega⟩ = 1013+u.val := by
  fin_cases u <;> decide

theorem east_position (u : Fin 8) :
    position ⟨17+u.val, by have := u.isLt; omega⟩ = 1003+u.val := by
  fin_cases u <;> decide

theorem west_position (u : Fin 8) :
    position ⟨u.val, by have := u.isLt; omega⟩ = 1023+u.val := by
  fin_cases u <;> decide

/-- The vertical field phases compare the current south bits with the
    vertical predecessor's north bits. -/
theorem vertical_digits {row dummy : V → V} [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    {N s j j' : V} (hw : CompactWord row N s) (hj : j<N) (hj' : j'<N)
    (he : (j'+s)%N=j) (u : ℕ) (hu : u<9) :
    dig 67 (packedWord row dummy N) (8807*j+((983+u:ℕ):V)) =
      dig 67 (packedWord row dummy N) (8807*j'+((1013+u:ℕ):V)) := by
  let south : Fin 41 := ⟨25+u, by omega⟩
  let north : Fin 41 := ⟨8+u, by omega⟩
  have hps : position south = 983+u := south_position ⟨u,hu⟩
  have hpn : position north = 1013+u := north_position ⟨u,hu⟩
  have hs := word_copy row dummy N j hj south
  have hn := word_copy row dummy N j' hj' north
  have huV : (u:V)<9 := by exact_mod_cast hu
  have hb := vertical_bits hw hj hj' he (u:V) huV
  simp only [hps, wordPayloadBit, payloadBit, south, Nat.cast_add, Nat.cast_ofNat] at hs
  simp only [hpn, wordPayloadBit, payloadBit, north, Nat.cast_add, Nat.cast_ofNat] at hn
  simpa only [Nat.cast_add, Nat.cast_ofNat] using hs.trans (hb.trans hn.symm)

/-- The horizontal field phases compare current east bits with the
    horizontal predecessor's west bits. -/
theorem horizontal_digits {row dummy : V → V} [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    {N s j j' : V} (hw : CompactWord row N s) (hj : j<N) (hj' : j'<N)
    (he : (j'+1)%N=j) (u : ℕ) (hu : u<8) :
    dig 67 (packedWord row dummy N) (8807*j+((1003+u:ℕ):V)) =
      dig 67 (packedWord row dummy N) (8807*j'+((1023+u:ℕ):V)) := by
  let east : Fin 41 := ⟨17+u, by omega⟩
  let west : Fin 41 := ⟨u, by omega⟩
  have hpe : position east = 1003+u := east_position ⟨u,hu⟩
  have hpw : position west = 1023+u := west_position ⟨u,hu⟩
  have heast := word_copy row dummy N j hj east
  have hwest := word_copy row dummy N j' hj' west
  have huV : (u:V)<8 := by exact_mod_cast hu
  have hb := horizontal_bits hw hj hj' he (u:V) huV
  simp only [hpe, wordPayloadBit, payloadBit, east, Nat.cast_add, Nat.cast_ofNat] at heast
  simp only [hpw, wordPayloadBit, payloadBit, west] at hwest
  simpa only [Nat.cast_add, Nat.cast_ofNat] using heast.trans (hb.trans hwest.symm)

#print axioms CompactWordFieldDigits.vertical_digits
#print axioms CompactWordFieldDigits.horizontal_digits
end CompactWordFieldDigits
