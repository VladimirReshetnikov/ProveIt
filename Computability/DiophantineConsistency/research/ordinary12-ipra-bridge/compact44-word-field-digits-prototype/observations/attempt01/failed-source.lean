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

/-- The vertical field phases compare the current south bits with the
    vertical predecessor's north bits. -/
theorem vertical_digits {row dummy : V → V} [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    {N s j j' : V} (hw : CompactWord row N s) (hj : j<N) (hj' : j'<N)
    (he : (j'+s)%N=j) (u : ℕ) (hu : u<9) :
    dig 67 (packedWord row dummy N) (8807*j+((983+u:ℕ):V)) =
      dig 67 (packedWord row dummy N) (8807*j'+((1013+u:ℕ):V)) := by
  let south : Fin 41 := ⟨25+u, by omega⟩
  let north : Fin 41 := ⟨8+u, by omega⟩
  have hps : position south = 983+u := by
    dsimp [south]
    interval_cases u <;> decide
  have hpn : position north = 1013+u := by
    dsimp [north]
    interval_cases u <;> decide
  have hs := word_copy row dummy N j hj south
  have hn := word_copy row dummy N j' hj' north
  have huV : (u:V)<9 := by exact_mod_cast hu
  have hb := vertical_bits hw hj hj' he (u:V) huV
  simp only [hps, wordPayloadBit, payloadBit, south, Fin.val_mk, Nat.cast_add, Nat.cast_ofNat] at hs
  simp only [hpn, wordPayloadBit, payloadBit, north, Fin.val_mk, Nat.cast_add, Nat.cast_ofNat] at hn
  exact hs.trans (hb.trans hn.symm)

/-- The horizontal field phases compare current east bits with the
    horizontal predecessor's west bits. -/
theorem horizontal_digits {row dummy : V → V} [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    {N s j j' : V} (hw : CompactWord row N s) (hj : j<N) (hj' : j'<N)
    (he : (j'+1)%N=j) (u : ℕ) (hu : u<8) :
    dig 67 (packedWord row dummy N) (8807*j+((1003+u:ℕ):V)) =
      dig 67 (packedWord row dummy N) (8807*j'+((1023+u:ℕ):V)) := by
  let east : Fin 41 := ⟨17+u, by omega⟩
  let west : Fin 41 := ⟨u, by omega⟩
  have hpe : position east = 1003+u := by
    dsimp [east]
    interval_cases u <;> decide
  have hpw : position west = 1023+u := by
    dsimp [west]
    interval_cases u <;> decide
  have heast := word_copy row dummy N j hj east
  have hwest := word_copy row dummy N j' hj' west
  have huV : (u:V)<8 := by exact_mod_cast hu
  have hb := horizontal_bits hw hj hj' he (u:V) huV
  simp only [hpe, wordPayloadBit, payloadBit, east, Fin.val_mk, Nat.cast_add, Nat.cast_ofNat] at heast
  simp only [hpw, wordPayloadBit, payloadBit, west, Fin.val_mk] at hwest
  exact heast.trans (hb.trans hwest.symm)

#print axioms CompactWordFieldDigits.vertical_digits
#print axioms CompactWordFieldDigits.horizontal_digits
end CompactWordFieldDigits
