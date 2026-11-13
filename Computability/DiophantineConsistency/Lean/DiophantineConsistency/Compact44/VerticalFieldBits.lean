import DiophantineConsistency.Compact44.DecodedPayloadBits
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace VerticalFieldBits
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency ArithmeticWindowDigits ArithmeticCyclicWord CompactPartialBand CompactSymbolicKernel CleanGeometry
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem positions (u : ℕ) (hu : u<9) :
    position ⟨25+u,by omega⟩=983+u ∧ position ⟨8+u,by omega⟩=1013+u := by
  have hc : u=0 ∨ u=1 ∨ u=2 ∨ u=3 ∨ u=4 ∨ u=5 ∨ u=6 ∨ u=7 ∨ u=8 := by omega
  rcases hc with h|h|h|h|h|h|h|h|h <;> subst u <;> decide +revert

theorem bit (N C s h : V) (i j : Fin 943) (u : ℕ) (hu : u<9) (hN : 0<N) (hh : h<N) (hs : s<N)
    (hfield : ∀ k<8807*N, k%8807=((1013+u:ℕ):V) →
      dig 67 C (cyc (8807*N) k 30)=dig 67 C (cyc (8807*N) k (8807*s)))
    (hin : UniformBandInputs.Inputs (8807*N) C (8807*h+4393) 4393)
    (hw : UniformBandDecoder.copyWord (8807*N) C (8807*h+4393) 4393=Compact943Decoder.tileValue (V:=V) i)
    (hin' : UniformBandInputs.Inputs (8807*N) C (8807*(cyc N h s)+4393) 4393)
    (hw' : UniformBandDecoder.copyWord (8807*N) C (8807*(cyc N h s)+4393) 4393=Compact943Decoder.tileValue (V:=V) j) :
    fbit (Compact943Decoder.tileValue (V:=V) i) ((25+u:ℕ):V)=
    fbit (Compact943Decoder.tileValue (V:=V) j) ((8+u:ℕ):V) := by
  have hp := positions u hu
  have hcyc : cyc N h s<N := cyc_lt hN _ _
  have hleft := DecodedPayloadBits.bit N C h i ⟨25+u,by omega⟩ hh hin hw
  have hright := DecodedPayloadBits.bit N C (cyc N h s) j ⟨8+u,by omega⟩ hcyc hin' hw'
  simp only [hp.1,hp.2] at hleft hright
  have hi := BlockCyclicIndex.index N h ((1013+u:ℕ):V) hh (by exact_mod_cast (show 1013+u<8807 by omega))
  have he := hfield _ hi.1 hi.2
  have hsub : ((1013+u:ℕ):V)-30=((983+u:ℕ):V) := by
    apply (eq_tsub_of_add_eq ?_).symm
    exact_mod_cast (show (983+u)+30=1013+u by omega)
  have hhj : (30:V)≤((1013+u:ℕ):V) := by exact_mod_cast (show 30≤1013+u by omega)
  rw [BlockCyclicIndex.reflected N h ((1013+u:ℕ):V) 30 hh (by exact_mod_cast (show 1013+u<8807 by omega)) hhj,
    hsub,BlockCyclicIndex.shift N h s ((1013+u:ℕ):V) hh hs (by exact_mod_cast (show 1013+u<8807 by omega))] at he
  exact hleft.symm.trans (he.trans hright)
theorem fields (N C s h : V) (i j : Fin 943) (hN : 0<N) (hh : h<N) (hs : s<N)
    (hfield : ∀ u : ℕ, u<9 → ∀ k<8807*N, k%8807=((1013+u:ℕ):V) →
      dig 67 C (cyc (8807*N) k 30)=dig 67 C (cyc (8807*N) k (8807*s)))
    (hin : UniformBandInputs.Inputs (8807*N) C (8807*h+4393) 4393)
    (hw : UniformBandDecoder.copyWord (8807*N) C (8807*h+4393) 4393=Compact943Decoder.tileValue (V:=V) i)
    (hin' : UniformBandInputs.Inputs (8807*N) C (8807*(cyc N h s)+4393) 4393)
    (hw' : UniformBandDecoder.copyWord (8807*N) C (8807*(cyc N h s)+4393) 4393=Compact943Decoder.tileValue (V:=V) j) :
    BinarySliceEqual.slice (Compact943Decoder.tileValue (V:=V) i) 25 9 =
    BinarySliceEqual.slice (Compact943Decoder.tileValue (V:=V) j) 8 9 := by
  apply BinarySliceEqual.equal
  intro u hu
  obtain ⟨z,hz,he⟩ := bounded_standard 9 u hu
  have hb := bit N C s h i j z hz hN hh hs (hfield z hz) hin hw hin' hw'
  rw [he]
  simpa only [Nat.cast_add,Nat.cast_ofNat] using hb
#print axioms VerticalFieldBits.fields
#print axioms VerticalFieldBits.positions
#print axioms VerticalFieldBits.bit
end VerticalFieldBits
