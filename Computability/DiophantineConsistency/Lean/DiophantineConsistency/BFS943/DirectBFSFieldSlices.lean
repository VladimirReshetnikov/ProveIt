import DiophantineConsistency.BFS943.DirectBFSUniformDecoder
import DiophantineConsistency.Compact44.BinarySliceEqual

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DirectBFSDecodedPayloadBits
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency ArithmeticWindowDigits CompactPartialBand CompactSymbolicKernel
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem bit (N C h : V) (i : Fin 943) (j : Fin 41) (hh : h<N)
    (hin : UniformBandInputs.Inputs (8807*N) C (8807*h+4393) 4393)
    (hw : DirectBFSUniformDecoder.copyWord (8807*N) C (8807*h+4393) 4393=DirectBFSDecoder.tileValue (V:=V) i) :
    dig 67 C (8807*h+(position j:V))=fbit (DirectBFSDecoder.tileValue (V:=V) i) (j.val:V) := by
  have hb := FiniteBinaryWord.bit 41 (copyDigit position (8807*N) C (8807*h+4393) 4393) hin.2.1 j
  change fbit (DirectBFSUniformDecoder.copyWord (8807*N) C (8807*h+4393) 4393) (j.val:V) = _ at hb
  rw [hw] at hb
  unfold copyDigit at hb
  have hj : position j≤4393 := by
    have ha := ForeignBandGeometry.copy_allowed j
    unfold ForeignBandGeometry.Allowed at ha
    omega
  have hi := BlockSelectedMarker.copy_index N h 4393 j hh (by decide) hj
  simp only [Nat.cast_ofNat] at hi
  rw [hi] at hb
  exact hb.symm
#print axioms DirectBFSDecodedPayloadBits.bit
end DirectBFSDecodedPayloadBits
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DirectBFSVerticalFieldBits
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
    (hw : DirectBFSUniformDecoder.copyWord (8807*N) C (8807*h+4393) 4393=DirectBFSDecoder.tileValue (V:=V) i)
    (hin' : UniformBandInputs.Inputs (8807*N) C (8807*(cyc N h s)+4393) 4393)
    (hw' : DirectBFSUniformDecoder.copyWord (8807*N) C (8807*(cyc N h s)+4393) 4393=DirectBFSDecoder.tileValue (V:=V) j) :
    fbit (DirectBFSDecoder.tileValue (V:=V) i) ((25+u:ℕ):V)=
    fbit (DirectBFSDecoder.tileValue (V:=V) j) ((8+u:ℕ):V) := by
  have hp := positions u hu
  have hcyc : cyc N h s<N := cyc_lt hN _ _
  have hleft := DirectBFSDecodedPayloadBits.bit N C h i ⟨25+u,by omega⟩ hh hin hw
  have hright := DirectBFSDecodedPayloadBits.bit N C (cyc N h s) j ⟨8+u,by omega⟩ hcyc hin' hw'
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
    (hw : DirectBFSUniformDecoder.copyWord (8807*N) C (8807*h+4393) 4393=DirectBFSDecoder.tileValue (V:=V) i)
    (hin' : UniformBandInputs.Inputs (8807*N) C (8807*(cyc N h s)+4393) 4393)
    (hw' : DirectBFSUniformDecoder.copyWord (8807*N) C (8807*(cyc N h s)+4393) 4393=DirectBFSDecoder.tileValue (V:=V) j) :
    BinarySliceEqual.slice (DirectBFSDecoder.tileValue (V:=V) i) 25 9 =
    BinarySliceEqual.slice (DirectBFSDecoder.tileValue (V:=V) j) 8 9 := by
  apply BinarySliceEqual.equal
  intro u hu
  obtain ⟨z,hz,he⟩ := bounded_standard 9 u hu
  have hb := bit N C s h i j z hz hN hh hs (hfield z hz) hin hw hin' hw'
  rw [he]
  simpa only [Nat.cast_add,Nat.cast_ofNat] using hb
#print axioms DirectBFSVerticalFieldBits.fields
#print axioms DirectBFSVerticalFieldBits.positions
#print axioms DirectBFSVerticalFieldBits.bit
end DirectBFSVerticalFieldBits
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DirectBFSHorizontalFieldBits
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency ArithmeticWindowDigits ArithmeticCyclicWord CompactPartialBand CompactSymbolicKernel CleanGeometry
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem positions (u : ℕ) (hu : u<8) :
    position ⟨17+u,by omega⟩=1003+u ∧ position ⟨u,by omega⟩=1023+u := by
  have hc : u=0 ∨ u=1 ∨ u=2 ∨ u=3 ∨ u=4 ∨ u=5 ∨ u=6 ∨ u=7 := by omega
  rcases hc with h|h|h|h|h|h|h|h <;> subst u <;> decide +revert

theorem previous (N g : V) (u : ℕ) (hu : u<8) (hN : 0<N) (hg : g<N) :
    cyc (8807*N) (8807*g+((1065+u:ℕ):V)) 8849 = 8807*(cyc N g 1)+((1023+u:ℕ):V) := by
  have hn : 0<8807*N := mul_pos (by norm_num) hN
  have hs : 1%N<N := mod_lt _ hN
  have hmod : (8807:V)%(8807*N)=8807*(1%N) := by
    simpa only [mul_one] using (ArithmeticModularCancellation.mul_mod_mul (k:=(8807:V)) (a:=(1:V)) (b:=N) (by norm_num) hN)
  have hj : (((1065+u):ℕ):V)<8807 := by exact_mod_cast (show 1065+u<8807 by omega)
  have hd : (42:V)≤(((1065+u):ℕ):V) := by exact_mod_cast (show 42≤1065+u by omega)
  have hsub : (((1065+u):ℕ):V)-42=(((1023+u):ℕ):V) := by
    apply (eq_tsub_of_add_eq ?_).symm
    exact_mod_cast (show (1023+u)+42=1065+u by omega)
  calc
    _ = cyc (8807*N) (cyc (8807*N) (8807*g+((1065+u:ℕ):V)) 42) 8807 := by
      rw [TemporalSafeCyclic.cyc_nested _ _ _ _ hn]
      norm_num
    _ = cyc (8807*N) (8807*g+((1023+u:ℕ):V)) 8807 := by
      rw [BlockCyclicIndex.reflected N g _ 42 hg hj hd,hsub]
    _ = cyc (8807*N) (8807*g+((1023+u:ℕ):V)) (8807*(1%N)) := by
      rw [←hmod,cyc_mod _ _ _ hn]
    _ = 8807*(cyc N g (1%N))+((1023+u:ℕ):V) := BlockCyclicIndex.shift N g (1%N) _ hg hs (by exact_mod_cast (show 1023+u<8807 by omega))
    _ = 8807*(cyc N g 1)+((1023+u:ℕ):V) := by rw [cyc_mod _ _ _ hN]

theorem bit (N C g : V) (i j : Fin 943) (u : ℕ) (hu : u<8) (hN : 0<N) (hg : g<N)
    (hfield : ∀ k<8807*N, k%8807=((1065+u:ℕ):V) →
      dig 67 C (cyc (8807*N) k 62)=dig 67 C (cyc (8807*N) k 8849))
    (hin : UniformBandInputs.Inputs (8807*N) C (8807*g+4393) 4393)
    (hw : DirectBFSUniformDecoder.copyWord (8807*N) C (8807*g+4393) 4393=DirectBFSDecoder.tileValue (V:=V) i)
    (hin' : UniformBandInputs.Inputs (8807*N) C (8807*(cyc N g 1)+4393) 4393)
    (hw' : DirectBFSUniformDecoder.copyWord (8807*N) C (8807*(cyc N g 1)+4393) 4393=DirectBFSDecoder.tileValue (V:=V) j) :
    fbit (DirectBFSDecoder.tileValue (V:=V) i) ((17+u:ℕ):V)=
    fbit (DirectBFSDecoder.tileValue (V:=V) j) (u:V) := by
  have hp := positions u hu
  have hcyc : cyc N g 1<N := cyc_lt hN _ _
  have hleft := DirectBFSDecodedPayloadBits.bit N C g i ⟨17+u,by omega⟩ hg hin hw
  have hright := DirectBFSDecodedPayloadBits.bit N C (cyc N g 1) j ⟨u,by omega⟩ hcyc hin' hw'
  simp only [hp.1,hp.2] at hleft hright
  have hi := BlockCyclicIndex.index N g ((1065+u:ℕ):V) hg (by exact_mod_cast (show 1065+u<8807 by omega))
  have he := hfield _ hi.1 hi.2
  have hsub : ((1065+u:ℕ):V)-62=((1003+u:ℕ):V) := by
    apply (eq_tsub_of_add_eq ?_).symm
    exact_mod_cast (show (1003+u)+62=1065+u by omega)
  have hhj : (62:V)≤((1065+u:ℕ):V) := by exact_mod_cast (show 62≤1065+u by omega)
  rw [BlockCyclicIndex.reflected N g ((1065+u:ℕ):V) 62 hg (by exact_mod_cast (show 1065+u<8807 by omega)) hhj,
    hsub,previous N g u hu hN hg] at he
  exact hleft.symm.trans (he.trans hright)

theorem fields (N C g : V) (i j : Fin 943) (hN : 0<N) (hg : g<N)
    (hfield : ∀ u : ℕ, u<8 → ∀ k<8807*N, k%8807=((1065+u:ℕ):V) →
      dig 67 C (cyc (8807*N) k 62)=dig 67 C (cyc (8807*N) k 8849))
    (hin : UniformBandInputs.Inputs (8807*N) C (8807*g+4393) 4393)
    (hw : DirectBFSUniformDecoder.copyWord (8807*N) C (8807*g+4393) 4393=DirectBFSDecoder.tileValue (V:=V) i)
    (hin' : UniformBandInputs.Inputs (8807*N) C (8807*(cyc N g 1)+4393) 4393)
    (hw' : DirectBFSUniformDecoder.copyWord (8807*N) C (8807*(cyc N g 1)+4393) 4393=DirectBFSDecoder.tileValue (V:=V) j) :
    BinarySliceEqual.slice (DirectBFSDecoder.tileValue (V:=V) i) 17 8 =
    BinarySliceEqual.slice (DirectBFSDecoder.tileValue (V:=V) j) 0 8 := by
  apply BinarySliceEqual.equal
  intro u hu
  obtain ⟨z,hz,he⟩ := bounded_standard 8 u hu
  have hb := bit N C g i j z hz hN hg (hfield z hz) hin hw hin' hw'
  rw [he]
  simpa only [Nat.cast_add,Nat.cast_ofNat,zero_add] using hb
#print axioms DirectBFSHorizontalFieldBits.previous
#print axioms DirectBFSHorizontalFieldBits.fields
end DirectBFSHorizontalFieldBits
