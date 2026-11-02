import DiophantineConsistency.VerticalFieldBits
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace HorizontalFieldBits
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
    (hw : UniformBandDecoder.copyWord (8807*N) C (8807*g+4393) 4393=Compact943Decoder.tileValue (V:=V) i)
    (hin' : UniformBandInputs.Inputs (8807*N) C (8807*(cyc N g 1)+4393) 4393)
    (hw' : UniformBandDecoder.copyWord (8807*N) C (8807*(cyc N g 1)+4393) 4393=Compact943Decoder.tileValue (V:=V) j) :
    fbit (Compact943Decoder.tileValue (V:=V) i) ((17+u:ℕ):V)=
    fbit (Compact943Decoder.tileValue (V:=V) j) (u:V) := by
  have hp := positions u hu
  have hcyc : cyc N g 1<N := cyc_lt hN _ _
  have hleft := DecodedPayloadBits.bit N C g i ⟨17+u,by omega⟩ hg hin hw
  have hright := DecodedPayloadBits.bit N C (cyc N g 1) j ⟨u,by omega⟩ hcyc hin' hw'
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
    (hw : UniformBandDecoder.copyWord (8807*N) C (8807*g+4393) 4393=Compact943Decoder.tileValue (V:=V) i)
    (hin' : UniformBandInputs.Inputs (8807*N) C (8807*(cyc N g 1)+4393) 4393)
    (hw' : UniformBandDecoder.copyWord (8807*N) C (8807*(cyc N g 1)+4393) 4393=Compact943Decoder.tileValue (V:=V) j) :
    BinarySliceEqual.slice (Compact943Decoder.tileValue (V:=V) i) 17 8 =
    BinarySliceEqual.slice (Compact943Decoder.tileValue (V:=V) j) 0 8 := by
  apply BinarySliceEqual.equal
  intro u hu
  obtain ⟨z,hz,he⟩ := bounded_standard 8 u hu
  have hb := bit N C g i j z hz hN hg (hfield z hz) hin hw hin' hw'
  rw [he]
  simpa only [Nat.cast_add,Nat.cast_ofNat,zero_add] using hb
#print axioms HorizontalFieldBits.previous
#print axioms HorizontalFieldBits.fields
end HorizontalFieldBits
