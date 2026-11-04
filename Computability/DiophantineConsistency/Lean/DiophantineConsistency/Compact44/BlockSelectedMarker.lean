import DiophantineConsistency.Compact44.FixedGraphBlockCopy
import DiophantineConsistency.Compact44.DecodedOccupied
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace BlockSelectedMarker
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency ArithmeticWindowDigits ArithmeticCyclicWord CompactPartialBand CompactSymbolicKernel
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem copy_index (N h : V) (T : ℕ) (j : Fin 41) (hh : h<N) (hT : T<8807)
    (hj : position j≤T) :
    cyc (8807*N) (8807*h+(T:V)) (((T-position j):ℕ):V) = 8807*h+(position j:V) := by
  have hd : (((T-position j):ℕ):V)≤(T:V) := by exact_mod_cast (Nat.sub_le T (position j))
  rw [BlockCyclicIndex.reflected N h (T:V) (((T-position j):ℕ):V) hh (by exact_mod_cast hT) hd]
  congr 1
  have hsum : (position j:V)+(((T-position j):ℕ):V)=(T:V) := by exact_mod_cast (Nat.add_sub_of_le hj)
  exact (eq_tsub_of_add_eq hsum).symm

theorem selected_markers (N C h : V) (T : ℕ) (hh : h<N) (hT : 3296≤T) (hTmax : T<8807)
    (hin : UniformBandInputs.Inputs (8807*N) C (8807*h+(T:V)) T)
    (hsel : ∃ i : Fin 943, CompactSelectorSum.Selected (selectorDigit (8807*N) C (8807*h+(T:V)) T) i ∧
      UniformBandDecoder.copyWord (8807*N) C (8807*h+(T:V)) T=Compact943Decoder.tileValue (V:=V) i) :
    dig 67 C (8807*h+1095)=1 ∧ dig 67 C (8807*h+2195)=1 ∧ dig 67 C (8807*h+3296)=1 := by
  obtain ⟨i,hi,hw⟩ := hsel
  have hall : ∀ j : Fin 41, 34≤j.val → dig 67 C (8807*h+(position j:V))=1 := by
    intro j hj
    have hbit := DecodedOccupied.decoded_occupied (8807*N) C (8807*h+(T:V)) T i hin.2.1 hw j hj
    have ha := ForeignBandGeometry.copy_allowed j
    unfold ForeignBandGeometry.Allowed at ha
    have hjT : position j≤T := le_trans (by omega) hT
    unfold copyDigit at hbit
    rw [copy_index N h T j hh hTmax hjT] at hbit
    exact hbit
  have h1 := hall ⟨38,by decide⟩ (by decide)
  have h2 := hall ⟨39,by decide⟩ (by decide)
  have h3 := hall ⟨40,by decide⟩ (by decide)
  simpa [position,slots] using And.intro h1 (And.intro h2 h3)

theorem selected_of_copy_one (n C k : V) (T : ℕ) (j : Fin 41)
    (hbit : copyDigit position n C k T j=1) (hdec : UniformBandDecoder.Conclusion n C k T) :
    ∃ i : Fin 943, CompactSelectorSum.Selected (selectorDigit n C k T) i ∧
      UniformBandDecoder.copyWord n C k T=Compact943Decoder.tileValue (V:=V) i := by
  rcases hdec with hzero | hsel
  · have hle : (2:V)^j.val*copyDigit position n C k T j ≤ UniformBandDecoder.copyWord n C k T := by
      unfold UniformBandDecoder.copyWord
      apply Finset.single_le_sum (fun x _ => by simp) (Finset.mem_univ j)
    rw [hbit,mul_one,hzero.2] at hle
    have hp : (0:V)<(2:V)^j.val := pow_pos (by norm_num) _
    exact False.elim ((not_le_of_gt hp) hle)
  · exact hsel
#print axioms BlockSelectedMarker.copy_index
#print axioms BlockSelectedMarker.selected_markers
#print axioms BlockSelectedMarker.selected_of_copy_one
end BlockSelectedMarker
