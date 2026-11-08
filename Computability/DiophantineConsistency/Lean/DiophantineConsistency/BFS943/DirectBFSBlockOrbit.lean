import DiophantineConsistency.BFS943.DirectBFSUniformDecoder
import DiophantineConsistency.Compact44.MarkerSuccessor
import DiophantineConsistency.Compact44.BlockSelectionBridge
import DiophantineConsistency.Compact44.InternalOrbit

/-! Direct-BFS occupied markers and internal orbit propagation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DirectBFSBlockOrbit
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency ArithmeticWindowDigits ArithmeticCyclicWord CompactPartialBand CompactSymbolicKernel
open OrbitDefinability CleanGeometry
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def SelectedBlock (N C h : V) : Prop :=
  ∃ i : Fin 943,CompactSelectorSum.Selected (selectorDigit (8807*N) C (8807*h+4393) 4393) i ∧
    DirectBFSUniformDecoder.copyWord (8807*N) C (8807*h+4393) 4393=DirectBFSDecoder.tileValue (V:=V) i

theorem decoded_occupied (n C k : V) (T : ℕ) (i : Fin 943)
    (hb : ∀ j,copyDigit position n C k T j≤1)
    (hw : (∑ j : Fin 41,(2:V)^j.val*copyDigit position n C k T j)=DirectBFSDecoder.tileValue (V:=V) i) :
    ∀ j : Fin 41,34≤j.val → copyDigit position n C k T j=1 := by
  have hbig : (2181843386368:V)≤∑ j : Fin 41,(2:V)^j.val*copyDigit position n C k T j := by
    rw [hw]
    dsimp only [DirectBFSDecoder.tileValue,CompactTilePayload.value]
    have hpos : (0:V)≤((DirectBFSSymbolicKernel.row i).1:V)+
      256*((DirectBFSSymbolicKernel.row i).2.1:V)+
      131072*((DirectBFSSymbolicKernel.row i).2.2.1:V)+
      33554432*((DirectBFSSymbolicKernel.row i).2.2.2:V) := by simp
    have h := add_le_add hpos (le_refl (127*17179869184:V))
    norm_num only at h
    simpa only [zero_add,show (127:V)*17179869184=2181843386368 by norm_num] using h
  intro j hj
  exact OccupiedBits.high_bits_one _ hb hbig j hj

theorem selected_of_copy_one (n C k : V) (T : ℕ) (j : Fin 41)
    (hbit : copyDigit position n C k T j=1) (hdec : DirectBFSUniformDecoder.Conclusion n C k T) :
    ∃ i : Fin 943,CompactSelectorSum.Selected (selectorDigit n C k T) i ∧
      DirectBFSUniformDecoder.copyWord n C k T=DirectBFSDecoder.tileValue (V:=V) i := by
  rcases hdec with hzero | hsel
  · have hle : (2:V)^j.val*copyDigit position n C k T j≤DirectBFSUniformDecoder.copyWord n C k T := by
      unfold DirectBFSUniformDecoder.copyWord
      apply Finset.single_le_sum (fun x _ => by simp) (Finset.mem_univ j)
    rw [hbit,mul_one,hzero.2] at hle
    have hp : (0:V)<(2:V)^j.val := pow_pos (by norm_num) _
    exact False.elim ((not_le_of_gt hp) hle)
  · exact hsel

theorem selected_iff_digit (N C h : V) (hh : h<N)
    (hdec : DirectBFSUniformDecoder.Conclusion (8807*N) C (8807*h+4393) 4393) :
    SelectedBlock N C h ↔ ∃ j<943,dig 67 C (8807*h+j)=1 := by
  constructor
  · rintro ⟨i,hi,_hw⟩
    refine ⟨(i.val:V),by exact_mod_cast i.isLt,?_⟩
    have hbit := hi.1
    unfold selectorDigit at hbit
    rw [BlockSelectionBridge.selector_index N h i hh] at hbit
    exact hbit
  · rintro ⟨j,hj,hbit⟩
    obtain ⟨m,hm,hmj⟩ := bounded_standard 943 j hj
    let i : Fin 943 := ⟨m,hm⟩
    have hi : selectorDigit (8807*N) C (8807*h+4393) 4393 i=1 := by
      unfold selectorDigit
      rw [BlockSelectionBridge.selector_index N h i hh]
      simpa only [hmj] using hbit
    rcases hdec with hzero | hsel
    · have h := hzero.1 i
      rw [hi] at h
      exact False.elim (_root_.one_ne_zero h)
    · exact hsel

theorem occupied_successor (N C h : V) (hN : 0<N) (hh : h<N)
    (heq : ∀ k<8807*N,k%8807=1073 →
      dig 67 C (cyc (8807*N) k 62)=dig 67 C (cyc (8807*N) k 8849))
    (hin : UniformBandInputs.Inputs (8807*N) C (8807*h+4393) 4393)
    (hsel : SelectedBlock N C h)
    (hdec : DirectBFSUniformDecoder.Conclusion (8807*N) C (8807*((h+1)%N)+4393) 4393) :
    SelectedBlock N C ((h+1)%N) := by
  let g := (h+1)%N
  have hg : g<N := mod_lt _ hN
  obtain ⟨i,_hi,hw⟩ := hsel
  have hbit := decoded_occupied (8807*N) C (8807*h+4393) 4393 i hin.2.1 hw ⟨34,by decide⟩ (by decide)
  unfold copyDigit at hbit
  have hidx := BlockSelectedMarker.copy_index N h 4393 ⟨34,by decide⟩ hh (by decide) (by decide)
  simp only [Nat.cast_ofNat] at hidx
  rw [hidx] at hbit
  have hmarker : dig 67 C (8807*h+1031)=1 := by simpa [position,slots] using hbit
  have he := MarkerBlockIndex.marker N C g hN hg heq
  rw [show cyc N g 1=h from BlockOrbit.forward_back N h 1 hN hh,hmarker] at he
  apply selected_of_copy_one (8807*N) C (8807*g+4393) 4393 ⟨36,by decide⟩ _ hdec
  unfold copyDigit
  have hidx2 := BlockSelectedMarker.copy_index N g 4393 ⟨36,by decide⟩ hg (by decide) (by decide)
  simp only [Nat.cast_ofNat] at hidx2
  rw [hidx2]
  simpa [position,slots] using he

theorem orbit_all (C N s : V) (hN : 0<N)
    (hdec : ∀ h<N,DirectBFSUniformDecoder.Conclusion (8807*N) C (8807*h+4393) 4393)
    (hbase : SelectedBlock N C 0)
    (hstep : ∀ h<N,SelectedBlock N C h → SelectedBlock N C ((h+s)%N)) :
    ∀ t : V,Occupied C N s t := by
  intro t
  induction t using ISigma1.sigma1_succ_induction
  · unfold Occupied orbit; definability
  case zero =>
    have h0 := (selected_iff_digit N C 0 hN (hdec 0 hN)).1 hbase
    simpa [Occupied,orbit] using h0
  case succ t ih =>
    let h := orbit N s t
    have hh : h<N := mod_lt _ hN
    have hs : SelectedBlock N C h := (selected_iff_digit N C h hh (hdec h hh)).2 ih
    have hn := hstep h hh hs
    have hnext : orbit N s (t+1)=(h+s)%N := InternalOrbit.orbit_next N s t hN
    have hnextlt : (h+s)%N<N := mod_lt _ hN
    have hdigit := (selected_iff_digit N C ((h+s)%N) hnextlt (hdec _ hnextlt)).1 hn
    unfold Occupied
    rw [hnext]
    exact hdigit

#print axioms DirectBFSBlockOrbit.decoded_occupied
#print axioms DirectBFSBlockOrbit.selected_iff_digit
#print axioms DirectBFSBlockOrbit.occupied_successor
#print axioms DirectBFSBlockOrbit.orbit_all
end DirectBFSBlockOrbit
