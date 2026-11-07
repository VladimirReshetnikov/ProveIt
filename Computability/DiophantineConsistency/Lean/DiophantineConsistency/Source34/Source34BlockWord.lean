import DiophantineConsistency.Source34.Source34AllBlocks
import DiophantineConsistency.Mixed121.Mixed121BlockWord
import DiophantineConsistency.ArithmeticPackingBlocks

/-! # The row word of selected tiles, at source34

`Mixed121BlockWord` at the source34 tuple. The selector reader
`Mixed121BlockWord.selPos`, the row function `row` and their `𝚺₁`
definability, and `selected_position` read only selector cells and are shared.
Re-declared over `Source34Uniform.DecodedAt` and `Source34Band.copyDigit`:
`row_selected`, `bounded`, `represented`, `one_not_mem` (the source34 mask
support also omits `1`) and the chain link `graph_all_block_word`. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Source34BlockWord
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ArithmeticWindowDigits ArithmeticCyclicWord ArithmeticRepunit ArithmeticPackingBlocks
open ArithmeticBinaryCarry
open Mixed121BlockWord (selPos row row_definable selected_position)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]


theorem row_selected (C N s t : V) (hN : 0<N)
    (hdec : ∀ h<N, Source34Uniform.DecodedAt (8801*N) C (8801*h+4393) 4393)
    (hocc : Mixed121AllBlocks.Occupied C N s t) :
    ∃ i : Fin 943, row C N s t=(i.val:V) ∧
      CompactSelectorSum.Selected
        (Mixed121Band.selDigit (8801*N) C (8801*Mixed121AllBlocks.orbit N s t+4393) 4393) i ∧
      ∀ j < 44, Source34Band.copyDigit (8801*N) C (8801*Mixed121AllBlocks.orbit N s t+4393) 4393 j =
        (Mixed121Digits.digit (Compact943Data.row i) j : V) := by
  let h := Mixed121AllBlocks.orbit N s t
  have hh : h<N := mod_lt _ hN
  have hsel := (Source34AllBlocks.selected_iff_digit N C h hh (hdec h hh)).2 hocc
  rcases hdec h hh with ⟨hz, _⟩ | ⟨i, hi, hcopy⟩
  · obtain ⟨i, hi⟩ := hsel
    have := hz i
    rw [hi.1] at this
    exact absurd this _root_.one_ne_zero
  · exact ⟨i, selected_position N C h hh i hi, hi, hcopy⟩

theorem bounded (C N s : V) (hN : 0<N)
    (hdec : ∀ h<N, Source34Uniform.DecodedAt (8801*N) C (8801*h+4393) 4393)
    (hocc : ∀ t, Mixed121AllBlocks.Occupied C N s t) : ∀ t, row C N s t<943 := by
  intro t
  obtain ⟨i,he,_,_⟩ := row_selected C N s t hN hdec (hocc t)
  rw [he]
  exact_mod_cast i.isLt

theorem represented (C N s : V) (hN : 0<N)
    (hdec : ∀ h<N, Source34Uniform.DecodedAt (8801*N) C (8801*h+4393) 4393)
    (hocc : ∀ t, Mixed121AllBlocks.Occupied C N s t) :
    ∃ W : V, Blocks 10 (row C N s) N W := by
  apply blocks_exists 10 (row C N s) N
  intro t _
  have he : Exp.exp (10:V)=1024 := by
    rw [show (10:V)=9+1 by norm_num,exp_succ]
    have h9 : Exp.exp (9:V)=512 := by
      have h := ArithmeticStandardCasts.cast_exp (V:=V) 9
      norm_num at h
      exact h
    rw [h9]
    norm_num
  rw [he]
  exact lt_trans (bounded C N s hN hdec hocc t) (by norm_num)

theorem one_not_mem : (1:ℕ) ∉ Source34Ports.maskSupport := by
  unfold Source34Ports.maskSupport
  rw [List.mem_toFinset, List.mem_filter]
  intro h
  exact absurd h.2 (by decide)

attribute [local irreducible] Compact943Data.rows Mixed121Flatten.selectors Mixed121Flatten.copies
attribute [local irreducible] Source34Ports.betaNat Source34Ports.lowNat Source34Ports.highNat
  Source34Kernel.paramKernel Mixed121Kernel.rho

theorem graph_all_block_word (v : Fin 12 → V) (hv : ∀ j, 0 < v j)
    (hz : CompactLeafFacts.LeafFacts Source34Ports.ports v) :
    let p := Source34Ports.ports
    let q : V := 1+v 0*(p 0:V)
    let C : V := q-v 1-v 2
    ∃ N W : V, 0<N ∧ q=Exp.exp ((121*8801)*N) ∧ v 0=rep (121*8801) N ∧
      Blocks 10 (row C N 1) N W ∧
      (∀ h<N, ∃ i : Fin 943, row C N 1 h=(i.val:V) ∧
        CompactSelectorSum.Selected (Mixed121Band.selDigit (8801*N) C (8801*h+4393) 4393) i ∧
        ∀ j < 44, Source34Band.copyDigit (8801*N) C (8801*h+4393) 4393 j =
          (Mixed121Digits.digit (Compact943Data.row i) j : V)) ∧
      (∀ h<N, row C N 1 h<943 ∧ row C N 1 h≠1) := by
  obtain ⟨N,hN,hq,hJ,hdecoder,hall⟩ := Source34AllBlocks.graph_all_blocks v hv hz
  obtain ⟨N'',w'',hN'',hq'',hJ'',hv5'',hcongr'',h0,hslots,hhigh⟩ :=
    Source34Temporal.position_noCarry v hv hz
  dsimp only at *
  have hNN : N''=N := by
    apply mul_left_cancel₀ (by norm_num : ((121*8801):V)≠0)
    exact exp_inj (hq''.symm.trans hq)
  subst N''
  let C : V := 1+v 0*(Source34Ports.ports 0:V)-v 1-v 2
  have hocc : ∀ t : V, Mixed121AllBlocks.Occupied C N 1 t := by
    intro t
    have hh : Mixed121AllBlocks.orbit N 1 t<N := mod_lt _ hN
    exact (Source34AllBlocks.selected_iff_digit N C _ hh (hdecoder _ hh)).1 (hall _ hh)
  obtain ⟨W,hW⟩ := represented C N 1 hN hdecoder hocc
  have hrows : ∀ h<N, ∃ i : Fin 943, row C N 1 h=(i.val:V) ∧
      CompactSelectorSum.Selected (Mixed121Band.selDigit (8801*N) C (8801*h+4393) 4393) i ∧
      ∀ j < 44, Source34Band.copyDigit (8801*N) C (8801*h+4393) 4393 j =
        (Mixed121Digits.digit (Compact943Data.row i) j : V) := by
    intro h hh
    have hr := row_selected C N 1 h hN hdecoder (hocc h)
    simpa only [Mixed121AllBlocks.orbit,mul_one,mod_eq_self_of_lt hh] using hr
  refine ⟨N,W,hN,hq,hJ,hW,hrows,?_⟩
  intro h hh
  obtain ⟨i,he,hi,_⟩ := hrows h hh
  constructor
  · rw [he]; exact_mod_cast i.isLt
  · intro hone
    have hi1 : (i.val:V)=1 := he.symm.trans hone
    have i1 : i.val=1 := by exact_mod_cast hi1
    have hiidx := Mixed121Copy.index N h 1 hh (by norm_num)
    have hzero : dig 121 C (8801*h+1)=0 := by
      have hpos : 0<8801*h+1 := by
        exact lt_of_lt_of_le (by norm_num) (le_add_of_nonneg_left (by simp))
      have hn := hslots _ hiidx.1 hpos
      rw [hiidx.2] at hn
      have hd := Source34Clean.absent_mask_digit (V:=V) 1 (by norm_num) one_not_mem (by norm_num)
      simp only [Nat.cast_one] at hd
      rw [hd] at hn
      exact Mixed121Increment.forbidden_zero _ (dig_lt 121 C _) hn
    have hbit := hi.1
    unfold Mixed121Band.selDigit at hbit
    rw [Mixed121AllBlocks.selector_index N h i hh] at hbit
    rw [i1] at hbit
    simp only [Nat.cast_one] at hbit
    rw [hzero] at hbit
    exact _root_.zero_ne_one hbit
end Source34BlockWord
#print axioms Source34BlockWord.row_selected
#print axioms Source34BlockWord.represented
#print axioms Source34BlockWord.graph_all_block_word
