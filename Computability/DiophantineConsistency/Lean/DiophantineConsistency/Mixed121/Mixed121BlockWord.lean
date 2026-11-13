import DiophantineConsistency.Mixed121.Mixed121AllBlocks
import DiophantineConsistency.ArithmeticPackingBlocks

/-! # The row word of selected tiles, at 121x8801

This is the 121x8801 counterpart of Compact44's `SelectorPosition`,
`OrbitRowWord` and `graph_all_block_word_facts`.

`selPos C 943 h = Σ_{m<943} m·C(8801h + m)` reads the selected tile of block
`h`, because exactly one selector cell of a selected block holds `1`
(`selected_position`). As a `𝚺₁` function of `h` it is packed into a single
word `W` with `10`-bit blocks (`943 < 1024`; `represented`).

`graph_all_block_word` states this for the 121x8801 ports. Every block's row
is a tile index below `943`, and its copy digits are that tile's digits. The
row is never `1`, the globally impossible tile: its selector cell
`8801h + 1` has low-mask digit `B − 1`, because `1` is not in the mask support,
so the cell is `0`. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Mixed121BlockWord
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ArithmeticWindowDigits ArithmeticCyclicWord ArithmeticRepunit ArithmeticPackingBlocks
open ArithmeticBinaryCarry
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def selPos (C : V) : ℕ → V → V
  | 0, _ => 0
  | m+1, h => selPos C m h + (m:V)*dig 121 C (8801*h+(m:V))

instance selPos_definable (C : V) (m : ℕ) : 𝚺₁-Function₁ (selPos C m) := by
  induction m with
  | zero =>
    change 𝚺₁-Function₁ (fun _ : V => (0:V))
    definability
  | succ m ih =>
    change 𝚺₁-Function₁ (fun h : V => selPos C m h + (m:V)*dig 121 C (8801*h+(m:V)))
    definability

theorem selected_position (N C h : V) (hh : h<N) (i : Fin 943)
    (hi : CompactSelectorSum.Selected (Mixed121Band.selDigit (8801*N) C (8801*h+4393) 4393) i) :
    selPos C 943 h=(i.val:V) := by
  have h1 : dig 121 C (8801*h+(i.val:V))=1 := by
    have hs := hi.1
    unfold Mixed121Band.selDigit at hs
    rw [Mixed121AllBlocks.selector_index N h i hh] at hs
    exact hs
  have h0 (m : ℕ) (hm : m<943) (hne : m≠i.val) : dig 121 C (8801*h+(m:V))=0 := by
    let j : Fin 943 := ⟨m,hm⟩
    have hj : j≠i := by
      intro he
      exact hne (congrArg Fin.val he)
    have hs := hi.2 j hj
    unfold Mixed121Band.selDigit at hs
    rw [Mixed121AllBlocks.selector_index N h j hh] at hs
    exact hs
  have hsum : ∀ m : ℕ, m≤943 → selPos C m h = if i.val<m then (i.val:V) else 0 := by
    intro m
    induction m with
    | zero => intro _; simp [selPos]
    | succ m ih =>
      intro hm
      rw [selPos,ih (by omega)]
      by_cases he : m=i.val
      · subst m
        rw [h1,if_neg (_root_.lt_irrefl _),if_pos (Nat.lt_succ_self _)]
        simp
      · rw [h0 m (by omega) he,mul_zero,add_zero]
        by_cases hl : i.val<m
        · rw [if_pos hl,if_pos (by omega)]
        · rw [if_neg hl,if_neg (by omega)]
  simpa only [if_pos i.isLt] using hsum 943 le_rfl

/-- The selected tile index of the block at orbit step `t`. -/
def row (C N s t : V) : V := selPos C 943 (Mixed121AllBlocks.orbit N s t)
instance row_definable (C N s : V) : 𝚺₁-Function₁ (row C N s) := by
  unfold row Mixed121AllBlocks.orbit
  definability

theorem row_selected (C N s t : V) (hN : 0<N)
    (hdec : ∀ h<N, Mixed121Uniform.DecodedAt (8801*N) C (8801*h+4393) 4393)
    (hocc : Mixed121AllBlocks.Occupied C N s t) :
    ∃ i : Fin 943, row C N s t=(i.val:V) ∧
      CompactSelectorSum.Selected
        (Mixed121Band.selDigit (8801*N) C (8801*Mixed121AllBlocks.orbit N s t+4393) 4393) i ∧
      ∀ j < 44, Mixed121Band.copyDigit (8801*N) C (8801*Mixed121AllBlocks.orbit N s t+4393) 4393 j =
        (Mixed121Digits.digit (Compact943Data.row i) j : V) := by
  let h := Mixed121AllBlocks.orbit N s t
  have hh : h<N := mod_lt _ hN
  have hsel := (Mixed121AllBlocks.selected_iff_digit N C h hh (hdec h hh)).2 hocc
  rcases hdec h hh with ⟨hz, _⟩ | ⟨i, hi, hcopy⟩
  · obtain ⟨i, hi⟩ := hsel
    have := hz i
    rw [hi.1] at this
    exact absurd this _root_.one_ne_zero
  · exact ⟨i, selected_position N C h hh i hi, hi, hcopy⟩

theorem bounded (C N s : V) (hN : 0<N)
    (hdec : ∀ h<N, Mixed121Uniform.DecodedAt (8801*N) C (8801*h+4393) 4393)
    (hocc : ∀ t, Mixed121AllBlocks.Occupied C N s t) : ∀ t, row C N s t<943 := by
  intro t
  obtain ⟨i,he,_,_⟩ := row_selected C N s t hN hdec (hocc t)
  rw [he]
  exact_mod_cast i.isLt

theorem represented (C N s : V) (hN : 0<N)
    (hdec : ∀ h<N, Mixed121Uniform.DecodedAt (8801*N) C (8801*h+4393) 4393)
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

theorem one_not_mem : (1:ℕ) ∉ Mixed121Ports.maskSupport := by
  unfold Mixed121Ports.maskSupport
  rw [List.mem_toFinset, List.mem_filter]
  intro h
  exact absurd h.2 (by decide)

attribute [local irreducible] Compact943Data.rows Mixed121Flatten.selectors Mixed121Flatten.copies
attribute [local irreducible] Mixed121Ports.betaNat Mixed121Ports.lowNat Mixed121Ports.highNat
  Mixed121Kernel.paramKernel Mixed121Kernel.rho

theorem graph_all_block_word (v : Fin 12 → V) (hv : ∀ j, 0 < v j)
    (hz : CompactLeafFacts.LeafFacts Mixed121Ports.ports v) :
    let p := Mixed121Ports.ports
    let q : V := 1+v 0*(p 0:V)
    let C : V := q-v 1-v 2
    ∃ N W : V, 0<N ∧ q=Exp.exp ((121*8801)*N) ∧ v 0=rep (121*8801) N ∧
      Blocks 10 (row C N 1) N W ∧
      (∀ h<N, ∃ i : Fin 943, row C N 1 h=(i.val:V) ∧
        CompactSelectorSum.Selected (Mixed121Band.selDigit (8801*N) C (8801*h+4393) 4393) i ∧
        ∀ j < 44, Mixed121Band.copyDigit (8801*N) C (8801*h+4393) 4393 j =
          (Mixed121Digits.digit (Compact943Data.row i) j : V)) ∧
      (∀ h<N, row C N 1 h<943 ∧ row C N 1 h≠1) := by
  obtain ⟨N,hN,hq,hJ,hdecoder,hall⟩ := Mixed121AllBlocks.graph_all_blocks v hv hz
  obtain ⟨N'',w'',hN'',hq'',hJ'',hv5'',hcongr'',h0,hslots,hhigh⟩ :=
    Mixed121Temporal.position_noCarry v hv hz
  dsimp only at *
  have hNN : N''=N := by
    apply mul_left_cancel₀ (by norm_num : ((121*8801):V)≠0)
    exact exp_inj (hq''.symm.trans hq)
  subst N''
  let C : V := 1+v 0*(Mixed121Ports.ports 0:V)-v 1-v 2
  have hocc : ∀ t : V, Mixed121AllBlocks.Occupied C N 1 t := by
    intro t
    have hh : Mixed121AllBlocks.orbit N 1 t<N := mod_lt _ hN
    exact (Mixed121AllBlocks.selected_iff_digit N C _ hh (hdecoder _ hh)).1 (hall _ hh)
  obtain ⟨W,hW⟩ := represented C N 1 hN hdecoder hocc
  have hrows : ∀ h<N, ∃ i : Fin 943, row C N 1 h=(i.val:V) ∧
      CompactSelectorSum.Selected (Mixed121Band.selDigit (8801*N) C (8801*h+4393) 4393) i ∧
      ∀ j < 44, Mixed121Band.copyDigit (8801*N) C (8801*h+4393) 4393 j =
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
      have hd := Mixed121Clean.absent_mask_digit (V:=V) 1 (by norm_num) one_not_mem (by norm_num)
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
end Mixed121BlockWord
#print axioms Mixed121BlockWord.selected_position
#print axioms Mixed121BlockWord.row_selected
#print axioms Mixed121BlockWord.represented
#print axioms Mixed121BlockWord.graph_all_block_word
