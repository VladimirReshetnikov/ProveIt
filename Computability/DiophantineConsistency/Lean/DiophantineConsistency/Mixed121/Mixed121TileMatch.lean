import DiophantineConsistency.Mixed121.Mixed121FieldMatch

/-! # Neighbouring tiles match as Wang tiles, at 121x8801

This is the 121x8801 counterpart of Compact44's `TilePayloadFields` and
`graph_tile_match_facts`.

Every tile label is below `512`, so `x + 512` has exactly ten bits, and they
are the ten radix-four digits of the label's field. The field equalities of
`Mixed121FieldMatch` therefore determine the labels (`bits_eq`). For every
block `h` with tile `i`, temporal predecessor tile `j` and spatial neighbour
tile `l`:

* `south(i) = north(j)`;
* `east(i) = west(l)`.

These are the Wang tiling constraints. Tiles are quadruples in west, north,
east, south order. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Mixed121TileMatch
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ArithmeticWindowDigits ArithmeticCyclicWord ArithmeticRepunit ArithmeticPackingBlocks
open Mixed121BlockWord

/-- Two numbers below `2^10` with the same ten low bits are equal. -/
theorem bits_eq (a b : ℕ) (ha : a < 2^10) (hb : b < 2^10)
    (h : ∀ u < 10, a / 2^u % 2 = b / 2^u % 2) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 10
  · rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq, h i hi]
  · have hle : 2^10 ≤ 2^i := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha hle),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hb hle)]

theorem digit_south (t : ℕ × ℕ × ℕ × ℕ) (u : ℕ) (hu : u<10) :
    Mixed121Digits.digit t (30+u) = Mixed121Digits.bit t.2.2.2 u := by
  unfold Mixed121Digits.digit
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
    Nat.add_sub_cancel_left]

theorem digit_north (t : ℕ × ℕ × ℕ × ℕ) (u : ℕ) (hu : u<10) :
    Mixed121Digits.digit t (10+u) = Mixed121Digits.bit t.2.1 u := by
  unfold Mixed121Digits.digit
  rw [if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]

theorem digit_east (t : ℕ × ℕ × ℕ × ℕ) (u : ℕ) (hu : u<10) :
    Mixed121Digits.digit t (20+u) = Mixed121Digits.bit t.2.2.1 u := by
  unfold Mixed121Digits.digit
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]

theorem digit_west (t : ℕ × ℕ × ℕ × ℕ) (u : ℕ) (hu : u<10) :
    Mixed121Digits.digit t u = Mixed121Digits.bit t.1 u := by
  unfold Mixed121Digits.digit
  rw [if_pos hu]

theorem labels (i : Fin 943) :
    (Compact943Data.row i).1 < 512 ∧ (Compact943Data.row i).2.1 < 512 ∧
      (Compact943Data.row i).2.2.1 < 512 ∧ (Compact943Data.row i).2.2.2 < 512 := by
  have hm : Compact943Data.row i ∈ Compact943Data.rows := List.get_mem Compact943Data.rows _
  exact of_decide_eq_true ((List.all_eq_true.mp Mixed121Kernel.labels_below) _ hm)

/-- Labels below `512` with equal field digits are equal. -/
theorem label_eq (x y : ℕ) (hx : x<512) (hy : y<512)
    (h : ∀ u < 10, Mixed121Digits.bit x u = Mixed121Digits.bit y u) : x = y := by
  have := bits_eq (x+512) (y+512) (by norm_num; omega) (by norm_num; omega)
    (fun u hu => by simpa only [Mixed121Digits.bit] using h u hu)
  omega

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

attribute [local irreducible] Compact943Data.rows Mixed121Flatten.selectors Mixed121Flatten.copies
attribute [local irreducible] Mixed121Ports.betaNat Mixed121Ports.lowNat Mixed121Ports.highNat
  Mixed121Kernel.paramKernel Mixed121Kernel.rho

theorem graph_tile_match (v : Fin 12 → V) (hv : ∀ j, 0 < v j)
    (hz : CompactLeafFacts.LeafFacts Mixed121Ports.ports v) :
    let p := Mixed121Ports.ports
    let q : V := 1+v 0*(p 0:V)
    let C : V := q-v 1-v 2
    ∃ N W s : V, 0<N ∧ q=Exp.exp ((121*8801)*N) ∧ s<N ∧
      Blocks 10 (row C N 1) N W ∧
      (∀ h<N, row C N 1 h<943 ∧ row C N 1 h≠1) ∧
      ∀ h<N, ∃ i j l : Fin 943,
        row C N 1 h=(i.val:V) ∧ row C N 1 (cyc N h s)=(j.val:V) ∧
        row C N 1 (cyc N h 1)=(l.val:V) ∧
        (Compact943Data.row i).2.2.2=(Compact943Data.row j).2.1 ∧
        (Compact943Data.row i).2.2.1=(Compact943Data.row l).1 := by
  obtain ⟨N,W,s,hN,hq,hs,hW,hbound,hfields⟩ := Mixed121FieldMatch.graph_field_match v hv hz
  refine ⟨N,W,s,hN,hq,hs,hW,hbound,?_⟩
  intro h hh
  obtain ⟨i,j,l,hi,hj,hl,hvert,hhor⟩ := hfields h hh
  refine ⟨i,j,l,hi,hj,hl,?_,?_⟩
  · apply label_eq _ _ (labels i).2.2.2 (labels j).2.1
    intro u hu
    have := hvert u hu
    rw [digit_south _ u hu, digit_north _ u hu] at this
    exact this
  · apply label_eq _ _ (labels i).2.2.1 (labels l).1
    intro u hu
    have := hhor u hu
    rw [digit_east _ u hu, digit_west _ u hu] at this
    exact this
end Mixed121TileMatch
#print axioms Mixed121TileMatch.bits_eq
#print axioms Mixed121TileMatch.label_eq
#print axioms Mixed121TileMatch.graph_tile_match
