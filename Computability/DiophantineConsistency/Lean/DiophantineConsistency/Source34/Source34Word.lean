import DiophantineConsistency.Compact44.CompactHaltWord
import DiophantineConsistency.Source34.Source34Cell
import DiophantineConsistency.Source34.Source34Calibration
import DiophantineConsistency.Mixed121.Mixed121Word
import DiophantineConsistency.ArithmeticModularCancellation

/-! # The packed halting word at the source34 ports

`Mixed121Word` at the source34 tuple. Generic and used from `Mixed121Word`:
the halt dimensions and geometry (`dimensions`, `geometry`,
`halt_compact_word_powers`), `subdigit`, the halt word itself (`haltRow`,
`haltLength`, `haltStride`), `one_noCarry_even`, `swap_origin_bit` and the
marker facts (`marker_north`, `marker_south`, `predecessor_ne_marker`).

Re-declared on the source34 cell (`Source34Cell`):

* `packedWord row dummy N` packs one native cell per block, at block width
  `121·8801`. Its digits are the cell digits; the copy tracks are the labels'
  bits at the even cells `o + 2u`, so the vertical neighbours agree on
  south `960 + 2u` / north `1000 + 2u` and the horizontal ones on
  east `980 + 2u` / west `1020 + 2u` (`vertical_digits`, `horizontal_digits`).
* The base word (all controller bits zero) is carry-free against `MC` cell by
  cell, because every supported digit of `MC` is even (`B − 4` at `1063`,
  `B − 2` elsewhere). The origin cell is odd, so moving its low bit to the
  mask keeps it carry-free (`origin_low_noCarry`), and a Boolean controller
  pulse away from the origin keeps every cell carry-free
  (`pulsed_low_fields`). -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace Source34Word
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticPow ArithmeticWindowDigits ArithmeticPackingBlocks ArithmeticBinaryCarry
  ArithmeticMaskConstants ArithmeticStandardCasts ArithmeticCyclicWord
open CompactRowTransport CompactForwardCellInputs CompactWordCellClient CompactMarkedTransport
open Source34Cell ArithmeticTilingWord
open Mixed121Word (halt_compact_word_powers subdigit haltRow haltLength
  haltStride one_noCarry_even swap_origin_bit predecessor_ne_marker)
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## The packed word -/

def cellWord (row dummy : V → V) (j : V) : V := normalizedCell (row j) (dummy j)
def packedWord (row dummy : V → V) (N : V) : V := bsum (121*8801) (cellWord row dummy) N

instance cellWord_definable (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy] :
    𝚺₁-Function₁ (cellWord row dummy) := word_definable row dummy

theorem packedWord_lt (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy] (N : V) :
    packedWord row dummy N < Exp.exp ((121*8801)*N) := by
  exact bsum_lt (fun j _ => word_cell_lt row dummy j)

theorem word_digit (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    (N j p : V) (hj : j < N) (hp : p < 8801) :
    dig 121 (packedWord row dummy N) (8801*j+p) = cellDigit (row j) (dummy j % 2) p := by
  letI : 𝚺₁-Function₁ (fun k => normalizedCell (row k) (dummy k)) := word_definable row dummy
  unfold packedWord cellWord
  rw [← subdigit _ _ _ hp, dig_bsum (fun k _ => word_cell_lt row dummy k) hj]
  exact packedCell_digit _ _ _ (lt_two_iff_le_one.mp (mod_lt _ (by norm_num))) hp

theorem word_digit_cap (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    (N j p : V) (hj : j < N) (hp : p < 8801) :
    dig 121 (packedWord row dummy N) (8801*j+p) ≤ 1 := by
  rw [word_digit row dummy N j p hj hp]
  exact cellDigit_le_one _ _ _ (lt_two_iff_le_one.mp (mod_lt _ (by norm_num)))

theorem word_selector (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    (N j : V) (hj : j < N) (i : Fin 943) :
    dig 121 (packedWord row dummy N) (8801*j+(i.val : V)) = wordSelector row i j := by
  rw [word_digit row dummy N j _ hj (by exact_mod_cast (show i.val < 8801 by have := i.isLt; omega))]
  exact selector_digit _ _ i

theorem word_dummy (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    (N j : V) (hj : j < N) :
    dig 121 (packedWord row dummy N) (8801*j+1063) = dummy j % 2 := by
  rw [word_digit row dummy N j 1063 hj (by norm_num)]
  exact dummy_digit _ _

theorem word_south (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    (N j : V) (hj : j < N) (u : ℕ) (hu : u < 10) :
    dig 121 (packedWord row dummy N) (8801*j+((960+2*u:ℕ):V)) =
      fbit (compactField (fun t => t.2.2.2) (row j) + 512) (u:V) := by
  rw [word_digit row dummy N j _ hj (by exact_mod_cast (show 960+2*u < 8801 by omega))]
  exact at_south _ _ u hu

theorem word_east (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    (N j : V) (hj : j < N) (u : ℕ) (hu : u < 10) :
    dig 121 (packedWord row dummy N) (8801*j+((980+2*u:ℕ):V)) =
      fbit (compactField (fun t => t.2.2.1) (row j) + 512) (u:V) := by
  rw [word_digit row dummy N j _ hj (by exact_mod_cast (show 980+2*u < 8801 by omega))]
  exact at_east _ _ u hu

theorem word_north (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    (N j : V) (hj : j < N) (u : ℕ) (hu : u < 10) :
    dig 121 (packedWord row dummy N) (8801*j+((1000+2*u:ℕ):V)) =
      fbit (compactField (fun t => t.2.1) (row j) + 512) (u:V) := by
  rw [word_digit row dummy N j _ hj (by exact_mod_cast (show 1000+2*u < 8801 by omega))]
  exact at_north _ _ u hu

theorem word_west (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    (N j : V) (hj : j < N) (u : ℕ) (hu : u < 10) :
    dig 121 (packedWord row dummy N) (8801*j+((1020+2*u:ℕ):V)) =
      fbit (compactField (fun t => t.1) (row j) + 512) (u:V) := by
  rw [word_digit row dummy N j _ hj (by exact_mod_cast (show 1020+2*u < 8801 by omega))]
  exact at_west _ _ u hu

theorem word_anchor (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    (N j : V) (hj : j < N) (n : ℕ) (hn : n = 1095 ∨ n = 1096 ∨ n = 2195 ∨ n = 3296) :
    dig 121 (packedWord row dummy N) (8801*j+(n:V)) = 1 := by
  rw [word_digit row dummy N j _ hj (by exact_mod_cast (show n < 8801 by omega))]
  exact at_anchor _ _ n hn

theorem word_definable_length (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy] :
    𝚺₁-Function₁ (packedWord row dummy) := by
  apply bsum_definable
  exact word_cell_lt row dummy

theorem word_cap (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    (N k : V) (hk : k < 8801*N) : dig 121 (packedWord row dummy N) k ≤ 1 := by
  have hj : k/8801 < N := div_lt_of_lt_mul (by simpa only [mul_comm] using hk)
  have hp : k%8801 < 8801 := mod_lt k (by norm_num)
  have he : 8801*(k/8801)+k%8801 = k := div_add_mod k 8801
  rw [← he]
  exact word_digit_cap row dummy N _ _ hj hp

theorem marked_word_origin (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    (N s : V) (hword : CompactWord row N s) : 1 ≤ packedWord row dummy N := by
  have h := word_selector row dummy N 0 hword.pos ⟨0, by decide⟩
  have hzero : dig 121 (packedWord row dummy N) 0 = 1 := by
    simpa [wordSelector, selector, hword.marker] using h
  rw [dig_zero_index] at hzero
  rw [← hzero]
  exact mod_le _ _

/-! ## The halting word -/

def haltPacked (T : V) (dummy : V → V) : V := packedWord (haltRow T) dummy (haltLength T)

theorem halt_packed_word (T : V) (dummy : V → V) [𝚺₁-Function₁ dummy]
    (hT : ArithmeticCantor.first (ArithmeticMachineRun215.run T)=0) :
    (𝚺₁-Function₁ (haltRow T)) ∧
    CompactWord (haltRow T) (haltLength T) (haltStride T) ∧
    1 ≤ haltPacked T dummy ∧
    haltPacked T dummy < Exp.exp ((121*8801)*haltLength T) ∧
    (∀ k < 8801*haltLength T, dig 121 (haltPacked T dummy) k ≤ 1) ∧
    (∀ j < haltLength T, ∀ i : Fin 943,
      dig 121 (haltPacked T dummy) (8801*j+(i.val:V)) = wordSelector (haltRow T) i j) ∧
    (∀ j < haltLength T,
      dig 121 (haltPacked T dummy) (8801*j+1063) = dummy j % 2) := by
  obtain ⟨hrow, hword⟩ := halt_compact_word_powers T hT
  have he := (Mixed121Word.dimensions T).2.2.2
  rw [he] at hword
  change 𝚺₁-Function₁ (haltRow T) at hrow
  letI : 𝚺₁-Function₁ (haltRow T) := hrow
  have hw : CompactWord (haltRow T) (haltLength T) (haltStride T) := hword
  refine ⟨hrow, hw, ?_, ?_, ?_, ?_, ?_⟩
  · exact marked_word_origin _ _ _ _ hw
  · exact packedWord_lt _ _ _
  · exact word_cap _ _ _
  · exact word_selector _ _ _
  · exact word_dummy _ _ _

/-! ## Neighbouring field windows -/

/-- The vertical field windows compare the current south bits with the
vertical predecessor's north bits. -/
theorem vertical_digits {row dummy : V → V} [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    {N s j j' : V} (hw : CompactWord row N s) (hj : j<N) (hj' : j'<N)
    (he : (j'+s)%N=j) (u : ℕ) (hu : u<10) :
    dig 121 (packedWord row dummy N) (8801*j+((960+2*u:ℕ):V)) =
      dig 121 (packedWord row dummy N) (8801*j'+((1000+2*u:ℕ):V)) := by
  rw [word_south row dummy N j hj u hu, word_north row dummy N j' hj' u hu, hw.south j hj j' hj' he]

/-- The horizontal field windows compare the current east bits with the
horizontal predecessor's west bits. -/
theorem horizontal_digits {row dummy : V → V} [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    {N s j j' : V} (hw : CompactWord row N s) (hj : j<N) (hj' : j'<N)
    (he : (j'+1)%N=j) (u : ℕ) (hu : u<10) :
    dig 121 (packedWord row dummy N) (8801*j+((980+2*u:ℕ):V)) =
      dig 121 (packedWord row dummy N) (8801*j'+((1020+2*u:ℕ):V)) := by
  rw [word_east row dummy N j hj u hu, word_west row dummy N j' hj' u hu, hw.east j hj j' hj' he]

/-! ## Low-mask fields -/

/-- The `MC` digit at each supported position is even. -/
theorem supported_mask_even (n : ℕ) (hn : n < 8801)
    (hs : n ∈ Source34Ports.maskSupport) :
    dig 121 ((Source34Ports.lowNat : ℕ) : V) (n : V) % 2 = 0 := by
  have hd := dig_ofDigits (V:=V) 121
    (CompactListMask.digits (2^121) 8801 1063 Source34Ports.maskSupport)
    (CompactListMask.digits_lt _ _ _ _ (by norm_num)) n
  rw [CompactListMask.digits_getD _ _ _ _ hn] at hd
  have hd' : dig 121 ((Source34Ports.lowNat : ℕ) : V) (n : V) =
      ((CompactListMask.digit (2^121) 1063 Source34Ports.maskSupport n : ℕ) : V) := by
    rw [Source34Masks.lowNat_eq]; exact hd
  rw [hd']
  by_cases hsp : n = 1063
  · subst n
    simp only [CompactListMask.digit, ↓reduceIte]
    change (((2^121-4 : ℕ) : V) % ((2:ℕ):V)) = 0
    rw [← ArithmeticStandardCasts.cast_mod]
    norm_num
  · simp only [CompactListMask.digit, hsp, if_false, hs, if_true]
    change (((2^121-2 : ℕ) : V) % ((2:ℕ):V)) = 0
    rw [← ArithmeticStandardCasts.cast_mod]
    norm_num

/- From here on the million-bit masks must stay folded: with `lowNat` reducible,
`local_noCarry` did not elaborate in four minutes. -/
attribute [local irreducible] Source34Ports.lowNat Source34Ports.highNat

/-- All individual subdigits of a base cell avoid the corresponding mask digit. -/
theorem local_noCarry (a k : V) (ha : a ≠ 1) (hk : k < 8801) :
    NoCarry (cellDigit a 0 k) (dig 121 ((Source34Ports.lowNat : ℕ) : V) k) := by
  have hb := cellDigit_le_one a 0 k (by simp)
  rcases le_one_iff_eq_zero_or_one.mp hb with hz | ho
  · rw [hz, noCarry_iff]; intro i; simp
  · obtain ⟨n, he, hs⟩ := cellDigit_supported a 0 k ha hk (by rw [ho]; simp)
    have hn : n < 8801 := by rw [he] at hk; exact_mod_cast hk
    rw [ho, he]
    exact one_noCarry_even _ (supported_mask_even n hn hs)

/-- A base cell is disjoint from `MC`. -/
theorem base_noCarry (a : V) (ha : a ≠ 1) :
    NoCarry (packedCell a 0) ((Source34Ports.lowNat : ℕ) : V) := by
  letI : 𝚺₁-Function₁ (cellDigit a (0 : V)) := cellDigit_definable a 0
  let g : V → V := fun j => dig 121 ((Source34Ports.lowNat : ℕ) : V) j
  letI : 𝚺₁-Function₁ g := by unfold g; definability
  have hmask : bsum 121 g 8801 = ((Source34Ports.lowNat : ℕ) : V) := by
    apply bsum_unique (f := g) (fun j _ => dig_lt 121 ((Source34Ports.lowNat : ℕ) : V) j)
    exact ⟨Source34Masks.model_low_lt, fun j _ => rfl⟩
  have hc := bsum_noCarry (w := (121 : V)) (f := cellDigit a 0) (g := g) (n := 8801)
    (fun j _ => digit_bound a 0 (by simp) j) (fun j _ => dig_lt 121 _ j)
    (fun j hj => local_noCarry a j ha hj)
  unfold packedCell
  rwa [hmask] at hc

theorem origin_odd : (packedCell (0 : V) 0) % 2 = 1 := by
  have hs := packedCell_selector (0 : V) 0 (by simp) ⟨0, by decide⟩
  have hd : dig 121 (packedCell (0 : V) 0) 0 = 1 := by simpa [selector] using hs
  have hb := fbit_dig (121 : V) (packedCell (0 : V) 0) 0 0 (by norm_num)
  rw [hd] at hb
  have hone : fbit (1 : V) 0 = 1 := by
    rw [fbit_eq_div, exp_zero, Arithmetic.div_one]
    norm_num
  rw [hone] at hb
  have hf : fbit (packedCell (0 : V) 0) 0 = 1 := by
    simpa only [mul_zero, add_zero] using hb.symm
  simpa only [fbit_eq_div, exp_zero, Arithmetic.div_one] using hf

theorem origin_low_noCarry :
    NoCarry (packedCell (0 : V) 0 - 1) (((Source34Ports.lowNat : ℕ) : V) + 1) := by
  apply swap_origin_bit
  · exact base_noCarry 0 (by norm_num)
  · exact origin_odd
  · have hs := supported_mask_even (V:=V) 0 (by norm_num) Source34Ports.zero_mem_support
    have hf := fbit_dig (121 : V) ((Source34Ports.lowNat : ℕ) : V) 0 0 (by norm_num)
    have hz : fbit (dig 121 ((Source34Ports.lowNat : ℕ) : V) 0) 0 = 0 := by
      rw [fbit_eq_div, exp_zero, Arithmetic.div_one]
      simpa using hs
    have hbit : fbit ((Source34Ports.lowNat : ℕ) : V) 0 = 0 := by
      simpa only [mul_zero, add_zero] using hf.symm.trans hz
    simpa only [fbit_eq_div, exp_zero, Arithmetic.div_one] using hbit

def baseCell (row : V → V) (j : V) : V := packedCell (row j) 0
def pulsedCell (row δ : V → V) (j : V) : V :=
  baseCell row j + Exp.exp (121*1063) * δ j

/-- Exactly the origin and local low-mask fields for the base word. -/
theorem base_low_fields {row : V → V} {N s : V} (hw : CompactWord row N s) :
    1 ≤ baseCell row 0 ∧
    NoCarry (baseCell row 0 - 1) (((Source34Ports.lowNat : ℕ) : V) + 1) ∧
    (∀ j < N, NoCarry (baseCell row j) ((Source34Ports.lowNat : ℕ) : V)) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold baseCell
    rw [hw.marker]
    exact packedCell_origin 0 (by simp)
  · unfold baseCell
    rw [hw.marker]
    exact origin_low_noCarry
  · intro j hj
    exact base_noCarry (row j) (hw.tile_ne j hj)

/-- The same fields after any Boolean perturbation away from the origin. -/
theorem pulsed_low_fields {row δ : V → V} {N s : V} (hw : CompactWord row N s)
    (hbool : ∀ j, δ j ≤ 1) (hpos : ∀ j, δ j ≠ 0 → 0 < j) :
    1 ≤ pulsedCell row δ 0 ∧
    NoCarry (pulsedCell row δ 0 - 1) (((Source34Ports.lowNat : ℕ) : V) + 1) ∧
    (∀ j < N, NoCarry (pulsedCell row δ j) ((Source34Ports.lowNat : ℕ) : V)) := by
  have hz : δ 0 = 0 := by
    by_contra hne
    exact (Arithmetic.lt_irrefl (0 : V)) (hpos 0 hne)
  have h0 : pulsedCell row δ 0 = baseCell row 0 := by
    simp only [pulsedCell, hz, mul_zero, add_zero]
  obtain ⟨ho, hlo, hlow⟩ := base_low_fields hw
  refine ⟨?_, ?_, ?_⟩
  · rw [h0]; exact ho
  · rw [h0]; exact hlo
  · intro j hj
    rcases le_one_iff_eq_zero_or_one.mp (hbool j) with hzero | hone
    · simpa only [pulsedCell, hzero, mul_zero, add_zero] using hlow j hj
    · have hbase := hlow j hj
      have hp := packedCell_pulse_noCarry (row j) hbase
      simpa only [pulsedCell, baseCell, hone, mul_one] using hp

/-! ## Block residues -/

/-- The first selector digit is zero away from marker row zero. -/
theorem cell_mod_four (a d : V) (ha : a ≠ 0) (hd : d ≤ 1) : packedCell a d % 4 = 0 := by
  have hs := packedCell_selector a d hd ⟨0, by decide⟩
  have hz : dig 121 (packedCell a d) 0 = 0 := by simpa [selector, ha] using hs
  rw [dig_zero_index] at hz
  have hdiv : (4:V) ∣ Exp.exp 121 := by
    have he : Exp.exp (121:V) = (4:V)*Exp.exp 119 := by
      have he2 : Exp.exp (2:V) = (4:V) := by simpa using ArithmeticStandardCasts.cast_exp (V:=V) 2
      rw [← he2, ← exp_add]
      norm_num
    rw [he]
    exact dvd_mul_right _ _
  have hmod := ArithmeticModularCancellation.mod_mod_of_dvd (by norm_num : (0:V) < 4) hdiv (packedCell a d)
  rw [hz] at hmod
  simpa using hmod.symm

#print axioms Source34Word.halt_packed_word
#print axioms Source34Word.vertical_digits
#print axioms Source34Word.horizontal_digits
#print axioms Source34Word.pulsed_low_fields
#print axioms Source34Word.cell_mod_four
end Source34Word
