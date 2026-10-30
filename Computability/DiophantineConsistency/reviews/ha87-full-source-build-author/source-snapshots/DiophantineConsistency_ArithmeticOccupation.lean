import DiophantineConsistency.ArithmeticWholeField
import DiophantineConsistency.ArithmeticWangPlane

/-! **S12 — occupation, the tile assignment and the marked word** (soundness spec
§5, B7–B10), in every model `V` of IΣ1.

**Output for the Wang soundness lane (S14).** From the window equations
`H : CellInput N W C F κ` (`ArithmeticCellTransfer`), `marked_word` gives

  `ArithmeticWangPlane.MarkedWord (tileAt C) N ((W / 47) / 2011)`

for the explicit assignment `tileAt C : V → V` (with the instance
`𝚺₁-Function₁ (tileAt C)`): the tile index of the cell `2011·j` is
`invPos (selPos C 942 j)`, where `selPos C 942 j = Σ_{p<942} p·c(2011j+p)` is the
position of the unique selector and `invPos` the 942-entry numeral table of the
inverse physical order. So S14 receives `a = tileAt C`, the stride
`s = ⌊⌊W/47⌋/2011⌋` (natural, unreduced, as in the external `MarkedWord`), and
`N` itself; it needs to supply nothing else. It composes directly with
`ArithmeticWangSoundness.marked_halts`.

Steps: after alignment (`ArithmeticWholeField.aligned`) the temporal source of
`b + h` is `θ b + h` with `θ b` a cell, so the spatial parity becomes the East/West
copy (the temporal bit at `987+j` reads an unsupported residue) and the South copy
reads the North block of `θ b` (B7). Occupation of the cell `2011·j` is an IΣ1
induction on `j` (B8): a held tile has West `< 250`, so its complemented West bits
are not all zero, and the East copy then excludes an empty successor. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticOccupation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticWindowDigits ArithmeticCyclicWord 
  ArithmeticCellTransfer ArithmeticCellDecoding ArithmeticWholeField WangTiles942 ArithmeticCellPhysical

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### Elementary residues -/

theorem mul_mod_mul {m a c : V} (hm : 0 < m) (hc : 0 < c) : (m * a) % (m * c) = m * (a % c) :=
  ArithmeticModularCancellation.mul_mod_mul hm hc

theorem cell_of_index {N j : V} (hj : j < N) : IsCell N (2011 * j) :=
  ⟨mul_lt_mul_of_pos_left hj (by norm_num), by simp⟩

/-! ### The aligned copies -/

/-- The temporal cell `θ b` of an aligned window. -/
abbrev tcell (N W b : V) : V := cyc (2011 * N) b (shiftD (2011 * N) (W / 47) ((0:ℕ):V))

theorem bits_eq {C b b' : V} {o o' len x y : ℕ} (hx : x < 2 ^ len) (hy : y < 2 ^ len)
    (h1 : LabelBits C b o len x) (h2 : LabelBits C b' o' len y)
    (hc : ∀ k, k < len → dig 47 C (b + ((o + k : ℕ) : V)) = dig 47 C (b' + ((o' + k : ℕ) : V))) :
    x = y := by
  apply eq_of_bits hx hy
  intro k hk
  have := hc k hk
  rw [h1 k hk, h2 k hk] at this
  exact_mod_cast this

section window
variable {N W C F : V} {κ : V → V} (H : CellInput N W C F κ)
include H

private theorem hr0 : (W / 47) % 2011 = ((0:ℕ):V) := by rw [aligned H, Nat.cast_zero]

private theorem bit01 {k : V} (hk : k < 2011 * N) : ∃ x : ℕ, x ≤ 1 ∧ dig 47 C k = x := by
  obtain ⟨x, hx⟩ := std_of_le (m := 1) (by simpa using H.boolean k hk)
  exact ⟨x, by have := H.boolean k hk; rw [hx] at this; exact_mod_cast this, hx⟩

private theorem cell_lt' {b : V} (hb : IsCell N b) {q : ℕ} (hq : q < 2011) : b + (q:V) < 2011 * N :=
  lt_of_lt_of_le ((add_lt_add_iff_left _).mpr (by exact_mod_cast hq)) (cell_room hb.1 hb.2)

/-- **East/West copy (B7)**: `c(b+969+k) = c(b'+978+k)`, `b'` the previous cell. -/
theorem east_copy {b : V} (hb : IsCell N b) {k : ℕ} (hk : k < 8) :
    dig 47 C (b + ((969 + k : ℕ) : V)) = dig 47 C (prevCell (2011 * N) b + ((978 + k : ℕ) : V)) := by
  have hp := spatial_parity H hb hk
  have hz : dig 47 C (cyc (2011 * N) (b + ((987 + k : ℕ) : V)) (W / 47)) = 0 := by
    have hn : (0:V) < 2011 * N := mul_pos (by norm_num) H.N_pos
    apply H.support _ (cyc_lt hn _ _)
    rw [temporal_mod H.N_pos (hr0 H) hb (h := 987 + k) (by omega), inSupport_cast,
      CurrentMasks2011.lowSupport_def]
    simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico, Finset.mem_singleton]
    omega
  rw [hz, add_zero] at hp
  obtain ⟨x, hx, hxe⟩ := bit01 H (cell_lt' H hb (q := 969 + k) (by omega))
  obtain ⟨y, hy, hye⟩ := bit01 H (cell_lt' H (prevCell_isCell H.N_pos hb) (q := 978 + k) (by omega))
  rw [hxe, hye] at hp ⊢
  have h2 : (((x + y) % 2 : ℕ) : V) = 0 := by rw [natCast_mod]; push_cast; exact hp
  have : (x + y) % 2 = 0 := by exact_mod_cast h2
  congr 1
  omega

/-- **South/North copy (B7)**: `c(b+942+k) = c(θb+960+k)`. -/
theorem north_copy {b : V} (hb : IsCell N b) {k : ℕ} (hk : k < 9) :
    dig 47 C (b + ((942 + k : ℕ) : V)) = dig 47 C (tcell N W b + ((960 + k : ℕ) : V)) := by
  rw [south_copy H hb hk, temporal_eq H.N_pos (hr0 H) hb (h := 960 + k) (by omega) (by omega),
    Nat.sub_zero]

theorem tcell_isCell {b : V} (hb : IsCell N b) : IsCell N (tcell N W b) :=
  theta_isCell H.N_pos (hr0 H) hb

/-! ### Occupation -/

private theorem not_empty_succ {b b' : V} (hb : IsCell N b) (hb' : IsCell N b')
    (hprev : prevCell (2011 * N) b' = b) {i : Fin 942} (hi : CellHolds C b i) :
    ¬ CellEmpty C b' := by
  intro he
  have hw := tile_west_lt i
  have hbits := bits_eq (x := 0) (y := 255 - (tile i).west) (by norm_num) (by omega)
    he.2.2.2.1 hi.2.2.2.2.2 (fun k hk => by rw [east_copy H hb' hk, hprev])
  omega

private theorem holds_of_selector {b p : V} (hb : IsCell N b) (hp : p < 942)
    (hd : dig 47 C (b + p) = 1) : ∃ i : Fin 942, CellHolds C b i := by
  rcases decode H hb with ⟨he, -⟩ | h
  · obtain ⟨p₀, rfl⟩ := eq_nat_of_lt_nat (n := 942) (by simpa using hp)
    rw [he p₀ (by exact_mod_cast hp)] at hd
    exact absurd hd _root_.zero_ne_one
  · exact h

/-- **Occupation (B8)**: every cell `2011·j`, `j < N`, has a set selector. -/
theorem occupied : ∀ j : V, j < N → ∃ p < (942:V), dig 47 C (2011 * j + p) = 1 := by
  intro j
  induction j using ISigma1.sigma1_succ_induction
  · definability
  case zero =>
    intro _
    exact ⟨0, by norm_num, by simpa using H.origin⟩
  case succ j ih =>
    intro hj
    have hjN : j < N := lt_of_lt_of_le (lt_add_one j) (le_of_lt hj)
    have hb := cell_of_index hjN
    have hb' := cell_of_index hj
    obtain ⟨p, hp, hd⟩ := ih hjN
    obtain ⟨i, hi⟩ := holds_of_selector H hb hp hd
    have hprev : prevCell (2011 * N) (2011 * (j + 1)) = 2011 * j := by
      apply cyc_unique hb.1
      congr 1
      ring
    rcases decode H hb' with he' | ⟨i', hi'⟩
    · exact absurd he' (not_empty_succ H hb hb' hprev hi)
    · exact ⟨(physicalPosition i' : V), by exact_mod_cast physicalPosition_lt i', hi'.1⟩

theorem holds_of_index {j : V} (hj : j < N) : ∃ i : Fin 942, CellHolds C (2011 * j) i := by
  obtain ⟨p, hp, hd⟩ := occupied H j hj
  exact holds_of_selector H (cell_of_index hj) hp hd

end window

/-! ### The Δ0 tile assignment -/

/-- The inverse physical order, as a numeral table. -/
def posTab : List ℕ := List.ofFn fun p : Fin 942 => (physicalEquiv.symm p).val

/-- The tile at a physical selector position. -/
def invPos (x : V) : V := ArithmeticWangTable.tabValue posTab 0 x

instance invPos_definable : 𝚺₀-Function₁ (invPos : V → V) :=
  (ArithmeticWangTable.tab_defined posTab 0).to_definable

theorem invPos_cast (i : Fin 942) : invPos ((physicalPosition i : ℕ) : V) = ((i : ℕ) : V) := by
  rw [invPos, ArithmeticWangTable.tab_cast, List.getD_eq_getElem?_getD, posTab,
    List.getElem?_ofFn, dif_pos (physicalPosition_lt i)]
  have : physicalEquiv.symm ⟨physicalPosition i, physicalPosition_lt i⟩ = i := by
    apply physicalEquiv.injective
    rw [Equiv.apply_symm_apply]
    rfl
  simp [this]

/-- `selPos C m x = Σ_{p<m} p·c(2011x+p)`. -/
def selPos (C : V) : ℕ → V → V
  | 0, _ => 0
  | m + 1, x => selPos C m x + (m : V) * dig 47 C (2011 * x + (m : V))

instance selPos_definable (C : V) (m : ℕ) : 𝚺₁-Function₁ (selPos C m) := by
  induction m with
  | zero =>
    change 𝚺₁-Function₁ (fun _ : V => (0:V))
    definability
  | succ m ih =>
    change 𝚺₁-Function₁ (fun x : V => selPos C m x + (m : V) * dig 47 C (2011 * x + (m : V)))
    definability

/-- The tile index assigned to the cell `2011·x`. -/
def tileAt (C : V) (x : V) : V := invPos (selPos C 942 x)

instance tileAt_definable (C : V) : 𝚺₁-Function₁ (tileAt C : V → V) := by
  unfold tileAt
  definability

theorem selPos_holds {C x : V} {i : Fin 942} (hi : CellHolds C (2011 * x) i) :
    ∀ m : ℕ, m ≤ 942 → selPos C m x = if physicalPosition i < m then (physicalPosition i : V) else 0 := by
  intro m
  induction m with
  | zero => intro _; simp [selPos]
  | succ m ih =>
    intro hm
    rw [selPos, ih (by omega)]
    by_cases he : m = physicalPosition i
    · subst he
      rw [hi.1, if_neg (_root_.lt_irrefl _), if_pos (Nat.lt_succ_self _)]
      simp
    · rw [hi.2.1 m (by omega) he, mul_zero, add_zero]
      by_cases hl : physicalPosition i < m
      · rw [if_pos hl, if_pos (by omega)]
      · rw [if_neg hl, if_neg (by omega)]

theorem tileAt_holds {C x : V} {i : Fin 942} (hi : CellHolds C (2011 * x) i) :
    tileAt C x = ((i : ℕ) : V) := by
  rw [tileAt, selPos_holds hi 942 le_rfl, if_pos (physicalPosition_lt i), invPos_cast]

/-! ### The marked word -/

section marked
variable {N W C F : V} {κ : V → V} (H : CellInput N W C F κ)
include H

private theorem colours {j : V} (hj : j < N) :
    ∃ i : Fin 942, CellHolds C (2011 * j) i ∧ tileAt C j = ((i : ℕ) : V) ∧
      ArithmeticWangTable.eastC (tileAt C j) = ((tile i).east : V) ∧
      ArithmeticWangTable.westC (tileAt C j) = ((tile i).west : V) ∧
      ArithmeticWangTable.northC (tileAt C j) = ((tile i).north : V) ∧
      ArithmeticWangTable.southC (tileAt C j) = ((tile i).south : V) := by
  obtain ⟨i, hi⟩ := holds_of_index H hj
  have ht := tileAt_holds hi
  have hn : ArithmeticWangTable.tileN i = tile i := by
    rw [ArithmeticWangTable.tileN, dif_pos i.isLt]
  refine ⟨i, hi, ht, ?_, ?_, ?_, ?_⟩ <;>
    simp only [ht, ArithmeticWangTable.eastC_cast, ArithmeticWangTable.westC_cast,
      ArithmeticWangTable.northC_cast, ArithmeticWangTable.southC_cast, hn]

/-- **The marked word (B9–B10)**, the input of the Wang soundness lane. -/
theorem marked_word : ArithmeticWangPlane.MarkedWord (tileAt C) N ((W / 47) / 2011) := by
  have hn : (0:V) < 2011 * N := mul_pos (by norm_num) H.N_pos
  have ht : W / 47 = 2011 * ((W / 47) / 2011) := by
    have := div_add_mod (W / 47) 2011
    rw [aligned H, add_zero] at this
    exact this.symm
  refine ⟨H.N_pos, fun j hj => ?_, ?_, ?_, ?_⟩
  · obtain ⟨i, -, hti, -⟩ := colours H hj
    rw [hti]; exact_mod_cast i.isLt
  · have h0 : CellHolds C (2011 * (0:V)) 0 := by simpa using start_holds H
    rw [tileAt_holds h0]; simp
  · intro j hj j' hj' hjj
    obtain ⟨i, hi, -, he, -⟩ := colours H hj
    obtain ⟨i', hi', -, -, hw', -⟩ := colours H hj'
    rw [he, hw']
    have hprev : prevCell (2011 * N) (2011 * j) = 2011 * j' := by
      apply cyc_unique (cell_of_index hj').1
      rw [mod_eq_self_of_lt (cell_of_index hj).1,
        show 2011 * j' + 2011 = 2011 * (j' + 1) by ring, mul_mod_mul (by norm_num) H.N_pos, hjj]
    obtain ⟨hwe, hee, -, -⟩ := tile_tight i
    obtain ⟨hww, hew, -, -⟩ := tile_tight i'
    have := bits_eq (by omega : 255 - (tile i).east < 2 ^ 8) (by omega : 255 - (tile i').west < 2 ^ 8)
      hi.2.2.2.2.1 hi'.2.2.2.2.2
      (fun k hk => by rw [east_copy H (cell_of_index hj) hk, hprev])
    rw [show (tile i).east = (tile i').west by omega]
  · intro j hj j' hj' hjj
    obtain ⟨i, hi, -, -, -, -, hs⟩ := colours H hj
    obtain ⟨i', hi', -, -, -, hn', -⟩ := colours H hj'
    rw [hs, hn']
    have htc : tcell N W (2011 * j) = 2011 * j' := by
      apply cyc_unique (cell_of_index hj').1
      rw [mod_eq_self_of_lt (cell_of_index hj).1]
      have hsd' : shiftD (2011 * N) (W / 47) ((0:ℕ):V) = (W / 47) % (2011 * N) := by
        simp [shiftD]
      rw [hsd', add_comm, mod_add_mod' hn, ht,
        show 2011 * ((W / 47) / 2011) + 2011 * j' = 2011 * (j' + (W / 47) / 2011) by ring,
        mul_mod_mul (by norm_num) H.N_pos, hjj]
    obtain ⟨-, -, hni, hsi⟩ := tile_tight i
    obtain ⟨-, -, hni', hsi'⟩ := tile_tight i'
    have := bits_eq (by omega : 511 - (tile i).south < 2 ^ 9) (by omega : 511 - (tile i').north < 2 ^ 9)
      hi.2.2.1 hi'.2.2.2.1
      (fun k hk => by rw [north_copy H (cell_of_index hj) hk, htc])
    rw [show (tile i).south = (tile i').north by omega]

end marked

end DiophantineConsistency.ArithmeticOccupation
