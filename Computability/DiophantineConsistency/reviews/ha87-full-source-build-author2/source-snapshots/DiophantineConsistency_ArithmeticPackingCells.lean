import DiophantineConsistency.ArithmeticStandardCasts
import DiophantineConsistency.ArithmeticPacking
import DiophantineConsistency.CurrentKernelData2011
import DiophantineConsistency.ArithmeticWangPlane

/-! **K3c — the actual cell word of a marked tiling** (construction spec §5
P1–P2), in every model of IΣ1.

The cell of tile index `m` with dummy bit `δ` and marker bit `μ` is the
closed formula (radix `ρ = 2^47`)

`Cell(m,δ,μ) = ρ^{phys m} + Σ_{i<9} bit_i(511-S) ρ^{942+i} + Σ_{i<9} bit_i(511-N) ρ^{960+i}
             + Σ_{i<8} bit_i(255-E) ρ^{969+i} + Σ_{i<8} bit_i(255-W) ρ^{978+i}
             + δ ρ^977 + μ ρ^1004`,

written once in ℕ (`cellN`) and once internally (`cellV`), with
`cellV m δ μ = cellN m δ μ` on numerals (`cellV_cast`). For a Σ1 marked word
`a` on `N` cells with stride `s` and a Σ1 Boolean dummy map `δ`, the cell word
is `cellWord a δ N s j = cellV (a j) (δ j) (1 - a ((j+s) mod N))`
(the marker `μ_j = [a(j+s) = 0]`, simplification S1: Start need not be unique).

**The finite obligation.** `LocalNormalization` is the Local Normalization
Lemma of the spec, restated over single admissible triples
`(x_cur, x_prev, x_tmp)` of standard tiles and bits, as a statement about
standard natural numbers (`&&&` is `Nat.land`). It is a closed Δ0 fact about
standard numbers below `B²`, to be proved in ℕ (by the per-digit arguments of
`CurrentWordCopies2011`, `CurrentWordPadding2011`, `CurrentWordClause2011`,
`CurrentWordOrigin2011`, `CurrentWordTopBounds2011`, restated locally). This
module does **not** prove it; it is an explicit hypothesis.

**Main export.** `packing_of_marked`: under `LocalNormalization`, every marked
word yields `ArithmeticPacking.PackingInput 94517 K lowPort highPort N s
(cellWord a δ N s)`, hence all K3 scalar laws of `ArithmeticPacking`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.ArithmeticPackingCells
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open WangTiles942 ArithmeticWangTable ArithmeticWangPlane ArithmeticWindowDigits
  ArithmeticCyclicWord ArithmeticBinaryCarry ArithmeticPacking

/-! ## The cell in ℕ and the local normalization obligation -/

/-- Physical selector position of a table index (0 outside the table). -/
def physN (m : ℕ) : ℕ := if h : m < 942 then physicalPosition ⟨m, h⟩ else 0

/-- `Σ_{i<n} bit_i(x)·ρ^{b+i}`. -/
def spreadN (b : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, x => spreadN b n x + x / 2 ^ n % 2 * 2 ^ (47 * (b + n))

/-- The ℕ cell of tile index `m` with dummy `δ` and marker `μ`. -/
def cellN (m δ μ : ℕ) : ℕ :=
  2 ^ (47 * physN m) + spreadN 942 9 (511 - (tileN m).south) +
    spreadN 960 9 (511 - (tileN m).north) + spreadN 969 8 (255 - (tileN m).east) +
    spreadN 978 8 (255 - (tileN m).west) + δ * 2 ^ (47 * 977) + μ * 2 ^ (47 * 1004)

/-- `B = ρ^2011 = 2^94517`. -/
def BN : ℕ := 2 ^ 94517

/-- The normalized block of a triple: `Lo(x_cur) + Hi(x_prev) + Cell(x_tmp)`. -/
def lnlD (mc dc uc mp dp up mt dt ut : ℕ) : ℕ :=
  CurrentKernel2011.K * cellN mc dc uc % BN + CurrentKernel2011.K * cellN mp dp up / BN +
    cellN mt dt ut

/-- **The Local Normalization Lemma**, restated over single admissible triples
(the marker of `x_tmp` is `1 - mc`, i.e. `[a_cur = 0]`), plus the per-cell
mask facts. -/
structure LocalNormalization : Prop where
  block : ∀ mc mp mt dc uc dp up dt : ℕ, mc < 942 → mp < 942 → mt < 942 →
    dc ≤ 1 → uc ≤ 1 → dp ≤ 1 → up ≤ 1 → dt ≤ 1 →
    (tileN mc).east = (tileN mp).west → (tileN mc).south = (tileN mt).north →
    cellN mc dc uc + lnlD mc dc uc mp dp up mt dt (1 - mc) < BN ∧
    0 < lnlD mc dc uc mp dp up mt dt (1 - mc) ∧
    lnlD mc dc uc mp dp up mt dt (1 - mc) &&& CurrentMasks2011.highPort = 0 ∧
    (mc = 0 → lnlD mc dc uc mp dp up mt dt (1 - mc) &&& (CurrentMasks2011.highPort - 1) = 0)
  product : ∀ m d u : ℕ, m < 942 → d ≤ 1 → u ≤ 1 →
    CurrentKernel2011.K * cellN m d u < BN * BN
  low : ∀ m d u : ℕ, m < 942 → d ≤ 1 → u ≤ 1 → cellN m d u &&& CurrentMasks2011.lowPort = 0
  low_origin : ∀ d u : ℕ, d ≤ 1 → u ≤ 1 →
    (cellN 0 d u - 1) &&& (CurrentMasks2011.lowPort + 1) = 0
  /-- Mask sizes (`CurrentMasks2011.lowPort_lt`, `highPort_lt`, `highPort_pos`;
  that module is not importable next to Foundation). -/
  lowPort_bound : CurrentMasks2011.lowPort + 1 < BN
  highPort_bound : 1 ≤ CurrentMasks2011.highPort ∧ CurrentMasks2011.highPort < BN

theorem cellN_pos (m d u : ℕ) : 1 ≤ cellN m d u := by
  unfold cellN
  have := Nat.one_le_two_pow (n := 47 * physN m)
  omega

/-- Colour bounds of every table row. -/
theorem rows_bounded : ∀ row ∈ orderedRows,
    row.2.south ≤ 511 ∧ row.2.north ≤ 511 ∧ row.2.east ≤ 255 ∧ row.2.west ≤ 255 := by
  decide +kernel

theorem tileN_bounded (m : ℕ) :
    (tileN m).south ≤ 511 ∧ (tileN m).north ≤ 511 ∧ (tileN m).east ≤ 255 ∧
      (tileN m).west ≤ 255 := by
  by_cases hm : m < 942
  · obtain ⟨row, hr, he⟩ := tileN_mem m hm
    exact he ▸ rows_bounded row hr
  · simp [tileN, dif_neg hm]

/-! ## The internal cell -/

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Local numeral casts -/

theorem castExp (n : ℕ) : Exp.exp (n:V) = ((2^n : ℕ) : V) := by
  exact ArithmeticStandardCasts.cast_exp n

theorem castMod (a b : ℕ) : ((a % b : ℕ) : V) = (a:V) % (b:V) := by
  exact ArithmeticStandardCasts.cast_mod a b

theorem castDiv (a b : ℕ) : ((a / b : ℕ) : V) = (a:V) / (b:V) := by
  exact ArithmeticStandardCasts.cast_div a b

def physList : List ℕ := List.ofFn fun i : Fin 942 => physicalPosition i

/-- Internal physical position lookup. -/
def physV (m : V) : V := tabValue physList 0 m

instance physV_definable : 𝚺₀-Function₁ (physV : V → V) := (tab_defined physList 0).to_definable

theorem physV_cast (m : ℕ) : physV (m : V) = (physN m : V) := by
  rw [physV, tab_cast, physList, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  by_cases hm : m < 942 <;> simp [physN, hm]

/-- Internal `Σ_{i<n} bit_i(x)·ρ^{b+i}`. -/
def spreadV (b : ℕ) : ℕ → V → V
  | 0 => fun _ => 0
  | n + 1 => fun x => spreadV b n x + fbit x (n : V) * Exp.exp (47 * ((b + n : ℕ) : V))

theorem spreadV_definable (b : ℕ) : ∀ n : ℕ, 𝚺₁-Function₁ (spreadV (V := V) b n)
  | 0 => by
      show 𝚺₁-Function₁ (fun _ : V => (0 : V))
      definability
  | n + 1 => by
      haveI := spreadV_definable b n
      show 𝚺₁-Function₁ (fun x : V => spreadV b n x + fbit x (n : V) * Exp.exp (47 * ((b + n : ℕ) : V)))
      definability

instance (b n : ℕ) : 𝚺₁-Function₁ (spreadV (V := V) b n) := spreadV_definable b n

theorem fbit_cast (x i : ℕ) : fbit (x : V) (i : V) = ((x / 2 ^ i % 2 : ℕ) : V) := by
  rw [fbit_eq_div, castExp, ← castDiv, castMod]
  simp

theorem exp_cast (e : ℕ) : Exp.exp (47 * (e : V)) = ((2 ^ (47 * e) : ℕ) : V) := by
  rw [← castExp, Nat.cast_mul, Nat.cast_ofNat]

theorem spreadV_cast (b n x : ℕ) : spreadV b n (x : V) = (spreadN b n x : V) := by
  induction n with
  | zero => simp [spreadV, spreadN]
  | succ n ih =>
    show spreadV b n (x : V) + fbit (x : V) (n : V) * Exp.exp (47 * ((b + n : ℕ) : V)) = _
    rw [ih, fbit_cast, exp_cast, spreadN]
    push_cast; ring

/-- The internal cell of tile index `m` with dummy `δ` and marker `μ`. -/
def cellV (m δ μ : V) : V :=
  Exp.exp (47 * physV m) + spreadV 942 9 (511 - southC m) + spreadV 960 9 (511 - northC m) +
    spreadV 969 8 (255 - eastC m) + spreadV 978 8 (255 - westC m) +
    δ * Exp.exp (47 * 977) + μ * Exp.exp (47 * 1004)

instance cellV_definable : 𝚺₁-Function₃ (cellV : V → V → V → V) := by
  unfold cellV; definability

theorem sub_cast {a b : ℕ} (h : b ≤ a) : (a : V) - (b : V) = ((a - b : ℕ) : V) := by
  have : (a : V) = ((a - b : ℕ) : V) + (b : V) := by
    rw [← Nat.cast_add, Nat.sub_add_cancel h]
  rw [this, add_tsub_cancel_right]

theorem cellV_cast (m d u : ℕ) : cellV (m : V) (d : V) (u : V) = (cellN m d u : V) := by
  obtain ⟨hs, hn, he, hw⟩ := tileN_bounded m
  unfold cellV cellN
  rw [physV_cast, southC_cast, northC_cast, eastC_cast, westC_cast,
    show (511 : V) = ((511 : ℕ) : V) by simp, show (255 : V) = ((255 : ℕ) : V) by simp,
    sub_cast hs, sub_cast hn, sub_cast he, sub_cast hw,
    spreadV_cast, spreadV_cast, spreadV_cast, spreadV_cast, exp_cast,
    show (977 : V) = ((977 : ℕ) : V) by simp, show (1004 : V) = ((1004 : ℕ) : V) by simp,
    exp_cast, exp_cast]
  push_cast; ring

theorem one_sub_cast (m : ℕ) : (1 : V) - (m : V) = ((1 - m : ℕ) : V) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · rw [Nat.sub_eq_zero_of_le hm, Nat.cast_zero]
    exact tsub_eq_zero_of_le (by exact_mod_cast hm)

/-- Disjoint bits of standard numerals give internal `NoCarry`. -/
theorem noCarry_cast {x y : ℕ} (h : x &&& y = 0) : NoCarry (x : V) (y : V) := by
  intro i hi
  have hi' : i < ((x + y + 1 : ℕ) : V) := by push_cast; exact hi
  obtain ⟨k, -, rfl⟩ := standard_of_lt hi'
  rw [fbit_cast, fbit_cast]
  have hk : x / 2 ^ k % 2 + y / 2 ^ k % 2 ≤ 1 := by
    have h1 := Nat.testBit_and x y k
    rw [h, Nat.zero_testBit, Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq] at h1
    rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ k) with hx | hx <;>
      rcases Nat.mod_two_eq_zero_or_one (y / 2 ^ k) with hy | hy <;> simp_all
  exact_mod_cast hk

/-! ## The cell word of a marked word -/

/-- The cell word: `X j = Cell(a j, δ j, [a(j+s) = 0])`. -/
def cellWord (a δ : V → V) (N s j : V) : V := cellV (a j) (δ j) (1 - a ((j + s) % N))

instance cellWord_definable (a δ : V → V) [𝚺₁-Function₁ a] [𝚺₁-Function₁ δ] (N s : V) :
    𝚺₁-Function₁ (cellWord a δ N s) := by
  unfold cellWord; definability

theorem cyc_add_mod {N j e : V} (hj : j < N) (he : e < N) : (cyc N j e + e) % N = j := by
  have hN : 0 < N := lt_of_le_of_lt (Arithmetic.zero_le j) hj
  unfold cyc
  rw [mod_add_mod _ _ hN, mod_eq_self_of_lt he,
    tsub_add_cancel_of_le (le_trans he.le (le_add_of_nonneg_left (Arithmetic.zero_le j))),
    mod_add_remove_right hN, mod_eq_self_of_lt hj]

theorem B_cast : Exp.exp (94517 : V) = (BN : V) := by
  have := castExp (V := V) 94517
  rw [Nat.cast_ofNat] at this
  rw [this, BN]

/-- **K3 from a marked word.** Under the Local Normalization Lemma, the cell
word of every marked word with a Boolean dummy map satisfies the packing
input; hence `ArithmeticPacking.packing_*` give the scalars `C, F, α, z, J` and
both masks. -/
theorem packing_of_marked (hL : LocalNormalization) {a δ : V → V} [𝚺₁-Function₁ a]
    [𝚺₁-Function₁ δ] {N s : V} (hM : MarkedWord a N s) (hδ : ∀ j, δ j ≤ 1) (hN : 1 < N)
    (hs : s < N) :
    PackingInput 94517 (CurrentKernel2011.K : V) (CurrentMasks2011.lowPort : V)
      (CurrentMasks2011.highPort : V) N s (cellWord a δ N s) := by
  have hN0 : 0 < N := lt_trans (by norm_num) hN
  have h1N : 1 < N := hN
  -- standard data of a cell
  have std_tile : ∀ j < N, ∃ m : ℕ, m < 942 ∧ a j = m := fun j hj => tile_index (hM.tile_lt j hj)
  have std_bit : ∀ j, ∃ d : ℕ, d ≤ 1 ∧ δ j = d := fun j => by
    obtain ⟨d, hd, e⟩ := standard_of_lt (n := 2) (i := δ j)
      (lt_of_le_of_lt (hδ j) (by simpa using (Nat.cast_lt (α := V)).mpr (by decide : (1:ℕ) < 2)))
    exact ⟨d, by omega, e⟩
  have cell_std : ∀ j < N, ∃ m d u : ℕ, m < 942 ∧ d ≤ 1 ∧ u ≤ 1 ∧ a j = m ∧
      cellWord a δ N s j = (cellN m d u : V) ∧ ∃ m' : ℕ, a ((j + s) % N) = (m' : V) ∧ u = 1 - m' := by
    intro j hj
    obtain ⟨m, hm, ham⟩ := std_tile j hj
    obtain ⟨d, hd, hdd⟩ := std_bit j
    obtain ⟨m', hm', ham'⟩ := std_tile _ (mod_lt (j + s) hN0)
    refine ⟨m, d, 1 - m', hm, hd, by omega, ham, ?_, ?_⟩
    · rw [cellWord, ham, hdd, ham', one_sub_cast, cellV_cast]
    · exact ⟨m', ham', rfl⟩
  -- the block at cell j
  have blk_std : ∀ j < N, ∃ mc dc uc mp dp up mt dt : ℕ, mc < 942 ∧ mp < 942 ∧ mt < 942 ∧
      dc ≤ 1 ∧ uc ≤ 1 ∧ dp ≤ 1 ∧ up ≤ 1 ∧ dt ≤ 1 ∧ a j = mc ∧
      (tileN mc).east = (tileN mp).west ∧ (tileN mc).south = (tileN mt).north ∧
      cellWord a δ N s j = (cellN mc dc uc : V) ∧
      blk 94517 (CurrentKernel2011.K : V) N s (cellWord a δ N s) j =
        (lnlD mc dc uc mp dp up mt dt (1 - mc) : V) := by
    intro j hj
    have hp := cyc_lt hN0 j 1
    have ht := cyc_lt hN0 j s
    obtain ⟨mc, dc, uc, hmc, hdc, huc, hac, hXc, -⟩ := cell_std j hj
    obtain ⟨mp, dp, up, hmp, hdp, hup, hap, hXp, -⟩ := cell_std _ hp
    obtain ⟨mt, dt, ut, hmt, hdt, hut, hat, hXt, m', hμ, hu⟩ := cell_std _ ht
    rw [cyc_add_mod hj hs, hac] at hμ
    have hm' : m' = mc := by exact_mod_cast hμ.symm
    rw [hm'] at hu
    subst hu
    have heast := hM.east j hj _ hp (cyc_add_mod hj h1N)
    have hsouth := hM.south j hj _ ht (cyc_add_mod hj hs)
    rw [hac, hap, eastC_cast, westC_cast] at heast
    rw [hac, hat, southC_cast, northC_cast] at hsouth
    refine ⟨mc, dc, uc, mp, dp, up, mt, dt, hmc, hmp, hmt, hdc, huc, hdp, hup, hdt, hac,
      by exact_mod_cast heast, by exact_mod_cast hsouth, hXc, ?_⟩
    rw [blk, lo, hi, hXc, hXp, hXt, B_cast, ← Nat.cast_mul, ← Nat.cast_mul, ← castMod,
      ← castDiv, lnlD]
    push_cast; ring
  refine ⟨hN, hs, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- hi_lt
    intro j hj
    obtain ⟨m, d, u, hm, hd, hu, -, hX, -⟩ := cell_std j hj
    rw [hX, B_cast, ← Nat.cast_mul, ← Nat.cast_mul]
    exact_mod_cast hL.product m d u hm hd hu
  · rw [B_cast]; exact_mod_cast hL.lowPort_bound
  · exact_mod_cast hL.highPort_bound.1
  · rw [B_cast]; exact_mod_cast hL.highPort_bound.2
  · intro j hj
    obtain ⟨mc, dc, uc, mp, dp, up, mt, dt, hmc, hmp, hmt, hdc, huc, hdp, hup, hdt, -, he, hs', hX,
      hB⟩ := blk_std j hj
    rw [hX, hB, B_cast]
    exact_mod_cast (hL.block mc mp mt dc uc dp up dt hmc hmp hmt hdc huc hdp hup hdt he hs').1
  · obtain ⟨m, d, u, -, -, -, -, hX, -⟩ := cell_std 0 hN0
    rw [hX]; exact_mod_cast cellN_pos m d u
  · obtain ⟨mc, dc, uc, mp, dp, up, mt, dt, hmc, hmp, hmt, hdc, huc, hdp, hup, hdt, -, he, hs', -,
      hB⟩ := blk_std 0 hN0
    rw [hB]
    exact_mod_cast (hL.block mc mp mt dc uc dp up dt hmc hmp hmt hdc huc hdp hup hdt he hs').2.1
  · obtain ⟨m, d, u, -, hd, hu, ha, hX, -⟩ := cell_std 0 hN0
    have hm0 : m = 0 := by exact_mod_cast (ha.symm.trans hM.marker)
    subst hm0
    have e1 : ((cellN 0 d u : ℕ) : V) - 1 = ((cellN 0 d u - 1 : ℕ) : V) := by
      simpa only [Nat.cast_one] using sub_cast (V := V) (cellN_pos 0 d u)
    rw [hX, e1, show (CurrentMasks2011.lowPort : V) + 1 =
      ((CurrentMasks2011.lowPort + 1 : ℕ) : V) by push_cast; rfl]
    exact noCarry_cast (hL.low_origin d u hd hu)
  · intro j hj _
    obtain ⟨m, d, u, hm, hd, hu, -, hX, -⟩ := cell_std j hj
    rw [hX]; exact noCarry_cast (hL.low m d u hm hd hu)
  · obtain ⟨mc, dc, uc, mp, dp, up, mt, dt, hmc, hmp, hmt, hdc, huc, hdp, hup, hdt, hac, he, hs',
      -, hB⟩ := blk_std 0 hN0
    have hm0 : mc = 0 := by exact_mod_cast (hac.symm.trans hM.marker)
    have hb := (hL.block mc mp mt dc uc dp up dt hmc hmp hmt hdc huc hdp hup hdt he hs').2.2.2 hm0
    rw [hB, show (CurrentMasks2011.highPort : V) - 1 = ((CurrentMasks2011.highPort - 1 : ℕ) : V) by
      simpa only [Nat.cast_one] using sub_cast (V := V) hL.highPort_bound.1]
    exact noCarry_cast hb
  · intro j hj _
    obtain ⟨mc, dc, uc, mp, dp, up, mt, dt, hmc, hmp, hmt, hdc, huc, hdp, hup, hdt, -, he, hs',
      -, hB⟩ := blk_std j hj
    rw [hB]
    exact noCarry_cast (hL.block mc mp mt dc uc dp up dt hmc hmp hmt hdc huc hdp hup hdt he hs').2.2.1

end DiophantineConsistency.ArithmeticPackingCells
