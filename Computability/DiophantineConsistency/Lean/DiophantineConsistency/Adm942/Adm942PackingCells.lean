import DiophantineConsistency.ArithmeticPackingCells
import DiophantineConsistency.Adm942.Adm942Kernel

/-! # The admissible942 cell word of a marked tiling

The admissible942 counterpart of `ArithmeticPackingCells`
(`research/admissible942-independent/PROOF.md` §9), in every model of IΣ1.

The cell of tile index `m` with dummy bit `δ` and marker bit `μ` is (radix
`ρ = 2^47`)

`Cell(m,δ,μ) = ρ^m + Σ_{i<9} bit_i(511-S) ρ^{942+i} + Σ_{i<9} bit_i(511-N) ρ^{960+i}
             + Σ_{i<8} bit_i(255-E) ρ^{969+i} + Σ_{i<8} bit_i(255-W) ρ^{978+i}
             + δ ρ^977 + μ ρ^1005`:

the 2011 cell with the selector at its index `m` (2011: the sorted physical
position) and the marker at `1005` (2011: `1004`). It is written once in ℕ
(`cellN`) and once internally (`cellV`), with `cellV m δ μ = cellN m δ μ` on
numerals (`cellV_cast`). The cell word is the 2011 one,
`cellWord a δ N s j = cellV (a j) (δ j) (1 - a ((j+s) mod N))` (marker
`μ_j = [a(j+s) = 0]`, i.e. PROOF (2)). The constant-free pieces (`spreadN`,
`spreadV`, the casts, `noCarry_cast`, `cyc_add_mod`, `tileN_bounded`) are
reused from `ArithmeticPackingCells`.

**The finite obligation.** `LocalNormalization` is the 2011 structure with the
same field names, restated for the admissible942 cell, kernel
`Adm942Kernel.K`, masks `Adm942MaskData.lowPort`/`highPort` and
`BN = 2^189269`. It is a closed fact about standard natural numbers below
`BN²`. This module does **not** prove it; it is an explicit hypothesis.

**Main export.** `packing_of_marked`: under `LocalNormalization`, every marked
word yields `ArithmeticPacking.PackingInput 189269 K lowPort highPort N s
(cellWord a δ N s)`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
noncomputable section
namespace Adm942PackingCells
open DiophantineConsistency
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open WangTiles942 ArithmeticWangTable ArithmeticWangPlane ArithmeticWindowDigits
  ArithmeticCyclicWord ArithmeticBinaryCarry ArithmeticPacking
open ArithmeticPackingCells (spreadN spreadV spreadV_cast exp_cast sub_cast one_sub_cast
  noCarry_cast cyc_add_mod tileN_bounded castExp castMod castDiv)
attribute [local irreducible] Adm942Kernel.K Adm942MaskData.radix Adm942MaskData.beta
  Adm942MaskData.lowPort Adm942MaskData.highPort

/-! ## The cell in ℕ and the local normalization obligation -/

/-- The ℕ cell of tile index `m` with dummy `δ` and marker `μ`. -/
def cellN (m δ μ : ℕ) : ℕ :=
  2 ^ (47 * m) + spreadN 942 9 (511 - (tileN m).south) +
    spreadN 960 9 (511 - (tileN m).north) + spreadN 969 8 (255 - (tileN m).east) +
    spreadN 978 8 (255 - (tileN m).west) + δ * 2 ^ (47 * 977) + μ * 2 ^ (47 * 1005)

/-- `B = ρ^4027 = 2^189269`. -/
def BN : ℕ := 2 ^ 189269

/-- The normalized block of a triple: `Lo(x_cur) + Hi(x_prev) + Cell(x_tmp)`. -/
def lnlD (mc dc uc mp dp up mt dt ut : ℕ) : ℕ :=
  Adm942Kernel.K * cellN mc dc uc % BN + Adm942Kernel.K * cellN mp dp up / BN +
    cellN mt dt ut

/-- **The Local Normalization Lemma** for admissible942, restated over single
admissible triples (the marker of `x_tmp` is `1 - mc`, i.e. `[a_cur = 0]`),
plus the per-cell mask facts. The fields are the 2011 ones. -/
structure LocalNormalization : Prop where
  block : ∀ mc mp mt dc uc dp up dt : ℕ, mc < 942 → mp < 942 → mt < 942 →
    dc ≤ 1 → uc ≤ 1 → dp ≤ 1 → up ≤ 1 → dt ≤ 1 →
    (tileN mc).east = (tileN mp).west → (tileN mc).south = (tileN mt).north →
    cellN mc dc uc + lnlD mc dc uc mp dp up mt dt (1 - mc) < BN ∧
    0 < lnlD mc dc uc mp dp up mt dt (1 - mc) ∧
    lnlD mc dc uc mp dp up mt dt (1 - mc) &&& Adm942MaskData.highPort = 0 ∧
    (mc = 0 → lnlD mc dc uc mp dp up mt dt (1 - mc) &&& (Adm942MaskData.highPort - 1) = 0)
  product : ∀ m d u : ℕ, m < 942 → d ≤ 1 → u ≤ 1 →
    Adm942Kernel.K * cellN m d u < BN * BN
  low : ∀ m d u : ℕ, m < 942 → d ≤ 1 → u ≤ 1 → cellN m d u &&& Adm942MaskData.lowPort = 0
  low_origin : ∀ d u : ℕ, d ≤ 1 → u ≤ 1 →
    (cellN 0 d u - 1) &&& (Adm942MaskData.lowPort + 1) = 0
  /-- Mask sizes. -/
  lowPort_bound : Adm942MaskData.lowPort + 1 < BN
  highPort_bound : 1 ≤ Adm942MaskData.highPort ∧ Adm942MaskData.highPort < BN

theorem cellN_pos (m d u : ℕ) : 1 ≤ cellN m d u := by
  unfold cellN
  have := Nat.one_le_two_pow (n := 47 * m)
  omega

/-! ## The internal cell -/

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The internal cell of tile index `m` with dummy `δ` and marker `μ`. -/
def cellV (m δ μ : V) : V :=
  Exp.exp (47 * m) + spreadV 942 9 (511 - southC m) + spreadV 960 9 (511 - northC m) +
    spreadV 969 8 (255 - eastC m) + spreadV 978 8 (255 - westC m) +
    δ * Exp.exp (47 * 977) + μ * Exp.exp (47 * 1005)

instance cellV_definable : 𝚺₁-Function₃ (cellV : V → V → V → V) := by
  unfold cellV; definability

theorem cellV_cast (m d u : ℕ) : cellV (m : V) (d : V) (u : V) = (cellN m d u : V) := by
  obtain ⟨hs, hn, he, hw⟩ := tileN_bounded m
  unfold cellV cellN
  rw [southC_cast, northC_cast, eastC_cast, westC_cast,
    show (511 : V) = ((511 : ℕ) : V) by simp, show (255 : V) = ((255 : ℕ) : V) by simp,
    sub_cast hs, sub_cast hn, sub_cast he, sub_cast hw,
    spreadV_cast, spreadV_cast, spreadV_cast, spreadV_cast, exp_cast,
    show (977 : V) = ((977 : ℕ) : V) by simp, show (1005 : V) = ((1005 : ℕ) : V) by simp,
    exp_cast, exp_cast]
  push_cast; ring

/-! ## The cell word of a marked word -/

/-- The cell word: `X j = Cell(a j, δ j, [a(j+s) = 0])`. -/
def cellWord (a δ : V → V) (N s j : V) : V := cellV (a j) (δ j) (1 - a ((j + s) % N))

instance cellWord_definable (a δ : V → V) [𝚺₁-Function₁ a] [𝚺₁-Function₁ δ] (N s : V) :
    𝚺₁-Function₁ (cellWord a δ N s) := by
  unfold cellWord; definability

theorem B_cast : Exp.exp (189269 : V) = (BN : V) := by
  have := castExp (V := V) 189269
  rw [Nat.cast_ofNat] at this
  rw [this, BN]

/-- **K3 from a marked word.** Under the Local Normalization Lemma, the cell
word of every marked word with a Boolean dummy map satisfies the packing
input; hence `ArithmeticPacking.packing_*` give the scalars `C, F, α, z, J` and
both masks. -/
theorem packing_of_marked (hL : LocalNormalization) {a δ : V → V} [𝚺₁-Function₁ a]
    [𝚺₁-Function₁ δ] {N s : V} (hM : MarkedWord a N s) (hδ : ∀ j, δ j ≤ 1) (hN : 1 < N)
    (hs : s < N) :
    PackingInput 189269 (Adm942Kernel.K : V) (Adm942MaskData.lowPort : V)
      (Adm942MaskData.highPort : V) N s (cellWord a δ N s) := by
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
      blk 189269 (Adm942Kernel.K : V) N s (cellWord a δ N s) j =
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
    rw [hX, e1, show (Adm942MaskData.lowPort : V) + 1 =
      ((Adm942MaskData.lowPort + 1 : ℕ) : V) by push_cast; rfl]
    exact noCarry_cast (hL.low_origin d u hd hu)
  · intro j hj _
    obtain ⟨m, d, u, hm, hd, hu, -, hX, -⟩ := cell_std j hj
    rw [hX]; exact noCarry_cast (hL.low m d u hm hd hu)
  · obtain ⟨mc, dc, uc, mp, dp, up, mt, dt, hmc, hmp, hmt, hdc, huc, hdp, hup, hdt, hac, he, hs',
      -, hB⟩ := blk_std 0 hN0
    have hm0 : mc = 0 := by exact_mod_cast (hac.symm.trans hM.marker)
    have hb := (hL.block mc mp mt dc uc dp up dt hmc hmp hmt hdc huc hdp hup hdt he hs').2.2.2 hm0
    rw [hB, show (Adm942MaskData.highPort : V) - 1 = ((Adm942MaskData.highPort - 1 : ℕ) : V) by
      simpa only [Nat.cast_one] using sub_cast (V := V) hL.highPort_bound.1]
    exact noCarry_cast hb
  · intro j hj _
    obtain ⟨mc, dc, uc, mp, dp, up, mt, dt, hmc, hmp, hmt, hdc, huc, hdp, hup, hdt, -, he, hs',
      -, hB⟩ := blk_std j hj
    rw [hB]
    exact noCarry_cast (hL.block mc mp mt dc uc dp up dt hmc hmp hmt hdc huc hdp hup hdt he hs').2.2.1

end Adm942PackingCells

#print axioms Adm942PackingCells.cellV_cast
#print axioms Adm942PackingCells.packing_of_marked
