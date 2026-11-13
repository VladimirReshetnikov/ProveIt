import DiophantineConsistency.ArithmeticCellDecoding
import DiophantineConsistency.Adm942.Adm942CellLocal

/-! # Standard clause decoding of one admissible942 cell snapshot

The counterpart of `ArithmeticCellLabels` (soundness spec §5, B1 and B3;
`research/admissible942-independent/PROOF.md` §2 and §6). A clean clause band
(`Adm942CellLocal.clause_equation`) carries the clause sum
`n + 2^10 (Σ_j (1 + packed_j) x_j + W)` plus an incoming carry `k ≤ 57`; its mask
`μ = 2^44 − 2` tests bits `1..43`. Since `n + k ≤ 942 + 57 < 1024`, the tests force
`n + k ≤ 1` and `Q ≡ 0 (mod 2^34)`, so in **every** temporal phase the cell is
empty (no selector, label word zero) or holds exactly one tile whose four label
words are the complements of its colours. Unlike 2011 there is no doubled clause
and no preliminary count: the selector count comes from the decoder itself.

Selectors sit at their index (`sel cw i = cw (8054 + i)`); the generic 2011
helpers (`bw`, `Selected`, `packedTile`, `complementedTile`) are reused. Pure ℕ;
transferred to every model of IΣ1 by `Adm942CellTransfer`. -/

namespace Adm942CellLabels

open DiophantineConsistency DiophantineConsistency.WangTiles942
open ArithmeticCellLabels (bw bw_lt Selected sum_le_one_cases Selected.weighted_sum packedTile
  complementedTile packedTile_lt complementedTile_lt)
open Adm942CellLocal
open scoped BigOperators

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

/-! ### The clean-clause decoder (`PROOF.md` §2) -/

/-- The clause mask `2^44 − 2` tests precisely bits `1` through `43`. -/
theorem mask_iff (x : ℕ) : x &&& (2 ^ 44 - 2) = 0 ↔ x % 2 ^ 44 ≤ 1 := by
  have hd : (x &&& (2 ^ 44 - 2)) / 2 = (x / 2) % 2 ^ 43 := by
    rw [Nat.and_div_two, show (2 ^ 44 - 2) / 2 = 2 ^ 43 - 1 by norm_num,
      Nat.and_two_pow_sub_one_eq_mod]
  have hm : (x &&& (2 ^ 44 - 2)) % 2 = 0 := by
    have h := Nat.and_mod_two_pow (a := x) (b := 2 ^ 44 - 2) (n := 1)
    rw [pow_one] at h
    rw [h, show (2 ^ 44 - 2) % 2 = 0 by norm_num, Nat.and_zero]
  constructor
  · intro h
    rw [h] at hd
    omega
  · intro h
    omega

/-- **The decoder with carry-in**: if `n + k < 1024` and the digit of
`n + 2^10 Q + k` avoids `μ`, then `n + k ≤ 1` and `Q ≡ 0 (mod 2^34)`. -/
theorem clause_decode {n k Q d kout : ℕ} (hnk : n + k < 1024)
    (heq : n + 1024 * Q + k = d + 2 ^ 47 * kout) (hm : d % 2 ^ 44 ≤ 1) :
    n + k ≤ 1 ∧ Q % 2 ^ 34 = 0 := by
  omega

/-! ### Label words and the clause sum -/

/-- The four label words of a cell snapshot (complements of West, North, East, South). -/
def westW (cw : ℕ → ℕ) : ℕ := bw (fun j => cw (8054 + (978 + j))) 8
def northW (cw : ℕ → ℕ) : ℕ := bw (fun j => cw (8054 + (960 + j))) 9
def eastW (cw : ℕ → ℕ) : ℕ := bw (fun j => cw (8054 + (969 + j))) 8
def southW (cw : ℕ → ℕ) : ℕ := bw (fun j => cw (8054 + (942 + j))) 9

def word (cw : ℕ → ℕ) : ℕ :=
  westW cw + 2 ^ 8 * northW cw + 2 ^ 17 * eastW cw + 2 ^ 25 * southW cw

/-- The selector of tile `i`, at its index. -/
def sel (cw : ℕ → ℕ) (i : Fin 942) : ℕ := cw (8054 + i.val)

/-- The selector count of the cell. -/
def count (cw : ℕ → ℕ) : ℕ := ∑ i : Fin 942, sel cw i

def payload (cw : ℕ → ℕ) : ℕ := ∑ i : Fin 942, (1 + packedTile (tile i)) * sel cw i

private theorem block (cw : ℕ → ℕ) (a b n : ℕ) :
    (∑ j : Fin n, 2 ^ (10 + a + (j : ℕ)) * cw (8054 + (b + (j : ℕ)))) =
      1024 * 2 ^ a * bw (fun j => cw (8054 + (b + j))) n := by
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => 2 ^ (10 + a + j) * cw (8054 + (b + j))) n]
  unfold bw
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_add, pow_add]
  ring

/-- The clause sum is `n + 2^10 (payload + word)`. -/
theorem clause_word (cw : ℕ → ℕ) :
    clauseSum cw = count cw + 1024 * (payload cw + word cw) := by
  have hsel : (∑ i : Fin 942, selectorWeight (tile i) * sel cw i) =
      count cw + 1024 * payload cw := by
    unfold payload count
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [selectorWeight, packedTile]
    ring
  have hw := block cw 0 978 8
  have hn := block cw 8 960 9
  have he := block cw 17 969 8
  have hs := block cw 25 942 9
  simp only [Nat.add_zero] at hw
  norm_num only at hn he hs
  unfold clauseSum
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [CurrentKernel2011.weight, Adm942Kernel.position]
  change (∑ i : Fin 942, selectorWeight (tile i) * sel cw i) + _ = _
  rw [hsel, hw, hn, he, hs]
  unfold word westW northW eastW southW
  ring

theorem word_lt {cw : ℕ → ℕ} (hb : ∀ p, p < 12081 → cw p ≤ 1) : word cw < 2 ^ 34 := by
  have hw := bw_lt (fun j => cw (8054 + (978 + j))) 8 (fun j hj => hb _ (by omega))
  have hn := bw_lt (fun j => cw (8054 + (960 + j))) 9 (fun j hj => hb _ (by omega))
  have he := bw_lt (fun j => cw (8054 + (969 + j))) 8 (fun j hj => hb _ (by omega))
  have hs := bw_lt (fun j => cw (8054 + (942 + j))) 9 (fun j hj => hb _ (by omega))
  unfold word westW northW eastW southW
  omega

theorem count_le {cw : ℕ → ℕ} (hb : ∀ p, p < 12081 → cw p ≤ 1) : count cw ≤ 942 := by
  unfold count
  calc (∑ i : Fin 942, sel cw i) ≤ ∑ _i : Fin 942, 1 :=
        Finset.sum_le_sum fun i _ => hb _ (by have := i.isLt; omega)
    _ = 942 := by simp

/-! ### Decoding -/

/-- **Clause decoding (B1, B3)** in every temporal phase: the cell is empty or
holds exactly one tile, whose label word is its complemented colour word. -/
theorem decode {cw tw kw dw : ℕ → ℕ} {kin phase r : ℕ} (H : Local cw tw kw dw kin phase r) :
    ((∀ i, sel cw i = 0) ∧ word cw = 0) ∨
    ∃ i, Selected (sel cw) i ∧ word cw = complementedTile i := by
  obtain ⟨k, d, kout, hk, he, hm⟩ := clause_equation H
  rw [clause_word] at he
  have hcnt := count_le H.bool
  have hm' := (mask_iff d).mp hm
  obtain ⟨hone, hQ⟩ := clause_decode (n := count cw) (k := k) (by omega) he hm'
  have hL := word_lt H.bool
  have hone' : (∑ i, sel cw i) ≤ 1 := by
    have : count cw ≤ 1 := by omega
    exact this
  obtain hempty | ⟨i, hsel⟩ := sum_le_one_cases (sel cw) hone'
  · have hp0 : payload cw = 0 := by
      simp only [payload, hempty, mul_zero, Finset.sum_const_zero]
    rw [hp0] at hQ
    exact Or.inl ⟨hempty, by omega⟩
  · have hp1 : payload cw = 1 + packedTile (tile i) :=
      hsel.weighted_sum (fun j => 1 + packedTile (tile j))
    rw [hp1] at hQ
    have hpk := packedTile_lt i
    refine Or.inr ⟨i, hsel, ?_⟩
    unfold complementedTile
    omega

/-- At most one selector per cell (B1), in every phase. -/
theorem count_le_one {cw tw kw dw : ℕ → ℕ} {kin phase r : ℕ}
    (H : Local cw tw kw dw kin phase r) : count cw ≤ 1 := by
  rcases decode H with ⟨hempty, -⟩ | ⟨i, hsel, -⟩
  · unfold count
    simp only [hempty, Finset.sum_const_zero, zero_le]
  · unfold count
    have := hsel.weighted_sum (fun _ => 1)
    simp only [one_mul] at this
    omega

/-- The four label words of a selected tile are the complements of its colours. -/
theorem labels_of_word {cw : ℕ → ℕ} (hb : ∀ p, p < 12081 → cw p ≤ 1) (i : Fin 942)
    (hword : word cw = complementedTile i) :
    westW cw = 255 - (tile i).west ∧ northW cw = 511 - (tile i).north ∧
    eastW cw = 255 - (tile i).east ∧ southW cw = 511 - (tile i).south := by
  have hw : westW cw < 2 ^ 8 :=
    bw_lt (fun j => cw (8054 + (978 + j))) 8 (fun j hj => hb _ (by omega))
  have hn : northW cw < 2 ^ 9 :=
    bw_lt (fun j => cw (8054 + (960 + j))) 9 (fun j hj => hb _ (by omega))
  have he : eastW cw < 2 ^ 8 :=
    bw_lt (fun j => cw (8054 + (969 + j))) 8 (fun j hj => hb _ (by omega))
  have hs : southW cw < 2 ^ 9 :=
    bw_lt (fun j => cw (8054 + (942 + j))) 9 (fun j hj => hb _ (by omega))
  obtain ⟨hw', he', hn', hs'⟩ := ArithmeticCellPhysical.tile_tight i
  unfold word complementedTile packedTile at hword
  omega

theorem labels_of_zero {cw : ℕ → ℕ} (hword : word cw = 0) :
    westW cw = 0 ∧ northW cw = 0 ∧ eastW cw = 0 ∧ southW cw = 0 := by
  unfold word at hword
  omega

/-! ### The Start cell and the phase -/

/-- A cell whose selector 0 is set holds tile 0. -/
theorem start_cell {cw tw kw dw : ℕ → ℕ} {kin phase r : ℕ} (H : Local cw tw kw dw kin phase r)
    (h0 : cw 8054 = 1) : Selected (sel cw) 0 ∧ word cw = complementedTile 0 := by
  rcases decode H with ⟨he, -⟩ | ⟨i, hs, hw⟩
  · have : cw 8054 = 0 := he 0
    omega
  · have hi : i = 0 := by
      by_contra hne
      have : cw 8054 = 0 := hs.2 0 (Ne.symm hne)
      omega
    subst hi
    exact ⟨hs, hw⟩

/-- **Fractional phase zero (`PROOF.md` §7)**: in a cell whose selector 0 is set,
South bit 1 of the complemented Start colour `510` meets the temporal digit at
the copy test `961`, so every phase `1..46` (even temporal digits) is excluded. -/
theorem phase_zero {cw tw kw dw : ℕ → ℕ} {kin phase r : ℕ} (H : Local cw tw kw dw kin phase r)
    (h0 : cw 8054 = 1) : phase = 0 := by
  obtain ⟨-, hw⟩ := start_cell H h0
  obtain ⟨-, -, -, hs⟩ := labels_of_word H.bool 0 hw
  have hsW : southW cw = 510 := by rw [hs, ArithmeticCellPhysical.start_tile]; rfl
  have hbit := ArithmeticCellDecoding.bits_of_bw (fun j => cw (8054 + (942 + j))) 9
    (fun j hj => H.bool _ (by omega)) 1 (by omega)
  have hb1 : cw (8054 + (942 + 1)) = 1 := by
    have h' : bw (fun j => cw (8054 + (942 + j))) 9 = 510 := hsW
    rw [h'] at hbit
    exact hbit.trans (by norm_num)
  have hp := south_parity H (j := 1) (by omega)
  rw [hb1] at hp
  by_contra hne
  obtain ⟨k, rfl⟩ : ∃ k, phase = k + 1 := ⟨phase - 1, by omega⟩
  rw [show 2 ^ (k + 1) * tw (960 + 1) = 2 * (2 ^ k * tw (960 + 1)) by ring,
    Nat.add_mul_mod_self_left] at hp
  omega

/-- The last tile, whose complemented South colour `74` has bit 0 clear
(`PROOF.md` §7, the `r = 20` obstruction). -/
theorem tile941_south : (tile 941).south = 437 := by decide +kernel

end Adm942CellLabels

#print axioms Adm942CellLabels.decode
#print axioms Adm942CellLabels.count_le_one
#print axioms Adm942CellLabels.phase_zero
#print axioms Adm942CellLabels.tile941_south
