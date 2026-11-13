import DiophantineConsistency.ArithmeticTilingWord
import DiophantineConsistency.ArithmeticConstructionAssembly
import DiophantineConsistency.Bm2963.Bm2963PackingCells
import DiophantineConsistency.Bm2963.Bm2963RankForcing
import DiophantineConsistency.Bm2963.Bm2963Controller
import DiophantineConsistency.Bm2963.Bm2963ConstructionUnit
import DiophantineConsistency.ArithmeticConstructionVariation
import DiophantineConsistency.ArithmeticOuterSeed
import DiophantineConsistency.ArithmeticPellAuxiliarySeed
import DiophantineConsistency.ArithmeticConstructionBoundPell

/-! # Assembling the fourteen block-mask2963 coordinates

The block-mask2963 counterpart of `ArithmeticConstructionAssembly`
(`research/low-padding-independent/PROOF.md` §9–§12), in every model of IΣ1,
from an internal halting time. The argument is the 2011 one, with the
block-mask2963 constants and cell.

Chain: the marked word of `ArithmeticTilingWord.marked_word` at `w = λ^(T+1)`,
`H = λ^(T+3)` (`λ = 1362521`, `dimensions`), `N = w·H`, stride `s = w`; packing
without dummies (rank `R0`) and with the controller's dummies
(`Bm2963Controller.controller_tiling`, unit `Γ` from
`Bm2963ConstructionUnit.gamma_unit`, exact variation from the generic
`ArithmeticConstructionVariation`); rank forcing
(`Bm2963RankForcing.current_rank_forcing`); the derived multiplier
`w' = 2^(R−d·N)` and transport; the generic outer seed and auxiliary seed.

`construction` returns a positive vector `v` with `F ≤ q` satisfying the five
`ArithmeticCarrierSoundness2011.Equations` at the block-mask2963 ports. The
block-mask2963 Local Normalization Lemma
(`Bm2963PackingCells.LocalNormalization`) stays a hypothesis. The constant-free
pieces (`ArithmeticConstructionAssembly.equations_of`, `exp_two`,
`ArithmeticConstructionBound.Wb`, `Rq`, `Wb_mono`, `le_Wb_*`) are reused. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace Bm2963ConstructionAssembly
open DiophantineConsistency
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPow ArithmeticWindowDigits ArithmeticPackingBlocks ArithmeticPacking
  Bm2963PackingCells ArithmeticWangTable ArithmeticWangPlane ArithmeticRepunit
  ArithmeticBinaryPopulation ArithmeticPellRecurrence
open ArithmeticConstructionAssembly (exp_two)
open ArithmeticCantor (first)
open ArithmeticMachineRun215 (run)
attribute [local irreducible] Bm2963Kernel.K Bm2963MaskData.radix Bm2963MaskData.beta
  Bm2963MaskData.lowPort Bm2963MaskData.highPort

/-! ## The origin block: `C ≡ 1 (mod 4)` -/

theorem cellN_origin (u : ℕ) (hu : u ≤ 1) : cellN 0 0 u % 4 = 1 := by
  rcases (by omega : u = 0 ∨ u = 1) with rfl | rfl <;> decide +kernel

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem cellV_dummy (m δ μ : V) : cellV m δ μ = cellV m 0 μ + Exp.exp (47 * 977) * δ := by
  unfold cellV; ring

theorem C_mod_four {a δ : V → V} [𝚺₁-Function₁ a] [𝚺₁-Function₁ δ] {N s : V}
    (hM : MarkedWord a N s) (hN : 1 < N) (hδ0 : δ 0 = 0)
    (h : PackingInput 139261 (Bm2963Kernel.K : V) (Bm2963MaskData.lowPort : V)
      (Bm2963MaskData.highPort : V) N s (cellWord a δ N s)) :
    (Cw 139261 N (cellWord a δ N s) - 1) % 4 = 0 := by
  have hN0 : (0 : V) < N := lt_trans (by norm_num) hN
  have hd0 := dig_bsum (X_lt h) hN0
  rw [dig_zero_index] at hd0
  have hB : Exp.exp (139261 : V) = 4 * Exp.exp 139259 := by
    rw [show (139261 : V) = 2 + 139259 by norm_num, exp_add, exp_two]
  -- the origin cell is a standard ℕ cell ≡ 1 (mod 4)
  obtain ⟨m', hm', ham'⟩ := tile_index (hM.tile_lt _ (mod_lt (0 + s) hN0))
  have hX0 : cellWord a δ N s 0 = ((cellN 0 0 (1 - m') : ℕ) : V) := by
    rw [cellWord, hM.marker, hδ0, ham', ArithmeticPackingCells.one_sub_cast,
      show (0 : V) = ((0 : ℕ) : V) by simp, cellV_cast]
  have hC4 : Cw 139261 N (cellWord a δ N s) % 4 = 1 := by
    rw [← ArithmeticControllerLift.mod_of_mul_mod _ (by norm_num : (0 : V) < 4)
      (q := Exp.exp 139259), ← hB, Cw, hd0, hX0,
      show (4 : V) = ((4 : ℕ) : V) by simp, ← ArithmeticControllerData.cast_mod,
      cellN_origin _ (by omega)]
    simp
  have hd := div_add_mod (Cw 139261 N (cellWord a δ N s)) 4
  rw [hC4] at hd
  rw [← hd, add_tsub_cancel_right]
  simp

/-! ## Dimensions -/

/-- **Dimensions** at `λ = 1362521`: `w = λ^(T+1)`, `H = λ^(T+3)` (the 2011
`ArithmeticTilingWord.dimensions` with `p = λ`). -/
theorem dimensions (T : V) :
    2 * T + 5 ≤ power 1362521 (T + 1) ∧ T + 2 ≤ power 1362521 (T + 3) ∧
      4 ≤ power 1362521 (T + 3) ∧
      power 1362521 (T + 1) * power 1362521 (T + 3) = power 1362521 (2 * T + 4) := by
  have hp : (2 : V) ≤ 1362521 := by norm_num
  have h3 := ArithmeticTilingWord.succ_le_power hp (T + 3)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [power_succ]
    calc 2 * T + 5 ≤ 1362521 * (T + 1) := by
          rw [mul_add, mul_one]
          exact add_le_add (mul_le_mul_right' (by norm_num) T) (by norm_num)
      _ ≤ 1362521 * power 1362521 T := by
          exact mul_le_mul_left' (ArithmeticTilingWord.succ_le_power hp T) _
  · exact le_trans (by
      rw [show T + 3 + 1 = (T + 2) + 2 by ring]; exact le_add_of_nonneg_right (by positivity)) h3
  · exact le_trans (by
      rw [show T + 3 + 1 = T + 4 by ring]; exact le_add_of_nonneg_left (Arithmetic.zero_le T)) h3
  · rw [← power_add]; congr 1; ring

end Bm2963ConstructionAssembly

namespace Bm2963ConstructionBound
open DiophantineConsistency
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPow ArithmeticWindowDigits ArithmeticPackingBlocks ArithmeticPacking
  Bm2963PackingCells ArithmeticWangTable ArithmeticWangPlane ArithmeticRepunit
  ArithmeticBinaryPopulation ArithmeticPellRecurrence Bm2963ConstructionAssembly
  ArithmeticConstructionBoundPell
open ArithmeticConstructionAssembly (equations_of)
open ArithmeticConstructionBound (Rq Wb Wb_mono le_Wb_1 le_Wb_2 le_Wb_3 le_Wb_4 le_Wb_5 le_Wb_6
  le_Wb_7 le_Wb_8 le_Wb_9 le_Wb_10)
open ArithmeticCantor (first)
open ArithmeticMachineRun215 (run)
attribute [local irreducible] Bm2963Kernel.K Bm2963MaskData.radix Bm2963MaskData.beta
  Bm2963MaskData.lowPort Bm2963MaskData.highPort

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## The explicit bound -/

/-- The tiling size `N = w*H = 1362521^(2T+4)`. -/
def Nb (T : V) : V := power 1362521 (2 * T + 4)
/-- The radix `q = 2^(139261*N)`. -/
def Q (T : V) : V := Exp.exp (139261 * Nb T)

/-- **The witness bound**: an explicit term in `T` built from `+`, `*`, `Exp.exp`
and `power` only (the 2011 `Wb`, `Rq` at the block-mask2963 radix). -/
def zeroBound (T : V) : V := Wb (Q T) (Rq (Q T))

/-- The bounded construction records the common outer seed, rank/radix
facts, and the exact orientation of the chosen auxiliary seed. -/
theorem construction_below_seed_phase_hL (hL : LocalNormalization) (T : V) (hT : first (ArithmeticMachineRun215.run T) = 0) :
    ∃ v : Fin 14 → V, (∀ j, 0 < v j) ∧ v 1 ≤ (Bm2963MaskData.beta : V) * v 0 + 1 ∧
      ArithmeticCarrierSoundness2011.Equations (Bm2963MaskData.beta : V)
        (Bm2963Kernel.K : V) (Bm2963MaskData.lowPort : V)
        ((Bm2963MaskData.highPort + Bm2963MaskData.beta : ℕ) : V) v ∧
      (∀ j, v j ≤ zeroBound T) ∧
      Bm2963CarrierRadix.rank v % 4 = 3 ∧
      (∃ b, v 12 = ycoord (Bm2963CarrierRadix.rank v) b) ∧
      ∃ u, Bm2963CarrierRadix.q v = Exp.exp u ∧
        Exp.exp (Bm2963CarrierRadix.rank v) = Bm2963CarrierRadix.q v * v 8 ∧
        2*u ≤ Bm2963CarrierRadix.rank v ∧
        ArithmeticOuterSeed.SeedRelations u (Bm2963CarrierRadix.rank v)
          (v 7) (v 9) (v 10) (v 11) (v 13) ∧
        let q := Bm2963CarrierRadix.q v
        let Y := v 7*q^3
        let c := (v 10+v 11)*Y+v 10
        let R := Bm2963CarrierRadix.rank v
        let a := v 4*v 4*c*v 6
        let b := v 4*v 4*R+c
        a=(a-b)+(b-a)+c+v 4*v 4*R := by
  -- K2: the marked word at the tiling dimensions
  obtain ⟨hw5, hH2, hH4, hwH⟩ := dimensions T
  have hM := ArithmeticTilingWord.marked_word hT hw5 hH2 hH4
  set s := power (1362521 : V) (T + 1) with hsdef
  set N := s * power (1362521 : V) (T + 3) with hNdef
  set a := ArithmeticTilingBand.word T s (power (1362521 : V) (T + 3)) with hadef
  have hs0 : (0 : V) < s := power_pos _ _ (by norm_num)
  have hH1 : (1 : V) < power 1362521 (T + 3) := lt_of_lt_of_le (by norm_num) hH4
  have hsN : s < N := lt_mul_of_one_lt_right hs0 hH1
  have hN1 : (1 : V) < N := lt_of_le_of_lt (pos_iff_one_le.mp hs0) hsN
  have hN0 : (0 : V) < N := lt_trans (by norm_num) hN1
  -- K3 without dummies
  haveI : 𝚺₁-Function₁ (fun _ : V => (0 : V)) := by definability
  have h0 := packing_of_marked hL hM (δ := fun _ => (0 : V)) (fun _ => by simp) hN1 hsN
  -- notation for the radix and the rank formula
  set q := Exp.exp ((139261 : V) * N) with hqdef
  set J := rep (139261 : V) N with hJdef
  set MF : V := ((Bm2963MaskData.highPort + Bm2963MaskData.beta : ℕ) : V) with hMF
  set cJ := ((Bm2963MaskData.lowPort : V) + q * MF) * J with hcJ
  set X0 := cellWord a (fun _ => (0 : V)) N s with hX0def
  set R0 := ((q - 1) * (q - Fw 139261 (Bm2963Kernel.K : V) N s X0) +
    alpha 139261 (Bm2963Kernel.K : V) N s X0) * (q ^ 2 - 1) + cJ with hR0
  -- K5: the unit and the controller
  have hNp : N = power (1362521 : V) (2 * T + 3 + 1) := by
    rw [hwH]; congr 1; ring
  obtain ⟨Γi, hΓ⟩ := Bm2963ConstructionUnit.gamma_unit (V := V) (2 * T + 3) (T + 1)
  rw [← hNp, ← hsdef] at hΓ
  obtain ⟨δ, hδd, hδb, hδs, hctl⟩ := Bm2963Controller.controller_tiling T R0
    (Bm2963ConstructionUnit.Gamma N s) Γi hΓ
  haveI := hδd
  have hδ0 : δ 0 = 0 := by
    by_contra hc; exact absurd (hδs 0 hc).1 (_root_.lt_irrefl 0)
  -- K3 with dummies, and the exact variation
  have h1 := packing_of_marked hL hM (δ := δ) hδb hN1 hsN
  set X1 := cellWord a δ N s with hX1def
  have hX : ∀ j < N, X1 j = X0 j + Exp.exp (47 * 977) * δ j := by
    intro j _
    simp only [hX1def, hX0def, cellWord]
    exact cellV_dummy _ _ _
  obtain ⟨hC, hF⟩ := ArithmeticConstructionVariation.variation (d := 139261)
    (ρ := Exp.exp (47 * 977)) (by norm_num) h0 h1 (exp_monotone.mpr (by norm_num)) hX hδb
    (fun j hj => ⟨(hδs j hj).2.1, (hδs j hj).2.2⟩)
  have hrs := ArithmeticConstructionVariation.rank_shift (q := q) (c := cJ)
    (one_le_exp _) (packing_alpha h0).2 (packing_alpha h1).2 hC hF
  set C1 := Cw 139261 N X1 with hC1def
  set F1 := Fw 139261 (Bm2963Kernel.K : V) N s X1 with hF1def
  set α1 := alpha 139261 (Bm2963Kernel.K : V) N s X1 with hα1def
  set R := ((q - 1) * (q - F1) + α1) * (q ^ 2 - 1) + cJ with hRdef
  have hvar : R + Bm2963ConstructionUnit.Gamma N s * bsum 139261 δ N = R0 := by
    rw [hR0, ← hrs]
    unfold Bm2963ConstructionUnit.Gamma
    rw [hqdef]
    ring
  -- K4: rank forcing
  have hwd : (Bm2963MaskData.width : V) = 139261 := (Bm2963CarrierRadix.current_width).1
  let vr : Fin 14 → V := ![J, F1, α1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
  obtain ⟨hqv, -, hpop, hR4, hbig⟩ := Bm2963RankForcing.current_rank_forcing vr N C1 hN0
    (by rw [hwd]; rfl) (C_pos h1) (packing_alpha h1).1
    (by rw [hwd]; exact (packing_alpha h1).2)
    (C_mod_four hM hN1 hδ0 h1) (packing_low_mask h1) (packing_high_mask h1)
  rw [hwd] at hqv hpop hbig
  have hqE : (Bm2963MaskData.beta : V) * J + 1 = q := hqv
  have hrank : Bm2963CarrierRadix.rank vr = R := by
    unfold Bm2963CarrierRadix.rank
    rw [hqv]
    rfl
  rw [hrank] at hpop hR4 hbig
  -- the derived multiplier
  obtain ⟨-, -, -, hprod, hwmod⟩ := hctl R hvar hbig
  set w' := Exp.exp (R - 139261 * N) with hw'def
  have htr := packing_transport h1 w' hwmod
  set z := zq 139261 (Bm2963Kernel.K : V) N w' X1 with hzdef
  -- K6: the outer seed, with the size of its ordinate
  have hu : (0 : V) < 139261 * N := mul_pos (by norm_num) hN0
  have hodd : ∃ r, R = 2 * r + 1 := by
    refine ⟨2 * (R / 4) + 1, ?_⟩
    have hd := div_add_mod R 4
    rw [hR4] at hd
    calc R = 4 * (R / 4) + 3 := hd.symm
      _ = 2 * (2 * (R / 4) + 1) + 1 := by ring
  obtain ⟨sY, n, η, ζ, γ, hsY, hn, hη, hζ, hγ, hseed, hYb⟩ :=
    outer_seed_bound (139261 * N) R hu hodd hpop
  obtain ⟨hnb, hηb, hζb, hγb, hab, hcb⟩ := seed_bounds _ _ _ _ _ _ _ hsY hYb hseed
  have hseed_saved := hseed
  obtain ⟨hτ, hdn, hc, -, -⟩ := hseed
  -- Stage X: the auxiliary seed
  obtain ⟨f, i, T', u', y, hf, hi, hT', -, hy, hfx, hyic, hfn, hyd, hux, -, -, -, hlit, habs,
      hlast⟩ :=
    ArithmeticPellAuxiliarySeed.auxiliary_seed
      (Exp.exp R * (sY * q ^ 3) + sY * q ^ 3) R hR4
  have hRpos : 0 < R := (ArithmeticPellAuxiliarySeed.phase_indices R hR4).1
  obtain ⟨hfb, hib, hyb, hTb⟩ := aux_bounds _ R f i T' u' y hRpos hab hf hi hfx hyic hyd hux hlit
  have hsum1 : C1 + F1 + α1 = q := (packing_alpha h1).2
  have hFq : F1 ≤ q := by
    rw [← hsum1]
    exact le_trans (le_add_of_nonneg_left (Arithmetic.zero_le C1))
      (le_add_of_nonneg_right (Arithmetic.zero_le α1))
  have hJ0 : 0 < J := by
    rcases zero_or_succ N with hN | ⟨k, hN⟩
    · rw [hN] at hN0; exact absurd hN0 (_root_.lt_irrefl 0)
    · rw [hJdef, hN, rep_succ]; simp
  have hz0 : 0 < z := by
    rw [hzdef, zq]
    exact lt_of_lt_of_le _root_.zero_lt_one (le_add_of_nonneg_left (Arithmetic.zero_le _))
  -- the transport equation
  have e1 : ((Bm2963Kernel.K : V) + w') * C1 + q = z * (q - 1) + 1 + F1 := by
    rw [← htr, add_assoc, tsub_add_cancel_of_le hFq]
  have hW : ((Bm2963Kernel.K : V) + w') * q + q =
      ((Bm2963Kernel.K : V) + w') * (F1 + α1) + F1 + z * (q - 1) + 1 := by
    calc ((Bm2963Kernel.K : V) + w') * q + q =
          ((Bm2963Kernel.K : V) + w') * (C1 + F1 + α1) + q := by rw [hsum1]
      _ = ((Bm2963Kernel.K : V) + w') * (F1 + α1) +
          (((Bm2963Kernel.K : V) + w') * C1 + q) := by ring
      _ = _ := by rw [e1]; ring
  /- ### Sizes of the K-stage coordinates and of the rank -/
  have hN2 : (2 : V) ≤ N := by simpa [one_add_one_eq_two] using lt_iff_succ_le.mp hN1
  have hQ : q = Q T := by
    rw [hqdef, hNp, Q, Nb, show (2 : V) * T + 3 + 1 = 2 * T + 4 by ring]
  have hq1 : (1 : V) < q := ArithmeticControllerData.one_lt_exp hu
  have hE : Exp.exp (139261 : V) ≤ q :=
    exp_monotone_le.mpr (le_mul_of_one_le_right (by simp) (le_trans (by simp) hN2))
  have hLq : (Bm2963MaskData.lowPort : V) ≤ q := by
    refine le_trans Bm2963MaskConstants.lowPort_lt_exp.le ?_
    rw [show (47 : V) * 2963 = 139261 by norm_num]; exact hE
  have hMFq : MF ≤ q + q := by
    rw [hMF, Nat.cast_add]
    refine add_le_add ?_ ?_
    · refine le_trans Bm2963MaskConstants.highPort_lt_exp.le ?_
      rw [show (47 : V) * 2963 = 139261 by norm_num]; exact hE
    · rw [Bm2963CarrierRadix.current_beta_exp, hwd]
      exact le_trans tsub_le_self hE
  have hKq : (Bm2963Kernel.K : V) ≤ q := by
    have hprodK := hL.product 0 0 0 (by norm_num) (by norm_num) (by norm_num)
    have hKN : Bm2963Kernel.K < 2 ^ (139261 + 139261) := by
      have hle : Bm2963Kernel.K ≤ Bm2963Kernel.K * cellN 0 0 0 :=
        Nat.le_mul_of_pos_right _ (cellN_pos 0 0 0)
      have h2 : BN * BN = 2 ^ (139261 + 139261) := by unfold BN; exact (pow_add 2 139261 139261).symm
      rw [← h2]
      exact lt_of_le_of_lt hle hprodK
    have hV : (Bm2963Kernel.K : V) < ((2 ^ (139261 + 139261) : ℕ) : V) := Nat.cast_lt.mpr hKN
    rw [← ArithmeticMaskConstants.cast_exp] at hV
    refine le_trans hV.le (exp_monotone_le.mpr ?_)
    rw [Nat.cast_add]
    calc ((139261 : ℕ) : V) + ((139261 : ℕ) : V) = 139261 * 2 := by norm_num
      _ ≤ 139261 * N := mul_le_mul_of_nonneg_left hN2 (by simp)
  have hJq : J ≤ q := by
    have hrep : (Exp.exp 139261 - 1) * J + 1 = q := packing_repunit h1
    have h2 : (1 : V) + 1 ≤ Exp.exp 139261 := le_trans (by norm_num) (lt_exp (139261 : V)).le
    rw [← hrep]
    exact le_trans (le_mul_of_one_le_left (by simp) (le_tsub_of_add_le_left h2))
      (le_add_of_nonneg_right (by simp))
  have hC1q : C1 ≤ q := by
    rw [← hsum1, add_assoc]; exact le_add_of_nonneg_right (by simp)
  have hαq : α1 ≤ q := by
    rw [← hsum1]; exact le_add_of_nonneg_left (by simp)
  have hRle : R ≤ Rq q := by
    rw [hRdef, hcJ, Rq]
    refine add_le_add (mm (add_le_add (mm tsub_le_self tsub_le_self) hαq) ?_) ?_
    · rw [sq]; exact tsub_le_self
    · exact mm (add_le_add hLq (mm le_rfl hMFq)) hJq
  have hw' : w' ≤ Exp.exp R := exp_monotone_le.mpr tsub_le_self
  have hzb : z ≤ (q + Exp.exp R + 1) * q := by
    have hq1' : (1 : V) ≤ q - 1 :=
      le_tsub_of_add_le_left (by simpa [one_add_one_eq_two] using lt_iff_succ_le.mp hq1)
    calc z ≤ z * (q - 1) := le_self_mul hq1'
      _ ≤ z * (q - 1) + 1 + F1 := by
          rw [add_assoc]; exact le_add_of_nonneg_right (by simp)
      _ = ((Bm2963Kernel.K : V) + w') * C1 + q := e1.symm
      _ ≤ (q + Exp.exp R) * q + q := add_le_add (mm (add_le_add hKq hw') hC1q) le_rfl
      _ = (q + Exp.exp R + 1) * q := by ring
  have hsYb : sY ≤ Ys R :=
    le_trans (le_self_mul (one_le_pow₀ (one_le_exp _))) hYb
  have hWfin : Wb q R ≤ zeroBound T := by
    rw [zeroBound, ← hQ]; exact Wb_mono q hRle
  -- the auxiliary facts in terms of the seed coordinate c
  rw [← hc] at hfn habs hlast
  rw [habs] at hlast
  have hqfull : Bm2963CarrierRadix.q
      ![J, F1, α1, z, f, i, T', sY, w', n, η, ζ, y, γ] = q := by
    change (Bm2963MaskData.beta : V) * J + 1 = q
    exact hqE
  have hrank_full : Bm2963CarrierRadix.rank
      ![J, F1, α1, z, f, i, T', sY, w', n, η, ζ, y, γ] = R := by
    unfold Bm2963CarrierRadix.rank
    rw [hqfull]
    rfl
  refine ⟨![J, F1, α1, z, f, i, T', sY, w', n, η, ζ, y, γ], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    fin_cases j
    exacts [hJ0, F_pos h1, (packing_alpha h1).1, hz0, hf, hi, hT', hsY, exp_pos _, hn, hη, hζ,
      hy, hγ]
  · show F1 ≤ (Bm2963MaskData.beta : V) * J + 1
    rw [hqE]; exact hFq
  · exact equations_of _ _ _ _ _ q R hqE hprod rfl hW hτ hdn hfn hlast
  · intro j
    refine le_trans ?_ hWfin
    fin_cases j
    · exact le_Wb_1 hJq
    · exact le_Wb_1 hFq
    · exact le_Wb_1 hαq
    · exact le_Wb_2 hzb
    · exact le_Wb_8 hfb
    · exact le_Wb_8 hib
    · exact le_Wb_10 hTb
    · exact le_Wb_4 hsYb
    · exact le_Wb_3 hw'
    · exact le_Wb_5 hnb
    · exact le_Wb_6 hηb
    · exact le_Wb_6 hζb
    · exact le_Wb_9 hyb
    · exact le_Wb_7 hγb
  · rw [hrank_full]
    exact hR4
  · let a := Exp.exp R * (sY * q ^ 3) + sY * q ^ 3
    let c := ycoord R a
    refine ⟨delta a * i * c * c - 2, ?_⟩
    rw [hrank_full]
    exact hyd
  · refine ⟨139261*N, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hqfull, hqdef]
    · change Exp.exp (Bm2963CarrierRadix.rank
        ![J, F1, α1, z, f, i, T', sY, w', n, η, ζ, y, γ]) =
          Bm2963CarrierRadix.q ![J, F1, α1, z, f, i, T', sY, w', n, η, ζ, y, γ] * w'
      rw [hrank_full, hqfull]
      simpa only [mul_comm] using hprod.symm
    · rw [hrank_full]
      exact le_of_lt hbig
    · change ArithmeticOuterSeed.SeedRelations (139261*N)
        (Bm2963CarrierRadix.rank ![J, F1, α1, z, f, i, T', sY, w', n, η, ζ, y, γ])
        sY n η ζ γ
      rw [hrank_full]
      exact hseed_saved
    · change f*f*((η+ζ)*(sY*(Bm2963CarrierRadix.q
        ![J, F1, α1, z, f, i, T', sY, w', n, η, ζ, y, γ])^3)+η)*T' = _
      rw [hqfull, hrank_full]
      let C := (η+ζ)*(sY*q^3)+η
      change f*f*C*T' = (f*f*C*T'-(f*f*R+C))+(f*f*R+C-f*f*C*T')+C+f*f*R
      have hh := hlit
      rw [←hc, habs] at hh
      change f*f*C*T' = (f*f*C*T'-(f*f*R+C))+(f*f*R+C-f*f*C*T')+C+f*f*R at hh
      exact hh

/-- The previous phase and auxiliary-ordinate interface is preserved. -/
theorem construction_below_phase_hL (hL : LocalNormalization) (T : V) (hT : first (ArithmeticMachineRun215.run T) = 0) :
    ∃ v : Fin 14 → V, (∀ j, 0 < v j) ∧ v 1 ≤ (Bm2963MaskData.beta : V) * v 0 + 1 ∧
      ArithmeticCarrierSoundness2011.Equations (Bm2963MaskData.beta : V)
        (Bm2963Kernel.K : V) (Bm2963MaskData.lowPort : V)
        ((Bm2963MaskData.highPort + Bm2963MaskData.beta : ℕ) : V) v ∧
      (∀ j, v j ≤ zeroBound T) ∧
      Bm2963CarrierRadix.rank v % 4 = 3 ∧
      ∃ b, v 12 = ycoord (Bm2963CarrierRadix.rank v) b := by
  obtain ⟨v, hv, hF, heq, hb, hphase, hy, _⟩ := construction_below_seed_phase_hL hL T hT
  exact ⟨v, hv, hF, heq, hb, hphase, hy⟩

/-- The original bounded construction interface. -/
theorem construction_below_hL (hL : LocalNormalization) (T : V) (hT : first (ArithmeticMachineRun215.run T) = 0) :
    ∃ v : Fin 14 → V, (∀ j, 0 < v j) ∧ v 1 ≤ (Bm2963MaskData.beta : V) * v 0 + 1 ∧
      ArithmeticCarrierSoundness2011.Equations (Bm2963MaskData.beta : V)
        (Bm2963Kernel.K : V) (Bm2963MaskData.lowPort : V)
        ((Bm2963MaskData.highPort + Bm2963MaskData.beta : ℕ) : V) v ∧
      ∀ j, v j ≤ zeroBound T := by
  obtain ⟨v, hv, hF, heq, hb, _, _⟩ := construction_below_phase_hL hL T hT
  exact ⟨v, hv, hF, heq, hb⟩

end Bm2963ConstructionBound

namespace Bm2963ConstructionAssembly
open DiophantineConsistency
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor (first)
open Bm2963PackingCells
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
section main
variable (hL : LocalNormalization) (T : V) (hT : first (ArithmeticMachineRun215.run T) = 0)
include hL hT

theorem construction :
    ∃ v : Fin 14 → V, (∀ j, 0 < v j) ∧ v 1 ≤ (Bm2963MaskData.beta : V) * v 0 + 1 ∧
      ArithmeticCarrierSoundness2011.Equations (Bm2963MaskData.beta : V)
        (Bm2963Kernel.K : V) (Bm2963MaskData.lowPort : V)
        ((Bm2963MaskData.highPort + Bm2963MaskData.beta : ℕ) : V) v := by
  obtain ⟨v, hv, hF, heq, _⟩ :=
    Bm2963ConstructionBound.construction_below_hL hL T hT
  exact ⟨v, hv, hF, heq⟩

end main
end Bm2963ConstructionAssembly

#print axioms Bm2963ConstructionAssembly.C_mod_four
#print axioms Bm2963ConstructionAssembly.dimensions
#print axioms Bm2963ConstructionBound.construction_below_seed_phase_hL
#print axioms Bm2963ConstructionAssembly.construction
