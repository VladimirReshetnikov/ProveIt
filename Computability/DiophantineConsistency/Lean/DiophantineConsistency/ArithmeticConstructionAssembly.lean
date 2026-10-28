import DiophantineConsistency.ArithmeticTilingWord
import DiophantineConsistency.ArithmeticPackingCells
import DiophantineConsistency.ArithmeticRankForcing2011
import DiophantineConsistency.ArithmeticController
import DiophantineConsistency.ArithmeticConstructionUnit
import DiophantineConsistency.ArithmeticConstructionVariation
import DiophantineConsistency.ArithmeticOuterSeed
import DiophantineConsistency.ArithmeticPellAuxiliarySeed

/-! **K7d — assembling the fourteen coordinates** (construction spec §9 X and
assembly), in every model of IΣ1, from an internal halting time.

Chain: K2 marked word (`w = p^(T+1)`, `H = p^(T+3)`, `N = w·H`, stride `s = w`);
K3 packing without dummies (rank `R0`) and with the controller's dummies
(`ArithmeticController.controller_tiling`, unit `Γ` from
`ArithmeticConstructionUnit.gamma_unit`, exact variation from
`ArithmeticConstructionVariation`); K4 rank forcing; derived multiplier
`w' = 2^(R−d·N)` and transport; K6 outer seed; Stage X auxiliary seed.

`construction` returns a positive vector `v` with `F ≤ q` satisfying the five
`ArithmeticCarrierSoundness2011.Equations` for the actual ports:
`v = (J, F, α, z, f, i, T', s_Y, w', n, η, ζ, y, γ)`. The Local Normalization
Lemma stays a hypothesis. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.ArithmeticConstructionAssembly
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPow ArithmeticWindowDigits ArithmeticPackingBlocks ArithmeticPacking
  ArithmeticPackingCells ArithmeticWangTable ArithmeticWangPlane ArithmeticRepunit
  ArithmeticBinaryPopulation ArithmeticPellRecurrence
open ArithmeticCantor (first)
open ArithmeticMachineRun215 (run)
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.radix CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort

/-! ## The origin block: `C ≡ 1 (mod 4)` -/

theorem cellN_origin (u : ℕ) (hu : u ≤ 1) : cellN 0 0 u % 4 = 1 := by
  rcases (by omega : u = 0 ∨ u = 1) with rfl | rfl <;> decide +kernel

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem cellV_dummy (m δ μ : V) : cellV m δ μ = cellV m 0 μ + Exp.exp (47 * 977) * δ := by
  unfold cellV; ring

theorem exp_two : Exp.exp (2 : V) = 4 := by
  rw [show (2 : V) = 0 + 1 + 1 by norm_num, exp_succ, exp_succ]; simp; norm_num

theorem C_mod_four {a δ : V → V} [𝚺₁-Function₁ a] [𝚺₁-Function₁ δ] {N s : V}
    (hM : MarkedWord a N s) (hN : 1 < N) (hδ0 : δ 0 = 0)
    (h : PackingInput 94517 (CurrentKernel2011.K : V) (CurrentMasks2011.lowPort : V)
      (CurrentMasks2011.highPort : V) N s (cellWord a δ N s)) :
    (Cw 94517 N (cellWord a δ N s) - 1) % 4 = 0 := by
  have hN0 : (0 : V) < N := lt_trans (by norm_num) hN
  have hd0 := dig_bsum (X_lt h) hN0
  rw [dig_zero_index] at hd0
  have hB : Exp.exp (94517 : V) = 4 * Exp.exp 94515 := by
    rw [show (94517 : V) = 2 + 94515 by norm_num, exp_add, exp_two]
  -- the origin cell is a standard ℕ cell ≡ 1 (mod 4)
  obtain ⟨m', hm', ham'⟩ := tile_index (hM.tile_lt _ (mod_lt (0 + s) hN0))
  have hX0 : cellWord a δ N s 0 = ((cellN 0 0 (1 - m') : ℕ) : V) := by
    rw [cellWord, hM.marker, hδ0, ham', one_sub_cast,
      show (0 : V) = ((0 : ℕ) : V) by simp, cellV_cast]
  have hC4 : Cw 94517 N (cellWord a δ N s) % 4 = 1 := by
    rw [← ArithmeticControllerLift.mod_of_mul_mod _ (by norm_num : (0 : V) < 4)
      (q := Exp.exp 94515), ← hB, Cw, hd0, hX0,
      show (4 : V) = ((4 : ℕ) : V) by simp, ← ArithmeticControllerData.cast_mod,
      cellN_origin _ (by omega)]
    simp
  have hd := div_add_mod (Cw 94517 N (cellWord a δ N s)) 4
  rw [hC4] at hd
  rw [← hd, add_tsub_cancel_right]
  simp

/-! ## The assembly -/

/-- The five equations from their ingredients, with `q`, `X = 2^R` and the rank
substituted. -/
theorem equations_of (β K MC MF : V) (v : Fin 14 → V) (q R : V)
    (hq : β * v 0 + 1 = q) (hX : v 8 * q = Exp.exp R)
    (hR : ((q - 1) * (q - v 1) + v 2) * (q ^ 2 - 1) + (MC + q * MF) * v 0 = R)
    (hW : (K + v 8) * q + q = (K + v 8) * (v 1 + v 2) + v 1 + v 3 * (q - 1) + 1)
    (hτ : let Y := v 7 * q ^ 3; let E := Exp.exp R * Y; let k := v 10 + v 11
      (E * v 9 + k - R) * (E * v 9 + k - R) = 1 + (E * Y) * (E * Y + 1) * k * k)
    (hd : let Y := v 7 * q ^ 3; let E := Exp.exp R * Y; let k := v 10 + v 11
      let c := k * Y + v 10; let a := E + Y; let d := Exp.exp R + a * c + v 13 * (4 * a + 3)
      d * d = 1 + (a + 1) * (a + 3) * c * c)
    (hf : let Y := v 7 * q ^ 3; let E := Exp.exp R * Y; let k := v 10 + v 11
      let c := k * Y + v 10; let a := E + Y
      v 4 * v 4 = 1 + (a + 1) * (a + 3) * (v 5 * c * c) * (v 5 * c * c))
    (hU : let Y := v 7 * q ^ 3; let E := Exp.exp R * Y; let k := v 10 + v 11
      let c := k * Y + v 10; let a := E + Y; let I := (a + 1) * (a + 3) * v 5 * c * c
      let u := (v 4 * v 4 * c * v 6 - (v 4 * v 4 * R + c)) + ((v 4 * v 4 * R + c) - v 4 * v 4 * c * v 6)
      I * I * u * u + v 12 * v 12 = 1 + I * I * v 12 * v 12) :
    ArithmeticCarrierSoundness2011.Equations β K MC MF v := by
  unfold ArithmeticCarrierSoundness2011.Equations
  simp only []
  rw [hq, hX, hR]
  exact ⟨hW, hτ, hd, hf, hU⟩



section main
variable (hL : LocalNormalization) (T : V) (hT : first (ArithmeticMachineRun215.run T) = 0)
include hL hT

theorem construction :
    ∃ v : Fin 14 → V, (∀ j, 0 < v j) ∧ v 1 ≤ (CurrentMasks2011.beta : V) * v 0 + 1 ∧
      ArithmeticCarrierSoundness2011.Equations (CurrentMasks2011.beta : V)
        (CurrentKernel2011.K : V) (CurrentMasks2011.lowPort : V)
        ((CurrentMasks2011.highPort + CurrentMasks2011.beta : ℕ) : V) v := by
  -- K2: the marked word at the tiling dimensions
  obtain ⟨hw5, hH2, hH4, hwH⟩ := ArithmeticTilingWord.dimensions T
  have hM := ArithmeticTilingWord.marked_word hT hw5 hH2 hH4
  set s := power (120199 : V) (T + 1) with hsdef
  set N := s * power (120199 : V) (T + 3) with hNdef
  set a := ArithmeticTilingBand.word T s (power (120199 : V) (T + 3)) with hadef
  have hs0 : (0 : V) < s := power_pos _ _ (by norm_num)
  have hH1 : (1 : V) < power 120199 (T + 3) := lt_of_lt_of_le (by norm_num) hH4
  have hsN : s < N := lt_mul_of_one_lt_right hs0 hH1
  have hN1 : (1 : V) < N := lt_of_le_of_lt (pos_iff_one_le.mp hs0) hsN
  have hN0 : (0 : V) < N := lt_trans (by norm_num) hN1
  -- K3 without dummies
  haveI : 𝚺₁-Function₁ (fun _ : V => (0 : V)) := by definability
  have h0 := packing_of_marked hL hM (δ := fun _ => (0 : V)) (fun _ => by simp) hN1 hsN
  -- notation for the radix and the rank formula
  set q := Exp.exp ((94517 : V) * N) with hqdef
  set J := rep (94517 : V) N with hJdef
  set MF : V := ((CurrentMasks2011.highPort + CurrentMasks2011.beta : ℕ) : V) with hMF
  set cJ := ((CurrentMasks2011.lowPort : V) + q * MF) * J with hcJ
  set X0 := cellWord a (fun _ => (0 : V)) N s with hX0def
  set R0 := ((q - 1) * (q - Fw 94517 (CurrentKernel2011.K : V) N s X0) +
    alpha 94517 (CurrentKernel2011.K : V) N s X0) * (q ^ 2 - 1) + cJ with hR0
  -- K5: the unit and the controller
  have hNp : N = power (120199 : V) (2 * T + 3 + 1) := by
    rw [hwH]; congr 1; ring
  obtain ⟨Γi, hΓ⟩ := ArithmeticConstructionUnit.gamma_unit (V := V) (2 * T + 3) (T + 1)
  rw [← hNp, ← hsdef] at hΓ
  obtain ⟨δ, hδd, hδb, hδs, hctl⟩ := ArithmeticController.controller_tiling T R0
    (ArithmeticConstructionUnit.Gamma N s) Γi hΓ
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
  obtain ⟨hC, hF⟩ := ArithmeticConstructionVariation.variation (d := 94517)
    (ρ := Exp.exp (47 * 977)) (by norm_num) h0 h1 (exp_monotone.mpr (by norm_num)) hX hδb
    (fun j hj => ⟨(hδs j hj).2.1, (hδs j hj).2.2⟩)
  have hrs := ArithmeticConstructionVariation.rank_shift (q := q) (c := cJ)
    (one_le_exp _) (packing_alpha h0).2 (packing_alpha h1).2 hC hF
  set C1 := Cw 94517 N X1 with hC1def
  set F1 := Fw 94517 (CurrentKernel2011.K : V) N s X1 with hF1def
  set α1 := alpha 94517 (CurrentKernel2011.K : V) N s X1 with hα1def
  set R := ((q - 1) * (q - F1) + α1) * (q ^ 2 - 1) + cJ with hRdef
  have hvar : R + ArithmeticConstructionUnit.Gamma N s * bsum 94517 δ N = R0 := by
    rw [hR0, ← hrs]
    unfold ArithmeticConstructionUnit.Gamma
    rw [hqdef]
    ring
  -- K4: rank forcing
  have hwd : (CurrentMasks2011.width : V) = 94517 := (ArithmeticCarrierRadix2011.current_width).1
  let vr : Fin 14 → V := ![J, F1, α1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
  obtain ⟨hqv, -, hpop, hR4, hbig⟩ := ArithmeticRankForcing2011.current_rank_forcing vr N C1 hN0
    (by rw [hwd]; rfl) (C_pos h1) (packing_alpha h1).1
    (by rw [hwd]; exact (packing_alpha h1).2)
    (C_mod_four hM hN1 hδ0 h1) (packing_low_mask h1) (packing_high_mask h1)
  rw [hwd] at hqv hpop hbig
  have hqE : (CurrentMasks2011.beta : V) * J + 1 = q := hqv
  have hrank : ArithmeticCarrierRadix2011.rank vr = R := by
    unfold ArithmeticCarrierRadix2011.rank
    rw [hqv]
    rfl
  rw [hrank] at hpop hR4 hbig
  -- the derived multiplier
  obtain ⟨-, -, -, hprod, hwmod⟩ := hctl R hvar hbig
  set w' := Exp.exp (R - 94517 * N) with hw'def
  have htr := packing_transport h1 w' hwmod
  set z := zq 94517 (CurrentKernel2011.K : V) N w' X1 with hzdef
  -- K6: the outer seed
  have hu : (0 : V) < 94517 * N := mul_pos (by norm_num) hN0
  have hodd : ∃ r, R = 2 * r + 1 := by
    refine ⟨2 * (R / 4) + 1, ?_⟩
    have hd := div_add_mod R 4
    rw [hR4] at hd
    calc R = 4 * (R / 4) + 3 := hd.symm
      _ = 2 * (2 * (R / 4) + 1) + 1 := by ring
  obtain ⟨sY, n, η, ζ, γ, hsY, hn, hη, hζ, hγ, hseed⟩ :=
    ArithmeticOuterSeed.outer_seed (94517 * N) R hu hodd hpop
  obtain ⟨hτ, hdn, hc, -, -⟩ := hseed
  -- Stage X: the auxiliary seed
  obtain ⟨f, i, T', u', y, hf, hi, hT', -, hy, -, -, hfn, -, -, -, -, -, -, habs, hlast⟩ :=
    ArithmeticPellAuxiliarySeed.auxiliary_seed
      (Exp.exp R * (sY * q ^ 3) + sY * q ^ 3) R hR4
  have hsum1 : C1 + F1 + α1 = q := (packing_alpha h1).2
  have hFq : F1 ≤ q := by
    rw [← hsum1]
    exact le_trans (le_add_of_nonneg_left (Arithmetic.zero_le C1))
      (le_add_of_nonneg_right (Arithmetic.zero_le α1))
  have hJ0 : 0 < J := by
    have hrep : (Exp.exp 94517 - 1) * J + 1 = q := packing_repunit h1
    rcases (Arithmetic.zero_le J).lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h, mul_zero, zero_add] at hrep
      have := ArithmeticControllerData.one_lt_exp hu
      rw [← hqdef, ← hrep] at this
      exact _root_.lt_irrefl _ this
  have hz0 : 0 < z := by
    rw [hzdef, zq]
    exact lt_of_lt_of_le _root_.zero_lt_one (le_add_of_nonneg_left (Arithmetic.zero_le _))
  -- the transport equation
  have hW : ((CurrentKernel2011.K : V) + w') * q + q =
      ((CurrentKernel2011.K : V) + w') * (F1 + α1) + F1 + z * (q - 1) + 1 := by
    have e1 : ((CurrentKernel2011.K : V) + w') * C1 + q = z * (q - 1) + 1 + F1 := by
      rw [← htr, add_assoc, tsub_add_cancel_of_le hFq]
    calc ((CurrentKernel2011.K : V) + w') * q + q =
          ((CurrentKernel2011.K : V) + w') * (C1 + F1 + α1) + q := by rw [hsum1]
      _ = ((CurrentKernel2011.K : V) + w') * (F1 + α1) +
          (((CurrentKernel2011.K : V) + w') * C1 + q) := by ring
      _ = _ := by rw [e1]; ring
  -- the auxiliary facts in terms of the seed coordinate c
  rw [← hc] at hfn habs hlast
  rw [habs] at hlast
  refine ⟨![J, F1, α1, z, f, i, T', sY, w', n, η, ζ, y, γ], ?_, ?_, ?_⟩
  · intro j
    fin_cases j
    exacts [hJ0, F_pos h1, (packing_alpha h1).1, hz0, hf, hi, hT', hsY, exp_pos _, hn, hη, hζ,
      hy, hγ]
  · show F1 ≤ (CurrentMasks2011.beta : V) * J + 1
    rw [hqE]; exact hFq
  · exact equations_of _ _ _ _ _ q R hqE hprod rfl hW hτ hdn hfn hlast

end main

end DiophantineConsistency.ArithmeticConstructionAssembly
