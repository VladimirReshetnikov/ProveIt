import DiophantineConsistency.ArithmeticConstructionAssembly
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.ArithmeticConstructionAssemblyCompat
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPow ArithmeticWindowDigits ArithmeticPackingBlocks ArithmeticPacking
  ArithmeticPackingCells ArithmeticWangTable ArithmeticWangPlane ArithmeticRepunit
  ArithmeticBinaryPopulation ArithmeticPellRecurrence ArithmeticConstructionAssembly
open ArithmeticCantor (first)
open ArithmeticMachineRun215 (run)
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.radix CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem construction_below_seed_phase_hL (hL : LocalNormalization) (T : V) (hT : first (ArithmeticMachineRun215.run T) = 0) :
    ∃ v : Fin 14 → V, (∀ j, 0 < v j) ∧ v 1 ≤ (CurrentMasks2011.beta : V) * v 0 + 1 ∧
      ArithmeticCarrierSoundness2011.Equations (CurrentMasks2011.beta : V)
        (CurrentKernel2011.K : V) (CurrentMasks2011.lowPort : V)
        ((CurrentMasks2011.highPort + CurrentMasks2011.beta : ℕ) : V) v ∧
      ArithmeticCarrierRadix2011.rank v % 4 = 3 ∧
      (∃ b, v 12 = ycoord (ArithmeticCarrierRadix2011.rank v) b) ∧
      ∃ u, ArithmeticCarrierRadix2011.q v = Exp.exp u ∧
        Exp.exp (ArithmeticCarrierRadix2011.rank v) = ArithmeticCarrierRadix2011.q v * v 8 ∧
        2*u ≤ ArithmeticCarrierRadix2011.rank v ∧
        ArithmeticOuterSeed.SeedRelations u (ArithmeticCarrierRadix2011.rank v)
          (v 7) (v 9) (v 10) (v 11) (v 13) ∧
        let q := ArithmeticCarrierRadix2011.q v
        let Y := v 7*q^3
        let c := (v 10+v 11)*Y+v 10
        let R := ArithmeticCarrierRadix2011.rank v
        let a := v 4*v 4*c*v 6
        let b := v 4*v 4*R+c
        a=(a-b)+(b-a)+c+v 4*v 4*R := by
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
  -- K6: the outer seed, with the size of its ordinate
  have hu : (0 : V) < 94517 * N := mul_pos (by norm_num) hN0
  have hodd : ∃ r, R = 2 * r + 1 := by
    refine ⟨2 * (R / 4) + 1, ?_⟩
    have hd := div_add_mod R 4
    rw [hR4] at hd
    calc R = 4 * (R / 4) + 3 := hd.symm
      _ = 2 * (2 * (R / 4) + 1) + 1 := by ring
  obtain ⟨sY, n, η, ζ, γ, hsY, hn, hη, hζ, hγ, hseed⟩ :=
    ArithmeticOuterSeed.outer_seed (94517 * N) R hu hodd hpop
  have hseed_saved := hseed
  obtain ⟨hτ, hdn, hc, -, -⟩ := hseed
  -- Stage X: the auxiliary seed
  obtain ⟨f, i, T', u', y, hf, hi, hT', -, hy, hfx, hyic, hfn, hyd, hux, -, -, -, hlit, habs,
      hlast⟩ :=
    ArithmeticPellAuxiliarySeed.auxiliary_seed
      (Exp.exp R * (sY * q ^ 3) + sY * q ^ 3) R hR4
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
  have e1 : ((CurrentKernel2011.K : V) + w') * C1 + q = z * (q - 1) + 1 + F1 := by
    rw [← htr, add_assoc, tsub_add_cancel_of_le hFq]
  have hW : ((CurrentKernel2011.K : V) + w') * q + q =
      ((CurrentKernel2011.K : V) + w') * (F1 + α1) + F1 + z * (q - 1) + 1 := by
    calc ((CurrentKernel2011.K : V) + w') * q + q =
          ((CurrentKernel2011.K : V) + w') * (C1 + F1 + α1) + q := by rw [hsum1]
      _ = ((CurrentKernel2011.K : V) + w') * (F1 + α1) +
          (((CurrentKernel2011.K : V) + w') * C1 + q) := by ring
      _ = _ := by rw [e1]; ring
  -- the auxiliary facts in terms of the seed coordinate c
  rw [← hc] at hfn habs hlast
  rw [habs] at hlast
  have hqfull : ArithmeticCarrierRadix2011.q
      ![J, F1, α1, z, f, i, T', sY, w', n, η, ζ, y, γ] = q := by
    change (CurrentMasks2011.beta : V) * J + 1 = q
    exact hqE
  have hrank_full : ArithmeticCarrierRadix2011.rank
      ![J, F1, α1, z, f, i, T', sY, w', n, η, ζ, y, γ] = R := by
    unfold ArithmeticCarrierRadix2011.rank
    rw [hqfull]
    rfl
  refine ⟨![J, F1, α1, z, f, i, T', sY, w', n, η, ζ, y, γ], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    fin_cases j
    exacts [hJ0, F_pos h1, (packing_alpha h1).1, hz0, hf, hi, hT', hsY, exp_pos _, hn, hη, hζ,
      hy, hγ]
  · show F1 ≤ (CurrentMasks2011.beta : V) * J + 1
    rw [hqE]; exact hFq
  · exact equations_of _ _ _ _ _ q R hqE hprod rfl hW hτ hdn hfn hlast
  · rw [hrank_full]
    exact hR4
  · let a := Exp.exp R * (sY * q ^ 3) + sY * q ^ 3
    let c := ycoord R a
    refine ⟨delta a * i * c * c - 2, ?_⟩
    rw [hrank_full]
    exact hyd
  · refine ⟨94517*N, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hqfull, hqdef]
    · change Exp.exp (ArithmeticCarrierRadix2011.rank
        ![J, F1, α1, z, f, i, T', sY, w', n, η, ζ, y, γ]) =
          ArithmeticCarrierRadix2011.q ![J, F1, α1, z, f, i, T', sY, w', n, η, ζ, y, γ] * w'
      rw [hrank_full, hqfull]
      simpa only [mul_comm] using hprod.symm
    · rw [hrank_full]
      exact le_of_lt hbig
    · change ArithmeticOuterSeed.SeedRelations (94517*N)
        (ArithmeticCarrierRadix2011.rank ![J, F1, α1, z, f, i, T', sY, w', n, η, ζ, y, γ])
        sY n η ζ γ
      rw [hrank_full]
      exact hseed_saved
    · change f*f*((η+ζ)*(sY*(ArithmeticCarrierRadix2011.q
        ![J, F1, α1, z, f, i, T', sY, w', n, η, ζ, y, γ])^3)+η)*T' = _
      rw [hqfull, hrank_full]
      let C := (η+ζ)*(sY*q^3)+η
      change f*f*C*T' = (f*f*C*T'-(f*f*R+C))+(f*f*R+C-f*f*C*T')+C+f*f*R
      have hh := hlit
      rw [←hc, habs] at hh
      change f*f*C*T' = (f*f*C*T'-(f*f*R+C))+(f*f*R+C-f*f*C*T')+C+f*f*R at hh
      exact hh


#print axioms construction_below_seed_phase_hL
end DiophantineConsistency.ArithmeticConstructionAssemblyCompat
