import DiophantineConsistency.ModelThirteenCoreInvariants
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.ModelThirteenCarrier
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
open AdaptiveEquationSyntax2011 ModelDifferenceRing DiscreteOrderedRingFacts FreshCarrierSpheres
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelArithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence ArithmeticCarrierRadix2011 ArithmeticCurrentSentence2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Assemble fresh positive strong, auxiliary, and carrier witnesses. -/
theorem seed_construction (w : Fin 14 → V) (x : Fin 14 → DiffRing V)
    (hxdef : x = fun j => ι (w j)) (hw : ∀ j, 0 < w j)
    (hFq : w 1 < q w) (hβ0 : (0 : V) < (CurrentMasks2011.beta : V))
    (hR4 : rank w % 4 = 3)
    (hcR : (w 10 + w 11) * Y w + w 10 = ycoord (rank w) (X w * Y w + Y w))
    (hG : 0 < transport ringPorts x)
    (hGb : transport ringPorts x = (ringPorts 0 * x 0) * (x 3 - 1)) :
    ∃ fR iR TR mR : DiffRing V, 0 < fR ∧ 0 < iR ∧ 0 < TR ∧ 0 < mR ∧
      fR ^ 2 - (Carrier65.core ringPorts x).delta *
        (ringPorts 0 * x 0 * iR * (Carrier65.core ringPorts x).c ^ 2) ^ 2 = 1 ∧
      let b := Carrier65.core ringPorts x
      let S := b.delta * (ringPorts 0 * x 0 * iR * b.c ^ 2)
      let U := fR ^ 2 * (b.c * TR - b.rank) - b.c
      let y := 1 + 4 * (ringPorts 0 * x 0 * (mR - U ^ 2 * transport ringPorts x) - transport ringPorts x)
      S ^ 2 * (U ^ 2 - y ^ 2) + y ^ 2 = 1 := by
  have hx : ∀ j, 0 < x j := by
    intro j
    rw [hxdef]
    exact ι_pos (hw j)
  have hb : (0 : DiffRing V) < ringPorts 0 := FreshModel106.beta_pos
  obtain ⟨eq_q, eq_Y, eq_E, eq_a, eq_c, eq_delta, eq_rank⟩ := core_invariants w hFq
  set aV := X w * Y w + Y w with haV
  set cV := (w 10 + w 11) * Y w + w 10 with hcV
  set RV := rank w with hRV
  have hc : cV = ycoord RV aV := hcR
  have hbJ : 0 < (CurrentMasks2011.beta : V) * w 0 := mul_pos hβ0 (hw 0)
  -- fresh strong and auxiliary seeds
  have hcpos : 0 < cV := by
    have := ι_lt_ι.mp (show ι 0 < ι cV by rw [map_zero, ← eq_c]; exact c_pos modelFacts ringPorts x hb hx)
    exact this
  obtain ⟨t, j, _, hj, hyt⟩ := ArithmeticThirteenSeed.strong_index aV ((CurrentMasks2011.beta : V) * w 0) cV hbJ hcpos
  have hR3 : RV % 4 = 3 := hR4
  obtain ⟨T, u, y, hf, hT, hu, hy, hn, hyI, _, hlit, _, haux', hres⟩ :=
    ArithmeticThirteenSeed.auxiliary_seed_of aV RV t ((CurrentMasks2011.beta : V) * w 0 * j) hR3
      (mul_pos hbJ hj) (by rw [hyt, ← hc])
  rw [← hc] at hn hlit haux' hres
  -- ring-level fresh coordinates
  set fR := ι (xcoord t aV)
  set iR := ι j
  set TR := ι T
  set IV := delta aV * ((CurrentMasks2011.beta : V) * w 0 * j) * cV * cV with hIV
  have hstrongR : fR ^ 2 - (Carrier65.core ringPorts x).delta *
      (ringPorts 0 * x 0 * iR * (Carrier65.core ringPorts x).c ^ 2) ^ 2 = 1 := by
    rw [eq_delta, eq_c, port0]
    have e := congrArg (ι : V →+* DiffRing V) hn
    simp only [map_add, map_mul, map_one] at e
    simp only [hxdef] at e ⊢
    linear_combination e
  have hVdef : ι u = fR ^ 2 * ((Carrier65.core ringPorts x).c * TR - (Carrier65.core ringPorts x).rank) -
      (Carrier65.core ringPorts x).c := by
    rw [eq_c, eq_rank]
    have e := congrArg (ι : V →+* DiffRing V) hlit
    simp only [map_add, map_mul] at e
    linear_combination -e
  -- the independent m
  obtain ⟨e4, he4⟩ : (4 * ((CurrentMasks2011.beta : V) * w 0)) ∣ y + 1 := by
    have h1 : 4 * IV * IV ∣ y + 1 := mod_eq_zero_iff_dvd.mp hres
    refine dvd_trans ⟨delta aV * j * cV * cV * IV, by ring⟩ h1
  set yR : DiffRing V := -ι y
  have hSR : (Carrier65.core ringPorts x).delta * (ringPorts 0 * x 0 * iR * (Carrier65.core ringPorts x).c ^ 2) = ι IV := by
    rw [eq_delta, eq_c, port0]; simp only [hxdef, map_mul, IV]; ring
  have hauxR : (ι IV) ^ 2 * ((ι u) ^ 2 - yR ^ 2) + yR ^ 2 = 1 := by
    have e := congrArg (ι : V →+* DiffRing V) haux'
    simp only [map_add, map_mul, map_one] at e
    simp only [yR]
    linear_combination e
  set bR := ringPorts 0 * x 0
  have hbR : bR = ι ((CurrentMasks2011.beta : V) * w 0) := by simp only [bR, port0, hxdef, map_mul]
  have hS2 : 2 ≤ ι IV := by
    rw [← hSR]
    have ha0 : 0 ≤ (Carrier65.core ringPorts x).a := by rw [eq_a]; exact ι_nonneg _
    have hδ3 : 3 ≤ (Carrier65.core ringPorts x).delta := by
      change 3 ≤ (Carrier65.core ringPorts x).a ^ 2 + (4 * (Carrier65.core ringPorts x).a + 3)
      linarith only [sq_nonneg (Carrier65.core ringPorts x).a, ha0]
    have hb1 : 1 ≤ bR := model_discrete _ (by rw [hbR]; exact ι_pos hbJ)
    have hi1 : 1 ≤ iR := model_discrete _ (ι_pos hj)
    have hc1 : 1 ≤ (Carrier65.core ringPorts x).c := model_discrete _ (c_pos modelFacts ringPorts x hb hx)
    have hc2 : 1 ≤ (Carrier65.core ringPorts x).c ^ 2 := one_le_pow₀ hc1
    have hbi : 1 ≤ bR * iR := one_le_mul_of_one_le_of_one_le hb1 hi1
    have hbic : 1 ≤ bR * iR * (Carrier65.core ringPorts x).c ^ 2 :=
      one_le_mul_of_one_le_of_one_le hbi hc2
    have := le_mul_of_one_le_right (by linarith only [hδ3] : (0 : DiffRing V) ≤ _) hbic
    linarith only [this, hδ3]
  obtain ⟨_, hsmall⟩ := ModelThirteenRestoration.auxiliary_estimates modelFacts hS2
    (show (ι IV) ^ 2 * (ι u) ^ 2 - ((ι IV) ^ 2 - 1) * yR ^ 2 = 1 by linear_combination hauxR)
  set gR := x 3 - 1
  have hgR : transport ringPorts x = bR * gR := hGb
  set mR : DiffRing V := -ι e4 + (1 + bR * (ι u) ^ 2) * gR
  have hym : yR = 1 + 4 * (bR * (mR - (ι u) ^ 2 * transport ringPorts x) - transport ringPorts x) := by
    have e := congrArg (ι : V →+* DiffRing V) he4
    simp only [map_add, map_mul, map_one, map_ofNat] at e
    simp only [yR, mR, hgR]
    rw [hbR]
    simp only [map_mul]
    linear_combination -e
  have hmpos : 0 < mR := by
    have hbpos : 0 < bR := by rw [hbR]; exact ι_pos hbJ
    have hsm : -2 * ι u < yR := by
      have := neg_abs_le yR
      have hu0 : |ι u| = ι u := abs_of_nonneg (ι_nonneg u)
      linarith only [this, hu0, hsmall]
    exact ModelThirteenRestoration.affine_carrier_pos modelFacts hbpos hG hsm hym
  have hauxFinal :
      let b := Carrier65.core ringPorts x
      let S := b.delta * (ringPorts 0 * x 0 * iR * b.c ^ 2)
      let U := fR ^ 2 * (b.c * TR - b.rank) - b.c
      let y := 1 + 4 * (ringPorts 0 * x 0 * (mR - U ^ 2 * transport ringPorts x) - transport ringPorts x)
      S ^ 2 * (U ^ 2 - y ^ 2) + y ^ 2 = 1 := by
    dsimp only
    rw [hSR, ← hVdef]
    rw [← hym]
    exact hauxR
  exact ⟨fR, iR, TR, mR, ι_pos hf, ι_pos hj, ι_pos hT, hmpos, hstrongR, hauxFinal⟩

end DiophantineConsistency.ModelThirteenCarrier
#print axioms DiophantineConsistency.ModelThirteenCarrier.seed_construction
