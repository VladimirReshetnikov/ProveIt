import DiophantineConsistency.Source34.Source34Seeds
import DiophantineConsistency.Source34.Source34Halt
import DiophantineConsistency.Nine121.Source31Converse

/-! # The source34 converse: an internal halt gives the leaf facts

From the canonical halt data at the source34 ports
(`Source34Seeds.halt_first_gamma`) this module builds, exactly as
`Nine121.Source31Converse` does at 121x8801, the 31 coordinates
`J F α z f h i o j s w τ η ζ y γ N E P c a X D C2 L F2 V g I Baux Δ` of the
31-input parent source and shows that every parent row
(`Source31Rows.rows`, read at the source34 ports) vanishes (`converse`). The
ring identity `Source31Converse.rows_zero` is generic and used directly; only
the port casts `cp0 … cp3` and the halt data change.

`Source31Facts.facts_ports` is generic in the ports (it needs only
`0 < β`, `MC < β`, `MF < 2β`, `46 ≤ β`, which `Source34Ports.leaf_bounds`
supplies), so the parent zero gives the six leaf facts
`CompactLeafFacts.LeafFacts` at the source34 ports, at the positive valuation
`![J, F, α, 1, 1, X, Y, 1, η, ζ, 1, 1]` (`converse_facts`). Together with the
soundness chain `Source34Halt.halts_of_facts` this is `halt_iff_facts`: in
every model of `𝗜𝚺₁`, machine 215 halts internally iff the leaf facts have a
positive solution at the source34 ports. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
noncomputable section
namespace Source34Converse
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ModelDifferenceRing
open Nine121
open ArithmeticPow ArithmeticPacking ArithmeticRepunit ArithmeticPellRecurrence ArithmeticPellHalfIndex
  ArithmeticOuterSeed
open Mixed121Kernel (rho)
open Source34Kernel Source34ConstructedRank Source34Word Source34Seeds
open Mixed121Word (haltRow haltLength haltStride)
open Mixed121Column (perturb perturb_definable)
open P72ConvArith (k_large)
open P72Root (ι_tsub)
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC

attribute [local irreducible] paramKernel rho Source34Ports.lowNat Source34Ports.highNat
  Source34Ports.betaNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## The source34 ports, cast -/

theorem beta_eq : ((Source34Ports.betaNat : ℕ) : V) = Exp.exp (1064921 : V) - 1 := by
  have h := Source34Ports.beta_identity (V:=V)
  rw [show (121:V)*8801 = 1064921 by norm_num] at h
  exact eq_tsub_of_add_eq h

theorem cp0 : (((Source34Ports.ports 0 : ℕ) : ℤ) : DiffRing V) = ι (Exp.exp (1064921 : V) - 1) := by
  unfold Source34Ports.ports
  rw [Source34Ports.ports_zero, Int.cast_natCast, ← map_natCast ι, beta_eq]

theorem cp1 : (((Source34Ports.ports 1 : ℕ) : ℤ) : DiffRing V) = ι ((paramKernel rho : ℕ) : V) := by
  unfold Source34Ports.ports
  rw [P55Converse.ports_one, Int.cast_natCast, ← map_natCast ι]

theorem cp2 : (((Source34Ports.ports 2 : ℕ) : ℤ) : DiffRing V) = ι (low : V) := by
  unfold Source34Ports.ports
  rw [Source34Ports.ports_two, Int.cast_natCast, ← map_natCast ι]

theorem cp3 : (((Source34Ports.ports 3 : ℕ) : ℤ) : DiffRing V) =
    ι (high + (Exp.exp (1064921 : V) - 1)) := by
  unfold Source34Ports.ports
  rw [Source34Ports.ports_three, Int.cast_natCast, ← map_natCast ι, Nat.cast_add, beta_eq, add_comm]

/-! ## The parent zero -/

private theorem aux_gt {I w y : DiffRing V} (h : I * I * w * w + y * y = 1 + I * I * y * y)
    (hy : 2 ≤ y) (hw : 0 ≤ w) : w < y := by
  by_contra hlt
  have hle : y ≤ w := le_of_not_gt hlt
  have h1 : I * I * y * y ≤ I * I * w * w := by
    have := mul_le_mul hle hle (by linarith) hw
    nlinarith [mul_self_nonneg I]
  nlinarith

/-- **The converse**: an internal halt of machine 215 gives a positive zero of
the parent source at the source34 ports. -/
theorem converse (T : V) (hT : ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0) :
    ∃ x : Fin 31 → V, (∀ i, 0 < x i) ∧
      ∀ k, Source31Rows.rows (Source31Facts.portsR Source34Ports.ports) (fun i => ι (x i)) k = 0 := by
  obtain ⟨δ, _, _, _, hpack, hx, hresult⟩ := halt_first_gamma T hT
  let Xf := perturb (baseCell (haltRow T)) δ
  letI : 𝚺₁-Function₁ Xf := hx
  let N := haltLength T
  let stride := haltStride T
  let K : V := paramKernel rho
  let u : V := 1064921 * N
  let R := rank K N stride Xf
  let q := Exp.exp u
  let wX := Exp.exp (R - u)
  obtain ⟨_, z, hz, hqw, htrv, sY, n, eta, zeta, gammaOld, hsY, _, he, hzz, hgpos,
    hseed, _, haux, _, _⟩ := hresult
  obtain ⟨f, i, auxT, auxw, y, hf, hi, _, hw0, hy, _, _, hstrong,
    hydef, _, _, hufmod, hucmod, _, _, hauxnorm, _, _, _, _, _⟩ := haux
  have hp : PackingInput 1064921 K low high N stride Xf := hpack
  -- the packing coordinates
  let Cv := Cw 1064921 N Xf
  let Fv := Fw 1064921 K N stride Xf
  let αv := alpha 1064921 K N stride Xf
  have hF : 0 < Fv := F_pos hp
  obtain ⟨hα, hsum⟩ := packing_alpha hp
  have hqsum : q = Fv + (Cv + αv) := by
    have h : q = Cv + Fv + αv := hsum.symm
    rw [h]; ring
  -- q = 1 + Jβ
  let J := rep 1064921 N
  have hq1 : 1 ≤ q := one_le_exp _
  have hqJ' : (Exp.exp (1064921 : V) - 1) * J + 1 = q := repunit_identity 1064921 N
  dsimp only [SeedRelations] at hseed
  obtain ⟨hτn, hdn, hcy, _, r', hRr, _, hkB⟩ := hseed
  -- the registers
  let Xv : V := Exp.exp R
  let Y : V := sY * q ^ 3
  let E : V := Xv * Y
  let k : V := eta + zeta
  let c : V := k * Y + eta
  let a : V := E + Y
  let τ : V := E * n + k - R
  let B : V := 2 * (E * Y - 1) + 1
  have hτn' : τ * τ = 1 + (E * Y) * (E * Y + 1) * k * k := hτn
  have hcy' : c = ycoord R a := hcy
  have hkB' : k = 2 * ycoord (r' + 1) B := hkB
  -- sizes
  have hN0 : 0 < N := power_pos _ _ (by norm_num)
  have hN1 : 1 ≤ N := pos_iff_one_le.mp hN0
  have hu1 : 1 ≤ u := le_trans hN1 (le_mul_of_one_le_left (Arithmetic.zero_le _) (by norm_num))
  have hq2 : 2 ≤ q := by
    have h := exp_monotone_le.mpr hu1
    have e1 : Exp.exp (1 : V) = 2 := by
      have := exp_succ (0 : V); rw [zero_add, exp_zero, mul_one] at this; exact this
    rwa [e1] at h
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq2
  have hq3c : 1 ≤ q ^ 3 := one_le_pow₀ (le_trans (by norm_num) hq2)
  have hY0 : 0 < Y := mul_pos hsY (lt_of_lt_of_le (by norm_num) hq3c)
  have hXv1 : 1 ≤ Xv := one_le_exp _
  have hE1 : 1 ≤ E := one_le_mul_of_one_le_of_one_le hXv1 (pos_iff_one_le.mp hY0)
  have hEY1 : 1 ≤ E * Y := one_le_mul_of_one_le_of_one_le hE1 (pos_iff_one_le.mp hY0)
  have hR3 : 3 ≤ R := by
    have h : 2 * u < R := (properties hp).2.2
    calc (3 : V) = 2 * 1 + 1 := by norm_num
      _ ≤ 2 * u + 1 := (add_le_add_iff_right 1).mpr (mul_le_mul_of_nonneg_left hu1 (by simp))
      _ ≤ R := lt_iff_succ_le.mp h
  have hr1 : 1 ≤ r' := by
    have h : 2 * 1 + 1 ≤ 2 * r' + 1 := by
      calc (2 * 1 + 1 : V) = 3 := by norm_num
        _ ≤ R := hR3
        _ = 2 * r' + 1 := hRr
    exact le_of_mul_le_mul_left ((add_le_add_iff_right 1).mp h) (by norm_num)
  have hk4 : 4 * (B + 2) ≤ k := k_large r' B k hr1 hkB'
  have hB2 : B + 2 = 2 * (E * Y) + 1 := by
    show 2 * (E * Y - 1) + 1 + 2 = 2 * (E * Y) + 1
    have := tsub_add_cancel_of_le hEY1
    calc 2 * (E * Y - 1) + 1 + 2 = 2 * (E * Y - 1 + 1) + 1 := by ring
      _ = 2 * (E * Y) + 1 := by rw [this]
  -- y > auxw
  have hwy : auxw < y := by
    have hy2 : (2 : DiffRing V) ≤ ι y := by
      have h : 2 ≤ y := by
        rw [hydef]; exact le_trans (le_trans (by norm_num) hR3) (time_le_y _ _)
      have h' := (ι_le_ι (V := V)).mpr h; rwa [map_ofNat] at h'
    have hn := congrArg ι hauxnorm
    simp only [map_add, map_mul, map_one] at hn
    exact (ι_lt_ι (V := V)).mp (aux_gt hn hy2 (ι_nonneg _))
  -- k = R + 1 + 4EYs'
  have hB1 : 2 * (E * Y) ∣ B + 1 := ⟨1, by
    have : B + 1 + 1 = 2 * (E * Y) + 1 := by rw [← hB2]; ring
    rw [mul_one]; exact add_right_cancel this⟩
  obtain ⟨_, s', _, hys⟩ := ArithmeticPellCongruences.residue_quotients (r' + 1) B (2 * (E * Y)) hB1
  have hRr' : R = 2 * r' + 1 := hRr
  have hk2 : k = R + 1 + 4 * (E * Y) * s' := by rw [hkB', hys, hRr']; ring
  have hs'1 : 1 ≤ s' := by
    rcases (Arithmetic.zero_le s').lt_or_eq with h | h
    · exact pos_iff_one_le.mp h
    · exfalso
      rw [← h, mul_zero, add_zero] at hk2
      have hRE : R < E * Y := lt_of_lt_of_le (lt_exp R) (le_trans (le_mul_of_one_le_right
        (Arithmetic.zero_le _) (pos_iff_one_le.mp hY0)) (le_mul_of_one_le_right (Arithmetic.zero_le _)
        (pos_iff_one_le.mp hY0)))
      have : R + 1 < 4 * (B + 2) := by
        rw [hB2]
        calc R + 1 < E * Y + 1 := (add_lt_add_iff_right 1).mpr hRE
          _ ≤ 4 * (2 * (E * Y) + 1) := by
            rw [show (4 : V) * (2 * (E * Y) + 1) = (E * Y + 1) + (7 * (E * Y) + 3) by ring]
            exact le_add_of_nonneg_right (Arithmetic.zero_le _)
      exact absurd (le_trans hk4 (le_of_eq hk2)) (not_le_of_gt this)
  -- the residues of the auxiliary ordinate
  have hc0 : 0 < c := add_pos_of_nonneg_of_pos (Arithmetic.zero_le _) he
  obtain ⟨o0, ho0⟩ : f * f ∣ auxw + c := by
    rw [hcy']; exact mod_eq_zero_iff_dvd.mp hufmod
  obtain ⟨j0, hj0⟩ : c ∣ auxw + R := by
    rw [hcy']; exact mod_eq_zero_iff_dvd.mp hucmod
  have ho0pos : 0 < o0 := by
    rcases (Arithmetic.zero_le o0).lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h, mul_zero] at ho0
      exact absurd ho0 (ne_of_gt (add_pos_of_pos_of_nonneg hw0 (Arithmetic.zero_le _)))
  have hj0pos : 0 < j0 := by
    rcases (Arithmetic.zero_le j0).lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h, mul_zero] at hj0
      exact absurd hj0 (ne_of_gt (add_pos_of_pos_of_nonneg hw0 (Arithmetic.zero_le _)))
  -- the positive coordinates
  have hJ0 : 0 < J := by
    rcases (Arithmetic.zero_le J).lt_or_eq with h | h
    · exact h
    · exfalso
      have hq' : q = 1 := by rw [← hqJ', ← h, mul_zero, zero_add]
      rw [hq'] at hq2
      exact absurd hq2 (by norm_num)
  have hwX0 : 0 < wX := lt_of_lt_of_le (by norm_num) (one_le_exp _)
  have hdelta0 : 0 < delta a := by
    unfold delta
    exact mul_pos (add_pos_of_nonneg_of_pos (Arithmetic.zero_le _) (by norm_num))
      (add_pos_of_nonneg_of_pos (Arithmetic.zero_le _) (by norm_num))
  have hτ0 : 0 < τ := by
    rcases (Arithmetic.zero_le τ).lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h, mul_zero] at hτn'
      exact absurd hτn'.symm (ne_of_gt (lt_of_lt_of_le _root_.zero_lt_one le_self_add))
  have hqq1 : 1 ≤ q * q := one_le_mul_of_one_le_of_one_le hq1 hq1
  have hq22 : 2 ≤ q * q := le_trans hq2 (le_mul_of_one_le_left (Arithmetic.zero_le _) hq1)
  let x : Fin 31 → V := ![J, Fv, αv, z + 1, f, 4 * Y * s', delta a * i, f * o0, j0, sY, wX, τ,
    eta, zeta, y, gammaOld, q * (q * q), E, E * Y * k + k, c, a, Xv,
    Xv + a * c + gammaOld * (4 * a + 3), c * c, q * q - 1, f * f, auxw, y * y - auxw * auxw,
    delta a * i * (c * c), (delta a * i * (c * c)) * (delta a * i * (c * c)), delta a]
  have hpos : ∀ j', 0 < x j' := by
    intro j'
    fin_cases j'
    · exact hJ0
    · exact hF
    · exact hα
    · exact lt_of_lt_of_le (by simp) le_add_self
    · exact hf
    · exact mul_pos (mul_pos (by norm_num) hY0) (lt_of_lt_of_le (by norm_num) hs'1)
    · exact mul_pos hdelta0 hi
    · exact mul_pos hf ho0pos
    · exact hj0pos
    · exact hsY
    · exact hwX0
    · exact hτ0
    · exact he
    · exact hzz
    · exact hy
    · exact hgpos
    · exact mul_pos hq0 (mul_pos hq0 hq0)
    · exact lt_of_lt_of_le (by norm_num) hE1
    · exact add_pos_of_nonneg_of_pos (Arithmetic.zero_le _) (add_pos_of_nonneg_of_pos
        (Arithmetic.zero_le _) hzz)
    · exact hc0
    · exact add_pos_of_pos_of_nonneg (lt_of_lt_of_le (by norm_num) hE1) (Arithmetic.zero_le _)
    · exact lt_of_lt_of_le (by norm_num) hXv1
    · exact add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (lt_of_lt_of_le (by norm_num) hXv1)
        (Arithmetic.zero_le _)) (Arithmetic.zero_le _)
    · exact mul_pos hc0 hc0
    · exact tsub_pos_of_lt (lt_of_lt_of_le (by norm_num) hq22)
    · exact mul_pos hf hf
    · exact hw0
    · exact tsub_pos_of_lt (mul_self_lt_mul_self (Arithmetic.zero_le _) hwy)
    · exact mul_pos (mul_pos hdelta0 hi) (mul_pos hc0 hc0)
    · exact mul_pos (mul_pos (mul_pos hdelta0 hi) (mul_pos hc0 hc0))
        (mul_pos (mul_pos hdelta0 hi) (mul_pos hc0 hc0))
    · exact hdelta0
  refine ⟨x, hpos, ?_⟩
  -- the ports, in the ring of differences
  have e0 : Source31Facts.portsR Source34Ports.ports 0 = ι (Exp.exp (1064921 : V) - 1) :=
    cp0
  have e1 : Source31Facts.portsR Source34Ports.ports 1 = ι K := cp1
  have e2 : Source31Facts.portsR Source34Ports.ports 2 = ι (low : V) := cp2
  have e3 : Source31Facts.portsR Source34Ports.ports 3 = ι (high + (Exp.exp (1064921 : V) - 1)) :=
    cp3
  have hιq : Source31Facts.portsR Source34Ports.ports 0 * ι J + 1 = ι q := by
    rw [e0, ← map_mul, ← map_one ι, ← map_add, hqJ']
  -- the rank, read from the packing
  have hFq : Fv ≤ q := le_of_lt (lt_of_lt_of_le (F_lt_M hp) tsub_le_self)
  have hq2' : 1 ≤ q ^ 2 := one_le_pow₀ hq1
  have hRR : ((ι q - 1) * (ι q - ι Fv) + ι αv) * (ι q * ι q - 1) +
      (Source31Facts.portsR Source34Ports.ports 2 + ι q * Source31Facts.portsR Source34Ports.ports 3) *
        ι J = ι R := by
    rw [e2, e3]
    change _ = ι (((q-1)*(q-Fv)+αv)*(q^2-1) + ((low:V)+q*(high+(Exp.exp (1064921:V)-1)))*J)
    simp only [map_add, map_mul, ι_tsub hq1, ι_tsub hFq, ι_tsub hq2', map_one, map_pow]
    ring
  have hιc : ι c = ι (ycoord R a) := by rw [hcy']
  -- the register identities, in the ring of differences
  let P0 : DiffRing V := Source31Facts.portsR Source34Ports.ports 0
  have hιY : ι Y = ι sY * ι (q * (q * q)) := by simp only [Y, map_mul, map_pow]; ring
  have h16 : ι (q * (q * q)) = (P0 * ι J + 1) * ((P0 * ι J + 1) * (P0 * ι J + 1)) := by
    rw [hιq]; simp only [map_mul]
  have h17 : ι E = ι Xv * (ι sY * ι (q * (q * q))) := by show ι (Xv * Y) = _; rw [map_mul, hιY]
  have h18 : ι (E * Y * k + k) = ι E * (ι sY * ι (q * (q * q))) * (ι eta + ι zeta) +
      (ι eta + ι zeta) := by
    rw [← hιY]; simp only [k, map_mul, map_add]
  have h19 : ι c = (ι eta + ι zeta) * (ι sY * ι (q * (q * q))) + ι eta := by
    rw [← hιY]; simp only [c, k, map_mul, map_add]
  have h20 : ι a = ι E + ι sY * ι (q * (q * q)) := by
    rw [← hιY]; simp only [a, map_add]
  have h21 : ι Xv = ι wX * (P0 * ι J + 1) := by
    rw [hιq, ← map_mul, mul_comm wX q, hqw]
  have h22 : ι (Xv + a * c + gammaOld * (4 * a + 3)) =
      ι Xv + ι a * ι c + ι gammaOld * (4 * ι a + 3) := by
    simp only [map_add, map_mul, map_ofNat]
  have h23 : ι (c * c) = ι c * ι c := map_mul ι c c
  have h24 : ι (q * q - 1) = (P0 * ι J + 1) * (P0 * ι J + 1) - 1 := by
    rw [ι_tsub hqq1, map_mul, map_one, hιq]
  have h25 : ι (f * f) = ι f * ι f := map_mul ι f f
  have hww : auxw * auxw ≤ y * y := mul_self_le_mul_self (Arithmetic.zero_le _) (le_of_lt hwy)
  have h27 : ι (y * y - auxw * auxw) = ι y * ι y - ι auxw * ι auxw := by
    rw [ι_tsub hww, map_mul, map_mul]
  have h28 : ι (delta a * i * (c * c)) = ι (delta a * i) * ι (c * c) := map_mul ι _ _
  have h29 : ι ((delta a * i * (c * c)) * (delta a * i * (c * c))) =
      ι (delta a * i * (c * c)) * ι (delta a * i * (c * c)) := map_mul ι _ _
  have h30 : ι (delta a) = ι a * ι a + 4 * ι a + 3 := by
    unfold delta; simp only [map_mul, map_add, map_ofNat, map_one]; ring
  have Cτ : ι τ * ι τ = 1 + ι (E * Y * k + k) * (ι (E * Y * k + k) - (ι eta + ι zeta)) := by
    have h := congrArg ι hτn'
    simp only [map_add, map_mul, map_one] at h
    rw [h]; simp only [k, map_mul, map_add]; ring
  have Cmain : ι (Xv + a * c + gammaOld * (4 * a + 3)) * ι (Xv + a * c + gammaOld * (4 * a + 3)) =
      1 + ι (delta a) * ι (c * c) := by
    have h := congrArg ι hdn
    unfold delta
    simp only [Xv, Y, E, k, c, a, q, u, N, R] at h ⊢
    simp only [map_add, map_mul, map_one, map_ofNat, map_pow] at h ⊢
    linear_combination h
  have Cidx : ι auxw + (ι eta + ι zeta) = 1 + ι j0 * ι c + ι (4 * Y * s') * ι E := by
    have h1 := congrArg ι hj0
    have h2 := congrArg ι hk2
    simp only [map_add, map_mul, map_one, map_ofNat] at h1 h2
    simp only [E, k, map_mul, map_add, map_ofNat] at h2 ⊢
    linear_combination h2 + h1
  have Cjc : ι j0 * ι c - ι auxw = (((P0 * ι J + 1) - 1) * ((P0 * ι J + 1) - ι Fv) + ι αv) *
        ((P0 * ι J + 1) * (P0 * ι J + 1) - 1) +
      (Source31Facts.portsR Source34Ports.ports 2 +
        (P0 * ι J + 1) * Source31Facts.portsR Source34Ports.ports 3) * ι J := by
    have h1 := congrArg ι hj0
    simp only [map_add, map_mul] at h1
    rw [hιq]
    linear_combination -h1 - hRR
  have Ctr : (Source31Facts.portsR Source34Ports.ports 1 + ι wX) * ((P0 * ι J + 1) - ι Fv - ι αv) =
      ι Fv + (ι (z + 1) - 1) * ((P0 * ι J + 1) - 1) := by
    have h := congrArg ι htrv
    simp only [map_add, map_mul] at h
    rw [ι_tsub hq1, map_one] at h
    rw [e1, hιq]
    have hιq' : ι q = ι Fv + (ι Cv + ι αv) := by rw [hqsum]; simp only [map_add]
    simp only [map_add, map_one]
    linear_combination h + (ι K + ι wX) * hιq'
  have Cfo : ι auxw + ι c = ι f * ι (f * o0) := by
    have h := congrArg ι ho0
    simp only [map_add, map_mul] at h
    simp only [map_mul]
    linear_combination h
  have Cstr : ι (delta a * i * (c * c)) * ι (delta a * i * (c * c)) + ι (delta a) =
      ι (delta a) * ι (f * f) := by
    have h := congrArg ι hstrong
    simp only [map_add, map_mul, map_one] at h
    rw [← hιc] at h
    simp only [map_mul]
    linear_combination -(ι (delta a)) * h
  have Caux : ι y * ι y = 1 + ι (y * y - auxw * auxw) *
      ι ((delta a * i * (c * c)) * (delta a * i * (c * c))) := by
    have h := congrArg ι hauxnorm
    simp only [map_add, map_mul, map_one] at h
    rw [← hιc] at h
    rw [h27]
    simp only [map_mul]
    linear_combination h
  exact Source31Converse.rows_zero _ (fun i => ι (x i)) h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h27 h28 h29 h30
    Cτ Cmain Cidx Cjc Ctr Cfo Cstr Caux


/-! ## The leaf facts -/

attribute [local irreducible] Source34Ports.ports

/-- **The source34 converse**: an internal halt of machine 215 gives a
positive valuation satisfying the six leaf facts at the source34 ports. -/
theorem converse_facts (T : V) (hT : ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0) :
    ∃ v : Fin 12 → V, (∀ j, 0 < v j) ∧ CompactLeafFacts.LeafFacts Source34Ports.ports v := by
  obtain ⟨x, hx, hz⟩ := converse T hT
  obtain ⟨hb, hl, hh, h46⟩ := Source34Ports.leaf_bounds (V := V)
  obtain ⟨X, Y, hX, hY, hF⟩ := Source31Facts.facts_ports Source34Ports.ports hb hl hh h46 x hx hz
  refine ⟨_, ?_, hF⟩
  intro i
  fin_cases i <;> simp [hX, hY, hx]

/-- **Round trip.** Internal halting of machine 215 is equivalent to a
positive solution of the leaf facts at the source34 ports. -/
theorem halt_iff_facts :
    (∃ T : V, ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0) ↔
      ∃ v : Fin 12 → V, (∀ j, 0 < v j) ∧ CompactLeafFacts.LeafFacts Source34Ports.ports v := by
  constructor
  · rintro ⟨T, hT⟩
    exact converse_facts T hT
  · rintro ⟨v, hv, hz⟩
    exact Source34Halt.halts_of_facts v hv hz

end Source34Converse

#print axioms Source34Converse.cp0
#print axioms Source34Converse.cp3
#print axioms Source34Converse.converse
#print axioms Source34Converse.converse_facts
#print axioms Source34Converse.halt_iff_facts
