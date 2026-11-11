import DiophantineConsistency.Z10.Z10Code
import DiophantineConsistency.Z10.Z10Ratio
import DiophantineConsistency.Z10.Z10Guard
import DiophantineConsistency.Z10.Z10Bootstrap
import DiophantineConsistency.Z10.Z10Lucas
import DiophantineConsistency.ModelProductPell
import DiophantineConsistency.ModelExponentialCongruence
import DiophantineConsistency.ArithmeticPellStrongDivisibility
import DiophantineConsistency.ArithmeticPellCongruences
import DiophantineConsistency.ZRows.CoprimeSquares
import DiophantineConsistency.Nine121.Source31Converse

/-! # Ten-integer package 106: the completed registers of a halting run

Completeness steps C1–C7 of the route, register part. From an internal halting
run of machine 215 the theorem `bridge_complete` chooses the first six unknowns
`t, g₀, c₀, k₀, l, w` of the equation of package 106 so that, whatever the last
four unknowns are, the registers satisfy (`Done`):

* `b = (2^s)²`, `X = Xn ≥ 8` natural, `B1 = 2 Xn + 1`;
* `halfA = a + 2` and `C = ψ_a(2 Xn + 1)`, so `D = (2 χ_a(2 Xn + 1))²`;
* `Q = χ_pp(Xn + 1)²` (`Phalf = pp + 2`, `K = ψ_pp(Xn + 1)`);
* `0 < Delta` (the guard) and `S = 4 a + 3 ∣ T`.

The chain is C1 (`Source31Converse.converse`), C2–C3 (`Z10Code.code_of_source`),
C4 (`Z10Contract.contract`), C5 (`Z10Ratio.bridge`) and C6
(`Z10Guard.guard_complete`). The two residues of C5 are proved here:

* `C_residue`: `ψ_a(4j + 3) ≡ −1 (mod 6)` when `3 ∣ a + 2`, so `C = 6 c₀ − 1`;
* `K_residue`: `ψ_p(n) ≡ n (mod (p + 1))` with quotient `≡ 4 b (mod 6 b)` when
  `6 b ∣ p + 2`, `2 ∣ n` and `n ≡ 4 b (mod 6 b)`. The quotient is read modulo
  `p + 2 ≡ 0`: there `p + 1 ≡ −1`, and `2 (p + 2) = ψ_p(2)` divides `ψ_p(n)`.
  So `K = X + 1 + b (6 k₀ + 4)(Phalf − 1)`.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.Z10BridgeComplete
open Nine121 Nine121.N105Layout Z10Regs

/-! ## Generic identities -/

section Generic
variable {𝔸 : Type*} [CommRing 𝔸]

theorem two_b_dvd_Bc {b : 𝔸} (h2 : (2 : 𝔸) ∣ b) : 2 * b ∣ Bc b := by
  obtain ⟨c, rfl⟩ := h2
  exact ⟨(radix : 𝔸) * c, by unfold Bc; ring⟩

/-- **`2b ∣ X + 1`** for an even base when `2b ∣ g`. -/
theorem two_b_dvd_Xc_succ (p : Fin 4 → 𝔸) {b g : 𝔸} (h2 : (2 : 𝔸) ∣ b) (hg : 2 * b ∣ g) :
    2 * b ∣ Xc p b g + 1 := by
  have hB := two_b_dvd_Bc h2
  have hN0 : 2 * b ∣ N0 b := hB.trans (dvd_pow_self _ (by norm_num))
  have hNN : 2 * b ∣ NN b := hB.trans (dvd_pow_self _ (by norm_num))
  have hS : 2 * b ∣ Sc p b g := by unfold Sc; exact dvd_add hg (hN0.mul_right _)
  have e : Xc p b g + 1 = NN b * (Sc p b g + Tc b + 1) - Sc p b g := by unfold Xc; ring
  rw [e]; exact dvd_sub (hNN.mul_right _) hS

/-- `X + 1 ≡ 4 b (mod 6 b)` from `2b ∣ X + 1`, `3 ∣ X` and `b = 6t + 4`. -/
theorem X1_sub (X b t α β : 𝔸) (hα : X + 1 = 2 * b * α) (hβ : X = 3 * β)
    (hb : b = 6 * t + 4) : X + 1 - 4 * b = 6 * b * (3 * α - β + 4 * t * α - 1) := by
  linear_combination (1 + 2 * b) * hα - 2 * b * hβ + 4 * b * α * hb

/-- The quotient of `K` read modulo `P = p + 2`. -/
theorem K_identity (K n P s b α β γ : 𝔸) (hK : K = n + (P - 1) * s)
    (hα : n - 4 * b = 6 * b * α) (hβ : P = 6 * b * β) (hγ : K = 6 * b * γ) :
    K = n + b * (6 * (α + β * s - γ) + 4) * (P - 1) := by
  linear_combination P * hK + (P - 1) * hα + (P - 1) * s * hβ - (P - 1) * hγ

theorem C_identity (y X q r : 𝔸) (e1 : y + (2 * X + 1) = 2 * q) (e2 : y + 1 = 3 * r) :
    y = 6 * (q - X - r) - 1 := by
  linear_combination 3 * e1 - 2 * e2

end Generic

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ModelDifferenceRing ArithmeticPellRecurrence ArithmeticBinomPascal
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

attribute [local irreducible] Mixed121Ports.ports

/-- The ports in the ring of differences. -/
local notation "pR" => Source31Facts.portsR (V := V) Mixed121Ports.ports

/-! ## The two residues -/

/-- **`C ≡ −1 (mod 6)`.** For `3 ∣ a + 2` the odd ordinate `ψ_a(4j + 3)` is `−1` modulo
`3` (`Z10Lucas.three_dvd_y`) and odd (`ModelProductPell.pp_parity`). -/
theorem C_residue (a Xn j w : V) (hw : a + 2 = 3 * w) (hj : 2 * Xn + 1 = 4 * j + 3) :
    ∃ c0 : DiffRing V, ι (ycoord (2 * Xn + 1) a) = 6 * c0 - 1 := by
  obtain ⟨⟨q, hq⟩, -⟩ := ModelProductPell.pp_parity a (2 * Xn + 1)
  obtain ⟨r, hr⟩ := Z10Lucas.three_dvd_y a w hw j
  rw [← hj] at hr
  refine ⟨ι q - ι Xn - ι r, ?_⟩
  have e1 := congrArg (ι (V := V)) hq
  have e2 := congrArg (ι (V := V)) hr
  simp only [map_add, map_mul, map_one, map_ofNat] at e1 e2
  exact C_identity _ _ _ _ e1 e2

/-- **The quotient of `K`.** `ψ_p(n) = n + b (6 k₀ + 4)(p + 1)` when `n` is even,
`6 b ∣ p + 2` and `6 b ∣ n − 4 b`. -/
theorem K_residue (Xn pp e : V) (b : DiffRing V) (he : Xn + 1 = 2 * e)
    (hP : 6 * b ∣ ι (pp + 2)) (hn : 6 * b ∣ ι (Xn + 1) - 4 * b) :
    ∃ k0 : DiffRing V,
      ι (ycoord (Xn + 1) pp) = ι (Xn + 1) + b * (6 * k0 + 4) * (ι (pp + 2) - 1) := by
  obtain ⟨-, s, -, hs⟩ :=
    ArithmeticPellCongruences.residue_quotients (Xn + 1) pp (pp + 1) dvd_rfl
  have hdiv : ycoord 2 pp ∣ ycoord (Xn + 1) pp :=
    (ArithmeticPellStrongDivisibility.y_dvd_iff pp 2 (Xn + 1)).mpr ⟨e, he⟩
  rw [Z10Lucas.y_two] at hdiv
  have hK6 : 6 * b ∣ ι (ycoord (Xn + 1) pp) :=
    hP.trans (map_dvd ι ((dvd_mul_left (pp + 2) 2).trans hdiv))
  obtain ⟨α, hα⟩ := hn
  obtain ⟨β, hβ⟩ := hP
  obtain ⟨γ, hγ⟩ := hK6
  refine ⟨α + β * ι s - γ, ?_⟩
  have hKs : ι (ycoord (Xn + 1) pp) = ι (Xn + 1) + (ι (pp + 2) - 1) * ι s := by
    rw [hs]; simp only [map_add, map_mul, map_one, map_ofNat]; ring
  exact K_identity _ _ _ _ _ _ _ _ hKs hα hβ hγ

/-! ## The completed registers -/

/-- What the first six unknowns of a halting run guarantee for the registers. -/
structure Done (R : Regs (DiffRing V)) (s Xn a qx : V) : Prop where
  hb : R.b = ι (Exp.exp s) * ι (Exp.exp s)
  hX : R.X = ι Xn
  hX8 : 8 ≤ Xn
  hhalfA : R.halfA = ι a + 2
  hB1 : R.B1 = 2 * ι Xn + 1
  hC : R.C = ι (ycoord (2 * Xn + 1) a)
  hD : R.D = (2 * ι (xcoord (2 * Xn + 1) a)) * (2 * ι (xcoord (2 * Xn + 1) a))
  hQ : R.Q = ι qx * ι qx
  hQpos : 0 < R.Q
  hDelta : 0 < R.Delta
  hS : R.S = 4 * ι a + 3
  hST : R.S ∣ R.T

/-- **The completed registers of a halting run** (steps C1–C7, register part). -/
theorem bridge_complete (T : V)
    (hT : ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0) :
    ∃ (t g0 c0 k0 l w : DiffRing V) (s Xn a pp : V),
      ∀ x : Fin 10 → DiffRing V, x 0 = t → x 1 = g0 → x 2 = c0 → x 3 = k0 → x 4 = l →
        x 5 = w → Done (regs pR x) s Xn a (xcoord (Xn + 1) pp) := by
  obtain ⟨p, hp, hz⟩ := Nine121.Source31Converse.converse T hT
  obtain ⟨s, t₀, g₀, z, hb6, h4b, hzb, hg0, hglo, hghi, hrows⟩ := Z10Code.code_of_source p hp hz
  obtain ⟨gW, hgW⟩ : ∃ gW : V, gW = ∑ i, z i * Z10Prefix.Bcm (Exp.exp (2 * s)) ^ weights i :=
    ⟨_, rfl⟩
  rw [← hgW] at hg0 hglo hghi
  have hb0 : 0 < Exp.exp (2 * s) := exp_pos _
  have hBcm : 0 < Z10Prefix.Bcm (Exp.exp (2 * s)) := lt_of_lt_of_le hb0 (Z10Code.le_Bcm hb0)
  have hgpos : 0 < gW := lt_of_lt_of_le (pow_pos hBcm 116) hglo
  have h4g : 4 ∣ gW := by rw [hg0]; exact h4b.mul_right _
  -- C4: the rank and the contract
  obtain ⟨Xn, hXn, hX8⟩ := Z10Prefix.prefix_naturals (Exp.exp (2 * s)) gW hb0
  obtain ⟨Yn, hYn⟩ : ∃ Yn : V, Yn = Exp.exp (2 * s) *
      (Exp.exp (34159017 : V) * Z10Prefix.Bcm (Exp.exp (2 * s)) ^ 2109) := ⟨_, rfl⟩
  have hYι : ι Yn = Yc (ι (Exp.exp (2 * s))) := by
    rw [hYn, map_mul, map_mul, map_pow, Z10Prefix.ι_Bcm, Z10Regs.Yc, Z10Prefix.threshold_eq']
  have hbι : (0 : DiffRing V) < ι (Exp.exp (2 * s)) := by
    have h := ι_lt_ι.mpr hb0; rwa [map_zero] at h
  have hgc' : ι gW < cap (ι (Exp.exp (2 * s))) := by
    rw [← Z10Code.ι_cap]; exact ι_lt_ι.mpr hghi
  have hgc : ι gW < 4 * cap (ι (Exp.exp (2 * s))) := by
    have := Z10Guard.capc_pos hbι; linarith
  have hdvd : Yn ∣ binom (2 * Xn) Xn :=
    (Z10Contract.contract (2 * s) gW Xn Yn hgc h4g hXn.symm hYι).mpr ⟨z, hzb, hgW, hrows⟩
  -- divisibilities of the rank
  have hb3 : (3 : DiffRing V) ∣ ι (Exp.exp (2 * s)) - 1 :=
    ⟨2 * ι t₀ + 1, by rw [hb6]; simp only [map_add, map_mul, map_ofNat]; ring⟩
  have hb2 : (2 : DiffRing V) ∣ ι (Exp.exp (2 * s)) :=
    ⟨3 * ι t₀ + 2, by rw [hb6]; simp only [map_add, map_mul, map_ofNat]; ring⟩
  have h2bB : 2 * Exp.exp (2 * s) ∣ Z10Prefix.Bcm (Exp.exp (2 * s)) :=
    ⟨Exp.exp (2134940 : V) * (3 * t₀ + 2), by rw [Z10Prefix.Bcm, hb6]; ring⟩
  have h2bg : 2 * ι (Exp.exp (2 * s)) ∣ ι gW := by
    have h := map_dvd ι (Z10Code.dvd_code h2bB z)
    rwa [← hgW, map_mul, map_ofNat] at h
  have hX1ι := two_b_dvd_Xc_succ pR hb2 h2bg
  rw [hXn] at hX1ι
  have hX1V : 2 * Exp.exp (2 * s) ∣ Xn + 1 := by
    refine ZRowsCoprimeSquares.ι_dvd_iff.mp ?_
    rwa [map_mul, map_ofNat, map_add, map_one]
  have hX3ι := Z10Bootstrap.Xc_mod3 pR (ι (Exp.exp (2 * s))) (ι gW) hb3
  rw [hXn] at hX3ι
  have hX3V : 3 ∣ Xn := by
    refine ZRowsCoprimeSquares.ι_dvd_iff.mp ?_
    rwa [map_ofNat]
  obtain ⟨α, hα⟩ := hX1V
  obtain ⟨β, hβ⟩ := hX3V
  have hX1pos : 0 < Xn + 1 := lt_of_lt_of_le (by norm_num) (le_add_left le_rfl : (1 : V) ≤ Xn + 1)
  -- C5: the ratio bridge
  have hBX : Exp.exp (2 * s) ≤ Xn + 1 := Arithmetic.le_of_dvd hX1pos ⟨2 * α, by rw [hα]; ring⟩
  have hs : 2 * s ≤ 2 * Xn + 1 := by
    have h1 : Xn + 1 ≤ 2 * Xn + 1 := by rw [two_mul, add_assoc]; exact le_add_left le_rfl
    exact le_trans (lt_exp _).le (le_trans hBX h1)
  have hE1 : (1 : V) ≤ Exp.exp (34159017 : V) * Z10Prefix.Bcm (Exp.exp (2 * s)) ^ 2109 :=
    pos_iff_one_le.mp (mul_pos (exp_pos _) (pow_pos hBcm _))
  have hbY : Exp.exp (2 * s) ≤ Yn := by
    rw [hYn]; exact le_mul_of_one_le_right (Arithmetic.zero_le _) hE1
  have hY64 : 64 ≤ Yn := calc
    (64 : V) ≤ 34159017 := by norm_num
    _ ≤ Exp.exp (34159017 : V) := (lt_exp _).le
    _ ≤ Exp.exp (34159017 : V) * Z10Prefix.Bcm (Exp.exp (2 * s)) ^ 2109 :=
        le_mul_of_one_le_right (Arithmetic.zero_le _) (pos_iff_one_le.mp (pow_pos hBcm _))
    _ ≤ Yn := by rw [hYn]; exact le_mul_of_one_le_left (Arithmetic.zero_le _) (pos_iff_one_le.mp hb0)
  obtain ⟨l₀, w₀, a, pp, -, -, hbw, ha, hpp, happ⟩ :=
    Z10Ratio.bridge s gW Xn Yn hgpos hX8 hs hY64 hbY hdvd
  -- the residues
  have hm0 : 0 < Exp.exp (2 * s) * α :=
    pos_of_mul_pos_right (show 0 < 2 * (Exp.exp (2 * s) * α) by rw [← mul_assoc, ← hα]; exact hX1pos)
      (by simp)
  have hm1 : 1 ≤ Exp.exp (2 * s) * α := pos_iff_one_le.mp hm0
  have hXj : Xn = 2 * (Exp.exp (2 * s) * α - 1) + 1 := by
    refine add_right_cancel (b := (1 : V)) ?_
    calc Xn + 1 = 2 * (Exp.exp (2 * s) * α - 1 + 1) := by
          rw [tsub_add_cancel_of_le hm1, hα]; ring
      _ = 2 * (Exp.exp (2 * s) * α - 1) + 1 + 1 := by ring
  have hj : 2 * Xn + 1 = 4 * (Exp.exp (2 * s) * α - 1) + 3 := by
    rw [hXj]; ring
  have hw3 : a + 2 = 3 * (β * (l₀ * Yn) * (4 * gW * w₀ * Yn + 1)) := by rw [ha, hβ]; ring
  obtain ⟨c0, hc0⟩ := C_residue a Xn _ _ hw3 hj
  have hP6 : 6 * ι (Exp.exp (2 * s)) ∣ ι (pp + 2) := by
    have h : pp + 2 = 6 * Exp.exp (2 * s) * (β * l₀ * (Exp.exp (34159017 : V) *
        Z10Prefix.Bcm (Exp.exp (2 * s)) ^ 2109) * (Xn * (l₀ * Yn)) * (4 * gW * w₀ * Yn)) := by
      rw [hpp, hβ, hYn]
      ring
    rw [h, map_mul, map_mul, map_ofNat]
    exact dvd_mul_right _ _
  have hn6 : 6 * ι (Exp.exp (2 * s)) ∣ ι (Xn + 1) - 4 * ι (Exp.exp (2 * s)) := by
    have hα' : ι Xn + 1 = 2 * ι (Exp.exp (2 * s)) * ι α := by
      have h := congrArg (ι (V := V)) hα
      simpa only [map_add, map_mul, map_one, map_ofNat] using h
    have hβ' : ι Xn = 3 * ι β := by
      have h := congrArg (ι (V := V)) hβ
      simpa only [map_mul, map_ofNat] using h
    have hb' : ι (Exp.exp (2 * s)) = 6 * ι t₀ + 4 := by
      rw [hb6]; simp only [map_add, map_mul, map_ofNat]
    refine ⟨3 * ι α - ι β + 4 * ι t₀ * ι α - 1, ?_⟩
    rw [map_add, map_one]
    exact X1_sub _ _ _ _ _ hα' hβ' hb'
  obtain ⟨k0, hk0⟩ := K_residue Xn pp (Exp.exp (2 * s) * α) (ι (Exp.exp (2 * s)))
    (by rw [hα]; ring) hP6 hn6
  -- C6–C7 inputs in the ring of differences
  have hgι : (0 : DiffRing V) < ι gW := by
    have h := ι_lt_ι.mpr hgpos; rwa [map_zero] at h
  have hc' : cap (ι (Exp.exp (2 * s))) * cap (ι (Exp.exp (2 * s))) ≤ ι gW * ι gW * ι gW := by
    rw [← Z10Code.ι_cap, ← map_mul, ← map_mul, ← map_mul]
    exact ι_le_ι.mpr (Z10Code.cap_sq_le hb0 hglo)
  have hKne : (ι (ycoord (Xn + 1) pp) : DiffRing V) ≠ 0 := by
    have h := ArithmeticPellRecurrence.ordinate_strictMono pp hX1pos
    simp only [y_zero] at h
    have h' := ι_lt_ι.mpr h
    rw [map_zero] at h'
    exact ne_of_gt h'
  have hnA := ArithmeticPellRecurrence.norm (2 * Xn + 1) a
  have hnK := ArithmeticPellRecurrence.norm (Xn + 1) pp
  unfold ArithmeticPellRecurrence.delta at hnA hnK
  have hnA' := congrArg (ι (V := V)) hnA
  have hnK' := congrArg (ι (V := V)) hnK
  simp only [map_add, map_mul, map_one, map_ofNat] at hnA' hnK'
  have hT2 := ModelExponentialCongruence.pow_congruence a (2 * Xn + 1)
  rw [sq] at hT2
  -- the six unknowns
  refine ⟨ι t₀, ι g₀, c0, k0, ι l₀, ι w₀, s, Xn, a, pp, ?_⟩
  intro x hx0 hx1 hx2 hx3 hx4 hx5
  have eb : (regs pR x).b = ι (Exp.exp (2 * s)) := by
    rw [b_def, hx0, hb6]; simp only [map_add, map_mul, map_ofNat]
  have eg : (regs pR x).g = ι gW := by rw [g_def, eb, hx1, hg0, map_mul]
  have eX : (regs pR x).X = ι Xn := by rw [X_def, eb, eg, hXn]
  have eY : (regs pR x).Y = ι Yn := by rw [Y_def, eb, ← hYι]
  have eL : (regs pR x).L = ι l₀ * ι Yn := by rw [L_def, hx4, eY]
  have ehalfA : (regs pR x).halfA = ι (a + 2) := by
    rw [Z10Bootstrap.halfA_eq, halfU_def, V_def, eL, eX, eg, hx5, eY, ha]
    simp only [map_add, map_mul, map_one, map_ofNat]
    ring
  have ePhalf : (regs pR x).Phalf = ι (pp + 2) := by
    rw [Phalf_def, U_def, uv_def, halfU_def, V_def, eL, eX, eg, hx5, eY, hpp]
    simp only [map_mul, map_ofNat]
    ring
  have eW : (regs pR x).W = ι (Exp.exp (2 * Xn + 1)) := by
    rw [W_def, eb, hx5, ← map_mul, hbw]
  have eC : (regs pR x).C = ι (ycoord (2 * Xn + 1) a) := by rw [C_def, hx2, hc0]
  have eK : (regs pR x).K = ι (ycoord (Xn + 1) pp) := by
    have e1 : ι (Xn + 1) = ι Xn + 1 := by rw [map_add, map_one]
    rw [K_def, k2_def, eX, eb, hx3, ePhalf, hk0, e1]
  have eA : (regs pR x).A = 2 * (ι a + 2) := by
    rw [A_def, ehalfA, map_add, map_ofNat]
  have eS : (regs pR x).S = 4 * ι a + 3 := by rw [S_def, eA]; ring
  have eQ : (regs pR x).Q = ι (xcoord (Xn + 1) pp) * ι (xcoord (Xn + 1) pp) := by
    rw [Q_def, ePhalf, eK, map_add, map_ofNat]
    linear_combination -hnK'
  refine ⟨?_, eX, hX8, ?_, ?_, eC, ?_, eQ, ?_, ?_, eS, ?_⟩
  · rw [eb, ← map_mul, ← exp_add, ← two_mul]
  · rw [ehalfA, map_add, map_ofNat]
  · rw [B1_def, eX]
  · rw [D_def, eA, eC]
    linear_combination (-4 : DiffRing V) * hnA'
  · rw [eQ, hnK']
    have h0 := ι_nonneg pp
    have hK0 := ι_nonneg (ycoord (Xn + 1) pp)
    have h1 : 0 ≤ (ι pp + 1) * (ι pp + 3) * ι (ycoord (Xn + 1) pp) * ι (ycoord (Xn + 1) pp) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) hK0) hK0
    linarith
  · rw [Delta_def, eg, cap_def, eb, eK, eC, eL]
    exact Z10Guard.guard_complete hgι hgc' hKne happ hc'
  · rw [eS, T_def, eW, eC]
    exact hT2

#print axioms C_residue
#print axioms K_residue
#print axioms bridge_complete

end DiophantineConsistency.Z10BridgeComplete
