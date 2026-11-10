import DiophantineConsistency.P137.P137Roots
import DiophantineConsistency.P138.P138Leaf

/-! # Soundness of package 137's 648/115 equation

A zero of the output `P137Value.value p x` gives `S ∣ Ac` (`P137Roots.S_dvd_Ac`), hence
`v = (1 + 2 v') q²` (`P137Bootstrap.recover`). At the recovered point
`x' = Function.update x 5 v'` and the native index `kN p x'`, every register of the weak front
is the corresponding register of package 138 (`P137Front.tr_*`), and the zero gives the folded
front `P138Rank.Folded p x' (kN p x')`. From there the soundness chain of package 138 (first
index, ratio, projector, orientation, leaf) applies unchanged: `P138Leaf.halt_of_folded`.

The fields of the record, and where they come from:

* `Budget > 0`: `P137Roots.budget_pos`.
* the main Pell pair `|c| = ψ_b(R)`, `R` odd, `Dm = χ_b(R)²`: `ZRowsStrongFold.strong_fold`,
  with the strong pair `f² = 1 + δ_b I₀²`, `I₀ = |A| |r| c² p₀` (here `Df = f²`, `BP = p₀²`,
  `U = A r c²`), `Q = (δ_b I₀)²`, the linear slot `V = f² · bOff − c`,
  `bOff = c − R + 4 U BP T`, and the adjacent equation of `P137Roots.descent`. The rank
  hypothesis is `bOff + R = c (1 + 4 A r c BP T) ≡ 0 (mod |c|)`; the size hypotheses
  `0 < 2R < |c|` are those of package 138 at the recovered point (`P138Budget.c_interval`,
  `P138Window.window`, `P138Window.k_ge`).
* `Dt = τ²`: `BP = P · Dm = p₀²` and `Dm = d²` give `P = t²`; `P = Dt · (1 + D4 Dt s²)` has
  coprime factors.
* `H ∣ Kq⁵`: `P137Bootstrap.H_dvd_Kq5`, `P137Bootstrap.Kq_transfer`. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.P137Fold
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing ZRowsCoprimeSquares P137Front P137Value P138Ports
open ArithmeticPellRecurrence ArithmeticPellHalfIndex
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC

attribute [local irreducible] Source34Ports.betaNat Source34Ports.lowNat Source34Ports.highNat
  Source34Kernel.paramKernel Mixed121Kernel.rho coneA coneB

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

section Regs
variable (p : Fin 6 → DiffRing V) (x : Fin 11 → DiffRing V) (v' : DiffRing V)
local notation "𝓕" => front p x
local notation "𝓑" => back p x
local notation "𝔵" => Function.update x 5 v'
local notation "𝓡" =>
  P138Value.regsK p (Function.update x 5 v') (P138Value.kN p (Function.update x 5 v'))

set_option maxHeartbeats 2000000 in
/-- **A zero of the 648/115 output gives the folded front of package 138** at the recovered
point and the native index. -/
theorem folded_of_zero (hp : PortFacts p) (hz : value p x = 0)
    (hv : x 5 = (1 + v' * 2) * (front p x).q2) :
    Nonempty (P138Rank.Folded p (Function.update x 5 v')
      (P138Value.kN p (Function.update x 5 v'))) := by
  -- the transfer equalities
  have eA : (𝓡).A = (𝓕).A := tr_A p x v' hv _
  have eR : (𝓡).R = (𝓕).R := tr_R p x v' _
  have eB : (𝓡).Budget = (𝓕).Budget := tr_Budget p x v' hv
  have eDt : (𝓡).Dt = (𝓕).Dt := tr_Dt p x v' hv
  have eDm : (𝓡).Dm = (𝓕).Dm := tr_Dm p x v' hv _
  have eH : (𝓡).H = (𝓕).H := tr_H p x v' hv _
  have e8 : 𝔵 8 = x 8 := upd_8 x v'
  -- the zero
  have hS := P137Roots.S_dvd_Ac p x hp hz
  have hB : 0 < (𝓡).Budget := by rw [eB]; exact P137Roots.budget_pos p x hp hz
  obtain ⟨p0, f, _, hp0, hf, _, hBP, hDf, _⟩ := P137Roots.roots p x hp hz
  obtain ⟨_, hr⟩ := P137Roots.s_r_ne p x hp hz
  have hc : x 8 ≠ 0 := by
    have := P138Budget.c_ne p 𝔵 _ hp hB
    rwa [e8] at this
  obtain ⟨y, _, haux, _⟩ := P137Roots.descent p x hp hz hc
  -- the base
  obtain ⟨Bn, hBn⟩ := abs_eq_ι (𝓕).A
  have hB3 : 3 ≤ Bn := by
    have h := P138Bootstrap.abs_A p 𝔵 (P138Value.kN p 𝔵) hp
    rw [eA, hBn, show (3 : DiffRing V) = ι 3 by rw [map_ofNat]] at h
    exact ι_le_ι.mp h
  obtain ⟨hD, hdb⟩ := ZRowsStrongFold.delta_of_abs hBn hB3
  have hDelta : (𝓕).Delta = ι (delta (Bn - 2)) := by rw [Delta_eq]; exact hD
  have hBn0 : 0 < Bn := lt_of_lt_of_le (by simp) hB3
  -- natural absolute values
  obtain ⟨rn, hrn⟩ := abs_eq_ι (x 4)
  obtain ⟨cn, hcn⟩ := abs_eq_ι (x 8)
  have hrn0 : 0 < rn := by
    rcases eq_zero_or_pos rn with h0 | h0
    · rw [h0, map_zero] at hrn; exact absurd (abs_eq_zero.mp hrn) hr
    · exact h0
  have hcn0 : 0 < cn := by
    rcases eq_zero_or_pos cn with h0 | h0
    · rw [h0, map_zero] at hcn; exact absurd (abs_eq_zero.mp hcn) hc
    · exact h0
  -- the strong pair
  obtain ⟨I0, hI0⟩ : ∃ I0 : V, I0 = Bn * rn * cn * cn * p0 := ⟨_, rfl⟩
  have hU2 : (𝓑).U ^ 2 = (ι Bn * ι rn * ι cn ^ 2) ^ 2 := by
    have h1 : (𝓑).U ^ 2 = |(𝓑).U| ^ 2 := (sq_abs _).symm
    rw [h1, U_eq, abs_mul, abs_mul, abs_pow, hBn, hrn, hcn]; ring
  have hstrong : f * f = 1 + delta (Bn - 2) * I0 * I0 := by
    apply ι_injective
    rw [hI0]
    simp only [map_mul, map_add, map_one]
    rw [← hDf, Df_eq, hDelta, hU2, hBP]; ring
  have hI0pos : 0 < I0 := by
    rw [hI0]; exact mul_pos (mul_pos (mul_pos (mul_pos hBn0 hrn0) hcn0) hcn0) hp0
  have hQJ : (𝓑).Q = ι (delta (Bn - 2) * I0) * ι (delta (Bn - 2) * I0) := by
    rw [Q_eq, hDelta, hU2, hBP, hI0]
    simp only [map_mul]; ring
  have hV : (𝓑).V = ι (f * f) * P137Roots.bOff p x - x 8 := by
    rw [P137Roots.V_bOff, hDf, map_mul]
  have hcdvd : cn * cn ∣ I0 := ⟨Bn * rn * p0, by rw [hI0]; ring⟩
  -- the rank and its size, from package 138 at the recovered point
  have hs := P138Rank.signs_of_budget p 𝔵 (P138Value.kN p 𝔵) hp hB
  obtain ⟨Rn, hRn', hlo, hhi⟩ := P138Window.window p 𝔵 (P138Value.kN p 𝔵) hp hs
  have hRn : (𝓕).R = ι Rn := by rw [← eR]; exact hRn'
  have hkR := P138Window.k_ge p 𝔵 (P138Value.kN p 𝔵) hp (P138Window.native_modulus p 𝔵 hp) hs
  have hci := (P138Budget.c_interval p 𝔵 (P138Value.kN p 𝔵) hp hB).1
  rw [e8] at hci
  have hY3 := P138Rank.three_le_abs_Y p 𝔵 (P138Value.kN p 𝔵) hp
  have hR0 : (0 : DiffRing V) ≤ ι Rn := ι_nonneg _
  have h2R : 2 * Rn < cn := by
    apply ι_lt_ι.mp
    rw [map_mul, map_ofNat, ← hcn]
    have h5 : 5 * ((𝓡).R + 1) ≤ |(𝓡).k| * (2 * |(𝓡).Y| - 1) := by
      have := mul_le_mul hkR (show (5 : DiffRing V) ≤ 2 * |(𝓡).Y| - 1 by linarith)
        (by norm_num) (abs_nonneg _)
      linarith
    rw [hRn'] at h5
    linarith
  have hRpos : 0 < Rn := by
    have : (0 : DiffRing V) ≤ |(𝓡).q| * ((𝓡).q ^ 2 - 1) := by
      have := P138Bootstrap.abs_q_ge p 𝔵 (P138Value.kN p 𝔵) hp
      have h64 : (2 : DiffRing V) ≤ 2 ^ 64 := by norm_num
      have : 1 ≤ (𝓡).q ^ 2 := by rw [← sq_abs]; nlinarith
      exact mul_nonneg (abs_nonneg _) (by linarith)
    exact P138EarlyFold.pos_of_ι (by linarith)
  have hcI : cn < I0 := by
    apply ι_lt_ι.mp
    rw [hI0]
    simp only [map_mul]
    have h2R' : 2 * (ι Rn : DiffRing V) < ι cn := by
      have := ι_lt_ι.mpr h2R
      rwa [map_mul, map_ofNat] at this
    have hR1 : (1 : DiffRing V) ≤ ι Rn := by
      rw [← map_one ι]; exact ι_le_ι.mpr (pos_iff_one_le.mp hRpos)
    have hc2 : (2 : DiffRing V) ≤ ι cn := by linarith
    have hr1 : (1 : DiffRing V) ≤ ι rn := by
      rw [← map_one ι]; exact ι_le_ι.mpr (pos_iff_one_le.mp hrn0)
    have hp1 : (1 : DiffRing V) ≤ ι p0 := by
      rw [← map_one ι]; exact ι_le_ι.mpr (pos_iff_one_le.mp hp0)
    have hB1 : (1 : DiffRing V) ≤ ι Bn := by
      rw [← map_one ι]; exact ι_le_ι.mpr (pos_iff_one_le.mp hBn0)
    have hcc : 2 * (ι cn : DiffRing V) ≤ ι cn * ι cn :=
      mul_le_mul_of_nonneg_right hc2 (by linarith)
    have h1 : (ι cn : DiffRing V) * ι cn * 1 ≤ ι cn * ι cn * ι rn :=
      mul_le_mul_of_nonneg_left hr1 (mul_nonneg (ι_nonneg _) (ι_nonneg _))
    have h2 : (ι cn : DiffRing V) * ι cn * ι rn * 1 ≤ ι cn * ι cn * ι rn * ι p0 :=
      mul_le_mul_of_nonneg_left hp1
        (mul_nonneg (mul_nonneg (ι_nonneg _) (ι_nonneg _)) (ι_nonneg _))
    have h3 : (ι cn : DiffRing V) * ι cn * ι rn * ι p0 * 1 ≤
        ι cn * ι cn * ι rn * ι p0 * ι Bn :=
      mul_le_mul_of_nonneg_left hB1
        (mul_nonneg (mul_nonneg (mul_nonneg (ι_nonneg _) (ι_nonneg _)) (ι_nonneg _))
          (ι_nonneg _))
    have h4 : (ι Bn : DiffRing V) * ι rn * ι cn * ι cn * ι p0 =
        ι cn * ι cn * ι rn * ι p0 * ι Bn := by ring
    linarith
  have hrank : (ι cn : DiffRing V) ∣ P137Roots.bOff p x - ι Rn ∨
      (ι cn : DiffRing V) ∣ P137Roots.bOff p x + ι Rn := by
    right
    have h8 : (ι cn : DiffRing V) ∣ x 8 := by
      rcases eq_or_eq_neg_abs (x 8) with h | h <;> rw [hcn] at h
      · exact ⟨1, by rw [mul_one]; exact h⟩
      · exact ⟨-1, by rw [mul_neg_one]; exact h⟩
    obtain ⟨u, hu⟩ := h8
    refine ⟨u + 4 * (𝓕).A * x 4 * x 8 * u * (𝓑).BP * x 7, ?_⟩
    unfold P137Roots.bOff
    rw [← hRn, U_eq]
    linear_combination (1 + 4 * (𝓕).A * x 4 * x 8 * (𝓑).BP * x 7) * hu
  obtain ⟨hodd, hcy, hmain⟩ := ZRowsStrongFold.strong_fold (Bn - 2) I0 f cn y Rn (x 8)
    (𝓑).Q (𝓑).V (P137Roots.bOff p x) hdb hf hI0pos hstrong hQJ hV haux hcn hcn0 hcdvd hcI
    hRpos h2R hrank
  have hDmF : (𝓕).Dm = ι (xcoord Rn (Bn - 2)) * ι (xcoord Rn (Bn - 2)) := by
    rw [Dm_eq, hDelta]; exact hmain
  -- the first norm is a square
  have hDm0 : (𝓕).Dm ≠ 0 :=
    (lt_of_lt_of_le zero_lt_one (P137Bootstrap.Dm_ge p x hp)).ne'
  obtain ⟨t, ht⟩ := dvd_of_sq_dvd_sq_ring (A := (ι p0 : DiffRing V))
    (B := ι (xcoord Rn (Bn - 2))) ⟨(𝓑).P, by rw [← hBP, ← hDmF, BP_def]; ring⟩
  have hPsq : (𝓑).P = t * t := by
    apply mul_left_cancel₀ hDm0
    have h1 := BP_def p x
    rw [hBP, hDmF, ht] at h1
    rw [hDmF]
    linear_combination -h1
  have hcop : ∃ α β, (𝓕).Dt * α + (1 + (𝓑).D4 * (𝓕).Dt * x 10 ^ 2) * β = 1 :=
    ⟨-((𝓑).D4 * x 10 ^ 2), 1, by ring⟩
  obtain ⟨⟨τ, hτ⟩, _⟩ := abs_squares_of_mul_square hcop ((P_eq p x).symm.trans hPsq)
  obtain ⟨hDt1, _⟩ := P137Bootstrap.Dt_facts p x hp
  rw [abs_of_pos (by linarith)] at hτ
  -- the projector divisibility
  have hHK : (𝓡).H ∣ P138EarlyFold.Kq p 𝔵 (P138Value.kN p 𝔵) ^ 5 := by
    rw [eH, P137Bootstrap.Kq_transfer p x v' hv]
    exact P137Bootstrap.H_dvd_Kq5 p x hp hS
  exact ⟨⟨Bn, cn, Rn, τ, by rw [eA]; exact hBn, hB3, by rw [e8]; exact hcn, hcn0, hB,
    by rw [eDt]; exact hτ, hHK, hRn', hodd, hcy, by rw [eDm]; exact hDmF, hRpos⟩⟩

end Regs

/-- **Soundness of the 648/115 equation.** A zero in the difference ring of any model of `𝗜𝚺₁`
gives an internal halt of machine 215. -/
theorem sound (x : Fin 11 → DiffRing V) (hz : value portsR x = 0) :
    ∃ T : V, ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0 := by
  have hS := P137Roots.S_dvd_Ac portsR x portFacts hz
  obtain ⟨v', hv⟩ := P137Bootstrap.recover portsR x portFacts hS
  obtain ⟨Fd⟩ := folded_of_zero portsR x v' portFacts hz hv
  exact P138Leaf.halt_of_folded _ _ (P138Window.native_modulus portsR _ portFacts) Fd

#print axioms folded_of_zero
#print axioms sound

end DiophantineConsistency.P137Fold
