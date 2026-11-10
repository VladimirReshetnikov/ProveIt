import DiophantineConsistency.P125.P125Roots
import DiophantineConsistency.P138.P138Leaf

/-! # Soundness of package 125's 488/118 and 464/119 equations

A zero of the three-root output `P125Value.outK p x κ ζ`, at a `k` slot `κ` with an index
modulus (`P138Window.IndexModulus`) and a norm slot `ζ` with `S ∣ ζ + Ac`, gives the folded
front `P138Rank.Folded p x κ` of package 138. From there the soundness chain of package 138
(first index, ratio, projector, orientation, leaf) applies unchanged:
`P138Leaf.halt_of_folded`.

The fields of the record, and where they come from:

* `Budget > 0` and `Dt = τ²`: `P125Roots.guard`.
* `H ∣ Kq⁵`: from `S ∣ Ac` (`P125Roots.S_dvd_Ac`, `P138EarlyFold.H_dvd_Kq5_of_S_dvd`).
* the main Pell pair `|c| = ψ_b(R)`, `R` odd, `Dm = χ_b(R)²`: `ZRowsStrongFold.strong_fold`,
  with the strong pair `f² = 1 + δ_b I₀²`, `I₀ = |r| c²` (`P125Roots.Df_root`, `I = r c²`),
  `Q = (δ_b I₀)²`, the linear slot `V = f² · bOff − c`, `bOff = c − R + 4 I T`, and the
  adjacent equation of `P125Roots.descent`. The rank hypothesis is
  `bOff + R = c (1 + 4 r c T) ≡ 0 (mod |c|)`; the size hypotheses `0 < 2R < |c|` are those of
  package 138 (`P138Budget.c_interval`, `P138Window.window`, `P138Window.k_ge`).

`sound_direct` and `sound_centered` are the statements at the native index `k = 1 + R + h E`
for the two norm slots `ζ = S n − Ac` (118 operations, degree 488) and `ζ = S (n + Q V) − Ac`
(119 operations, degree 464). -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.P125Fold
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing ZRowsCoprimeSquares P138Value P138Ports P138Bootstrap P138Adjacent
  P138Window P138EarlyFold P138Rank
open P125Value (back tail outK)
open ArithmeticPellRecurrence ArithmeticPellHalfIndex
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC

attribute [local irreducible] Source34Ports.betaNat Source34Ports.lowNat Source34Ports.highNat
  Source34Kernel.paramKernel Mixed121Kernel.rho coneA coneB

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

section Regs
variable (p : Fin 6 → DiffRing V) (x : Fin 11 → DiffRing V) (κ ζ : DiffRing V)
local notation "𝓡" => regsK p x κ
local notation "𝓑" => back p x κ

set_option maxHeartbeats 2000000 in
/-- **A zero of the three-root output gives the folded front of package 138.** -/
theorem folded_of_zero (hp : PortFacts p) (hκ : IndexModulus p x κ)
    (hz : outK p x κ ζ = 0) (hζ : (𝓡).S ∣ ζ + (𝓡).Ac) : Nonempty (Folded p x κ) := by
  obtain ⟨⟨τ, hDt⟩, hB⟩ := P125Roots.guard p x κ ζ hp hz hζ
  obtain ⟨f, hf, hDf⟩ := P125Roots.Df_root p x κ ζ hp hz hζ
  obtain ⟨y, _, haux⟩ := P125Roots.descent p x κ ζ hp hz hζ
  have hS := P125Roots.S_dvd_Ac p x κ ζ hp hz hζ
  obtain ⟨_, hr⟩ := P125Roots.s_r_ne p x κ ζ hz hζ
  have hc := P138Budget.c_ne p x κ hp hB
  -- the base
  obtain ⟨Bn, hBn⟩ := abs_eq_ι (𝓡).A
  have hB3 : 3 ≤ Bn := by
    have h := abs_A p x κ hp
    rw [hBn, show (3 : DiffRing V) = ι 3 by rw [map_ofNat]] at h
    exact ι_le_ι.mp h
  obtain ⟨hD, hdb⟩ := ZRowsStrongFold.delta_of_abs hBn hB3
  have hDelta : (𝓡).Delta = ι (delta (Bn - 2)) := by rw [Delta_eq]; exact hD
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
  obtain ⟨I0, hI0⟩ : ∃ I0 : V, I0 = rn * cn * cn := ⟨_, rfl⟩
  have hI2 : (𝓑).I ^ 2 = (ι rn * ι cn ^ 2) ^ 2 := by
    rw [P125Value.I_eq, ← sq_abs, abs_mul, abs_pow, hrn, hcn]
  have hstrong : f * f = 1 + delta (Bn - 2) * I0 * I0 := by
    apply ι_injective
    rw [hI0]
    simp only [map_mul, map_add, map_one]
    rw [← hDf, P125Value.Df_eq, hDelta, hI2]; ring
  have hI0pos : 0 < I0 := by
    rw [hI0]; exact mul_pos (mul_pos hrn0 hcn0) hcn0
  have hQJ : (𝓑).Q = ι (delta (Bn - 2) * I0) * ι (delta (Bn - 2) * I0) := by
    rw [P125Value.Q_eq, hDelta, hI2, hI0]
    simp only [map_mul]; ring
  obtain ⟨bOff, hbOff⟩ : ∃ t : DiffRing V,
      t = x 8 - (𝓡).R + 4 * (𝓑).I * x 7 := ⟨_, rfl⟩
  have hV : (𝓑).V = ι (f * f) * bOff - x 8 := by
    rw [P125Value.V_eq, hDf, map_mul, hbOff]
  have hcdvd : cn * cn ∣ I0 := ⟨rn, by rw [hI0]; ring⟩
  -- the rank and its size
  have hs := signs_of_budget p x κ hp hB
  obtain ⟨Rn, hRn, hlo, hhi⟩ := window p x κ hp hs
  have hkR := k_ge p x κ hp hκ hs
  have hci := (P138Budget.c_interval p x κ hp hB).1
  have hY3 := three_le_abs_Y p x κ hp
  have hR0 : (0 : DiffRing V) ≤ ι Rn := ι_nonneg _
  have h2R : 2 * Rn < cn := by
    apply ι_lt_ι.mp
    rw [map_mul, map_ofNat, ← hcn]
    have h5 : 5 * ((𝓡).R + 1) ≤ |(𝓡).k| * (2 * |(𝓡).Y| - 1) := by
      have := mul_le_mul hkR (show (5 : DiffRing V) ≤ 2 * |(𝓡).Y| - 1 by linarith)
        (by norm_num) (abs_nonneg _)
      linarith
    rw [hRn] at h5
    linarith
  have hRpos : 0 < Rn := by
    have : (0 : DiffRing V) ≤ |(𝓡).q| * ((𝓡).q ^ 2 - 1) := by
      have := abs_q_ge p x κ hp
      have h64 : (2 : DiffRing V) ≤ 2 ^ 64 := by norm_num
      have : 1 ≤ (𝓡).q ^ 2 := by rw [← sq_abs]; nlinarith
      exact mul_nonneg (abs_nonneg _) (by linarith)
    exact pos_of_ι (by linarith)
  have hcI : cn < I0 := by
    apply ι_lt_ι.mp
    rw [hI0]
    simp only [map_mul]
    have hR1 : (1 : DiffRing V) ≤ ι Rn := by
      rw [← map_one ι]; exact ι_le_ι.mpr (pos_iff_one_le.mp hRpos)
    have h2R' : 2 * (ι Rn : DiffRing V) < ι cn := by
      have := ι_lt_ι.mpr h2R
      rwa [map_mul, map_ofNat] at this
    have hc2 : (2 : DiffRing V) ≤ ι cn := by linarith
    have hr1 : (1 : DiffRing V) ≤ ι rn := by
      rw [← map_one ι]; exact ι_le_ι.mpr (pos_iff_one_le.mp hrn0)
    have hcc : 2 * (ι cn : DiffRing V) ≤ ι cn * ι cn :=
      mul_le_mul_of_nonneg_right hc2 (by linarith)
    have h1 : (ι cn : DiffRing V) * ι cn * 1 ≤ ι cn * ι cn * ι rn :=
      mul_le_mul_of_nonneg_left hr1 (mul_nonneg (ι_nonneg _) (ι_nonneg _))
    have h3 : (ι rn : DiffRing V) * ι cn * ι cn = ι cn * ι cn * ι rn := by ring
    linarith
  have hrank : (ι cn : DiffRing V) ∣ bOff - ι Rn ∨ (ι cn : DiffRing V) ∣ bOff + ι Rn := by
    right
    have h8 : (ι cn : DiffRing V) ∣ x 8 := by
      rcases eq_or_eq_neg_abs (x 8) with h | h <;> rw [hcn] at h
      · exact ⟨1, by rw [mul_one]; exact h⟩
      · exact ⟨-1, by rw [mul_neg_one]; exact h⟩
    obtain ⟨u, hu⟩ := h8
    refine ⟨u + 4 * x 4 * x 8 * u * x 7, ?_⟩
    rw [hbOff, ← hRn, P125Value.I_eq]
    linear_combination (1 + 4 * x 4 * x 8 * x 7) * hu
  obtain ⟨hodd, hcy, hmain⟩ := ZRowsStrongFold.strong_fold (Bn - 2) I0 f cn y Rn (x 8)
    (𝓑).Q (𝓑).V bOff hdb hf hI0pos hstrong hQJ hV haux hcn hcn0 hcdvd hcI hRpos h2R hrank
  have hDm : (𝓡).Dm = ι (xcoord Rn (Bn - 2)) * ι (xcoord Rn (Bn - 2)) := by
    rw [Dm_eq, hDelta]; exact hmain
  exact ⟨⟨Bn, cn, Rn, τ, hBn, hB3, hcn, hcn0, hB, hDt, H_dvd_Kq5_of_S_dvd p x κ hS, hRn, hodd,
    hcy, hDm, hRpos⟩⟩

end Regs

/-- **Soundness of the 488/118 equation** (direct slot). A zero in the difference ring of any
model of `𝗜𝚺₁` gives an internal halt of machine 215. -/
theorem sound_direct (x : Fin 11 → DiffRing V) (hz : P125Value.valueD portsR x = 0) :
    ∃ T : V, ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0 := by
  obtain ⟨Fd⟩ := folded_of_zero portsR x (kN portsR x) (P125Value.zD portsR x (kN portsR x))
    portFacts (native_modulus portsR x portFacts) hz
    (Dvd.intro _ (P125Value.zD_add portsR x (kN portsR x)).symm)
  exact P138Leaf.halt_of_folded x _ (native_modulus portsR x portFacts) Fd

/-- **Soundness of the 464/119 equation** (centered slot). -/
theorem sound_centered (x : Fin 11 → DiffRing V) (hz : P125Value.valueC portsR x = 0) :
    ∃ T : V, ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0 := by
  obtain ⟨Fd⟩ := folded_of_zero portsR x (kN portsR x) (P125Value.zC portsR x (kN portsR x))
    portFacts (native_modulus portsR x portFacts) hz
    (Dvd.intro _ (P125Value.zC_add portsR x (kN portsR x)).symm)
  exact P138Leaf.halt_of_folded x _ (native_modulus portsR x portFacts) Fd

#print axioms folded_of_zero
#print axioms sound_direct
#print axioms sound_centered

end DiophantineConsistency.P125Fold
