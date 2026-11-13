import DiophantineConsistency.P113.P113Chain
import DiophantineConsistency.P113.P113Fold
import DiophantineConsistency.P138.P138Leaf

/-! # Soundness of package 113: a zero gives the leaf facts, hence a halt

`leaf_of_foldedW` is `P138Leaf.leaf_of_folded` over the weak-window record
`P113Chain.FoldedW`: the same twelve positive coordinates
`![J, F, α, 1, 1, X, Y, 1, η, ζ, 1, 1]` of `CompactLeafFacts.LeafFacts Source34Ports.ports`. The
one change is `η > 0`: package 138 proves it from the ½-window by the sharpened half-binomial
(`P138HalfBinomial.eta_pos`); package 113 has the guard `η ζ > 0` instead, and with `k > 0` it
gives `η > 0` and `ζ > 0` at once (`P113Chain.eta_zeta_pos`).

Package 113's zero gives `P113Fold.Folded113`, which is `FoldedW` at the front
`front x` and the `k` slot `kk portsR x` (`foldedW_of_113`), with the index modulus
`P113Fold.index_modulus`; so `sound` gives an internal halt of machine 215 through
`Source34Converse.halt_iff_facts`. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.P113Leaf
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing ZRowsCoprimeSquares P138Value P138Ports P138Bootstrap P138NoRoot
  P138Squares P138Budget P138Adjacent P138Window P138EarlyFold P138Rank P138FirstIndex P138Ratio
  P138Projector P138Orientation P138Leaf P113Chain
open ArithmeticPellRecurrence
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC

attribute [local irreducible] Source34Ports.betaNat Source34Ports.lowNat Source34Ports.highNat
  Source34Kernel.paramKernel Mixed121Kernel.rho coneA coneB

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

section Zero
variable (x : Fin 11 → DiffRing V) (κ : DiffRing V)
local notation "𝓡" => regsK (portsR (V := V)) x κ

set_option maxHeartbeats 4000000 in
/-- **The leaf facts from the weak-window folded front**, at any `k` slot with an index
modulus. -/
theorem leaf_of_foldedW (hκ : IndexModulus portsR x κ) (Fd : FoldedW (portsR (V := V)) x κ) :
    ∃ v : Fin 12 → V, (∀ j, 0 < v j) ∧ CompactLeafFacts.LeafFacts Source34Ports.ports v := by
  have hp : PortFacts (portsR (V := V)) := portFacts
  obtain ⟨Fi⟩ := first_indexW portsR x κ hp hκ Fd
  obtain ⟨O⟩ := orientedW portsR x κ hp Fd Fi
  obtain ⟨t, ht⟩ := P72ConvArith.odd_of_mod_two Fd.hodd
  have hn : Fi.n = t + 1 := by
    have h := Fi.hn; rw [ht] at h
    apply ι_injective
    have h' := congrArg (ι (V := V)) h
    simp only [map_add, map_mul, map_ofNat, map_one] at h' ⊢
    linarith
  have hs := Fd.hs
  -- the natural coordinates
  obtain ⟨Jn, hJn0, hJn⟩ := natural O.hJ
  obtain ⟨Fn, hFn0, hFn⟩ := natural O.hF
  obtain ⟨Cn, hCn0, hCn⟩ := natural O.hC
  obtain ⟨αn, hαn0, hαn⟩ := natural O.hα
  obtain ⟨Yn, hYn0, hYn⟩ := natural O.hY
  obtain ⟨Wn, hWn0, hWn⟩ := natural (show 0 < (𝓡).W from
    (pos_iff_pos_of_mul_pos (show 0 < (𝓡).q * (𝓡).W by rw [← X_def, O.hX]; exact ι_pos (exp_pos _))).mp O.hq)
  set Xn : V := Exp.exp Fd.Rn with hXn
  have hXd : (𝓡).X = ι Xn := O.hX
  -- the first base
  obtain ⟨⟨ln, hln, hbF⟩, hk0⟩ := Fi.hpos (by rw [hXd]; exact ι_pos (exp_pos _))
  have hlnXY : ln = Xn * Yn * Yn := by
    apply ι_injective; rw [hln, hXd, hYn]; simp only [map_mul]; ring
  rw [hlnXY] at hbF
  set kk : V := 2 * ycoord Fi.n Fi.bF with hkk
  have hkd : (𝓡).k = ι kk := by rw [← Fi.hk, abs_of_pos hk0]
  -- the main base `b = XY + Y`
  have hb : Fd.Bn - 2 = Xn * Yn + Yn := by
    apply ι_injective
    rw [ι_tsub' (le_trans (by norm_num) Fd.hB3), map_ofNat, ← O.hA, A_eq, a_eq, hXd, hYn]
    simp only [map_add, map_mul]; ring
  have hcmain : Fd.cn = ycoord Fd.Rn (Xn * Yn + Yn) := by rw [Fd.hc, hb]
  have ht12 : (12 : V) ≤ t := by
    apply ι_le_ι.mp
    have h4 : (4080 : DiffRing V) ≤ ι Fd.Rn := by
      have := R_ge portsR x κ hp hs; rwa [Fd.hR] at this
    rw [ht] at h4; simp only [map_add, map_mul, map_ofNat, map_one] at h4; rw [map_ofNat]
    linarith
  have ht5 : (5 : V) ≤ t := le_trans (by norm_num) ht12
  -- `η > 0`, `ζ > 0` from the guard
  obtain ⟨hetap, hzeta⟩ := eta_zeta_pos portsR x κ Fd hk0
  obtain ⟨ηn, hηn0, hηn⟩ := natural hetap
  obtain ⟨ζn, hζn0, hζn⟩ := natural hzeta
  -- the ports
  set β : V := ((Source34Ports.ports 0 : ℕ) : V)
  set K0 : V := ((Source34Ports.ports 1 : ℕ) : V)
  set MC : V := ((Source34Ports.ports 2 : ℕ) : V)
  set MF : V := ((Source34Ports.ports 3 : ℕ) : V)
  set p0R : DiffRing V := portsR (V := V) 0 with hp0R
  have hp0 : p0R = ι β := port0
  have hp1 : portsR (V := V) 1 = ι K0 := port1
  have hp2 : portsR (V := V) 2 = ι MC := port2
  have hp3 : portsR (V := V) 3 = ι MF := port3
  have hJb : (𝓡).J * p0R = (𝓡).q - 1 := by rw [mul_comm]; exact beta_J portsR x κ
  set qV : V := 1 + Jn * β with hqVdef
  have hqV : (ι qV : DiffRing V) = (𝓡).q := by
    rw [hqVdef]; simp only [map_add, map_mul, map_one]; rw [← hJn, ← hp0, hJb]; ring
  have hq1 : 1 ≤ qV := le_add_of_nonneg_right (by simp)
  have hFq : Fn ≤ qV := by
    apply ι_le_ι.mp; rw [hqV, ← hFn]; have := O.hα; have := O.hC; linarith
  have hq2 : 1 ≤ qV ^ 2 := one_le_pow₀ hq1
  have hRV : ((qV - 1) * (qV - Fn) + αn) * (qV ^ 2 - 1) + (MC + qV * MF) * Jn = Fd.Rn := by
    apply ι_injective
    have e1 : (ι (qV - 1) : DiffRing V) = (𝓡).q - 1 := by rw [ι_tsub' hq1, map_one, hqV]
    have e2 : (ι (qV - Fn) : DiffRing V) = (𝓡).q - (𝓡).F := by rw [ι_tsub' hFq, hqV, ← hFn]
    have e3 : (ι (qV ^ 2 - 1) : DiffRing V) = (𝓡).q ^ 2 - 1 := by
      rw [ι_tsub' hq2, map_one, map_pow, hqV]
    simp only [map_add, map_mul]
    rw [e1, e2, e3, hqV, ← hαn, ← hJn, ← hp2, ← hp3, ← Fd.hR, R_eq]
    ring
  -- the valuation
  refine ⟨![Jn, Fn, αn, 1, 1, Xn, Yn, 1, ηn, ζn, 1, 1], ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [hJn0, hFn0, hαn0, hYn0, hηn0, hζn0, hXn]
  constructor
  · -- indices
    intro _ _ _
    show ∃ first main j pi : V, 0 < first ∧ 0 < main ∧ 13 ≤ j ∧ j < pi ∧
      pi = ((qV - 1) * (qV - Fn) + αn) * (qV ^ 2 - 1) +
        (MC + qV * MF) * Jn ∧
      2 * j = ((qV - 1) * (qV - Fn) + αn) * (qV ^ 2 - 1) +
        (MC + qV * MF) * Jn + 1 ∧
      xcoord j (2 * ((Xn * Yn) * Yn - 1) + 1) = first ∧
      2 * ycoord j (2 * ((Xn * Yn) * Yn - 1) + 1) = ηn + ζn ∧
      xcoord pi (Xn * Yn + Yn) = main ∧ ycoord pi (Xn * Yn + Yn) = ηn + Yn * (ηn + ζn)
    rw [hRV]
    refine ⟨xcoord Fi.n Fi.bF, xcoord Fd.Rn (Xn * Yn + Yn), Fi.n, Fd.Rn,
      lt_of_lt_of_le (by simp) (one_le_x _ _), lt_of_lt_of_le (by simp) (one_le_x _ _),
      ?_, ?_, rfl, Fi.hn, by rw [hbF], ?_, rfl, ?_⟩
    · rw [hn]
      apply ι_le_ι.mp; have := ι_le_ι.mpr ht12
      simp only [map_add, map_one, map_ofNat] at this ⊢; linarith
    · rw [hn, ht]
      apply ι_lt_ι.mp; have := ι_le_ι.mpr ht5
      simp only [map_add, map_mul, map_one, map_ofNat] at this ⊢; linarith
    · rw [← hbF]
      apply ι_injective
      rw [map_add, ← hηn, ← hζn, ← hkk, ← hkd]; ring
    · rw [← hcmain]
      apply ι_injective
      simp only [map_add, map_mul]
      rw [← hηn, ← hζn, ← hYn, ← O.hc, eta_eq]; ring
  · -- transport
    intro _
    show 0 < qV - (Fn + αn)
    apply pos_of_ι
    have hle : Fn + αn ≤ qV := by
      apply ι_le_ι.mp; rw [hqV, map_add, ← hFn, ← hαn]; have := O.hC; linarith
    rw [ι_tsub' hle, hqV, map_add, ← hFn, ← hαn]; have := O.hC; linarith
  · -- pairMod
    intro hb0
    show ((Fn + αn) * (Xn + K0 * qV) + Fn * qV) % (Jn * β) =
      (qV * (Xn + K0 * qV)) % (Jn * β)
    have hbpos : 0 < Jn * β := mul_pos hJn0 hb0
    apply mod_eq_of_ι_dvd hbpos
    refine ⟨-(x 2) * (𝓡).q, ?_⟩
    rw [hqVdef]
    simp only [map_add, map_mul, map_one]
    rw [← hJn, ← hp0, ← hFn, ← hαn, ← hp1, ← hXd, hJb, X_def, F_eq]
    ring
  · -- power
    intro _ _ _ _
    show Xn = Exp.exp (((qV - 1) * (qV - Fn) + αn) * (qV ^ 2 - 1) +
        (MC + qV * MF) * Jn)
    rw [hRV, hXn]
  · -- projection
    intro _ _ _
    show qV ∣ 3 * Xn ∧ qV ≤ 3 * Xn
    have hXW : Xn = qV * Wn := by
      apply ι_injective; rw [map_mul, hqV, ← hWn, ← hXd, X_def]
    refine ⟨⟨3 * Wn, by rw [hXW]; ring⟩, ?_⟩
    rw [hXW]
    have : 1 ≤ 3 * Wn := le_trans (pos_iff_one_le.mp hWn0) (le_mul_of_one_le_left (by simp) (by norm_num))
    calc qV = qV * 1 := (mul_one _).symm
      _ ≤ qV * (3 * Wn) := mul_le_mul_of_nonneg_left this (by simp)
      _ = 3 * (qV * Wn) := by ring
  · -- ydiv
    intro _ _
    show qV ^ 3 ∣ Yn
    have hq3 : 0 < (𝓡).q ^ 3 := pow_pos O.hq 3
    have hodd : 0 < 2 * x 5 + 1 := by
      have : 0 < (2 * x 5 + 1) * (𝓡).q ^ 3 := by rw [← Y_eq]; exact O.hY
      exact (pos_iff_pos_of_mul_pos this).mpr hq3
    obtain ⟨on, _, hon⟩ := natural hodd
    refine ⟨on, ?_⟩
    apply ι_injective
    rw [map_mul, map_pow, hqV, ← hon, ← hYn, Y_eq]; ring

/-- **A weak-window folded front gives an internal halt of machine 215.** -/
theorem halt_of_foldedW (hκ : IndexModulus portsR x κ) (Fd : FoldedW (portsR (V := V)) x κ) :
    ∃ T : V, ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0 :=
  (Source34Converse.halt_iff_facts).2 (leaf_of_foldedW x κ hκ Fd)

end Zero

section P113
variable (p : Fin 6 → DiffRing V) (x : Fin 12 → DiffRing V)

/-- Package 113's folded record is the weak-window record of its front. -/
def foldedW_of_113 (Fd : P113Fold.Folded113 p x) :
    FoldedW p (P113Front.front x) (P113Front.kk p x) :=
  ⟨Fd.Bn, Fd.cn, Fd.Rn, Fd.τ, Fd.hBn, Fd.hB3, Fd.hcn, Fd.hcn0, Fd.hs, Fd.hk0, Fd.hlo, Fd.hhi,
    Fd.hcky, Fd.hez, Fd.hDt, Fd.hHK, Fd.hR, Fd.hodd, Fd.hc, Fd.hDm, Fd.hRpos⟩

/-- **Soundness, leaf form, of package 113.** -/
theorem leaf_of_zero (hz : P113Value.value portsR x = 0) :
    ∃ v : Fin 12 → V, (∀ j, 0 < v j) ∧ CompactLeafFacts.LeafFacts Source34Ports.ports v := by
  obtain ⟨Fd⟩ := P113Fold.folded113_of_zero portsR x portFacts hz
  exact leaf_of_foldedW (P113Front.front x) (P113Front.kk portsR x)
    (P113Fold.index_modulus portsR x portFacts) (foldedW_of_113 portsR x Fd)

/-- **Soundness of package 113.** A zero of `P113Value.value` at package 138's ports, in any
model of `𝗜𝚺₁`, gives an internal halt of machine 215. -/
theorem sound (hz : P113Value.value portsR x = 0) :
    ∃ T : V, ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0 :=
  (Source34Converse.halt_iff_facts).2 (leaf_of_zero x hz)

end P113

#print axioms leaf_of_foldedW
#print axioms halt_of_foldedW
#print axioms leaf_of_zero
#print axioms sound

end DiophantineConsistency.P113Leaf
