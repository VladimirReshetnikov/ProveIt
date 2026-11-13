import DiophantineConsistency.Z10.Z10BridgeSound
import DiophantineConsistency.Z10.Z10Contract

/-! # Ten-integer package 106: soundness

Soundness step S17 of the route, which closes the soundness half: an integer
zero of the equation of package 106 at the wang943-mixed-121x8801 ports gives
an internal halting run of machine 215.

At a zero `x : Fin 10 → DiffRing V` of `Z10Regs.value pR`:

* `Z10Squares.roots` makes the base `b = β²` a positive natural, and
  `Z10Guard.guard` gives `0 < g < cap`, so the low word `g` is a natural;
* `Z10Prefix.prefix_naturals` then makes the rank `X = Xc pR b g` a natural
  `Xn ≥ 8`;
* `Z10BridgeSound.b_pow` gives `b = 2^(2s)` and `Z10BridgeSound.central` gives
  a natural `Yn = Y` with `Yn ∣ C(2 Xn, Xn)`;
* `g = b · x₁` with `x₁ > 0` and `b ≥ 4` gives `4 ∣ g`;
* `Z10Contract.contract` turns the divisibility into a zero of the 22 rows of
  the N101 source system, `N101Contract.source_of_code` into a positive zero
  of the 31-input parent source, and `Source31Facts.halts` into a halt.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.Z10Sound
open Nine121 Nine121.N105Layout Z10Regs
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ModelDifferenceRing ArithmeticBinomPascal
open Nine121.N101Contract (exp_two')
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

attribute [local irreducible] Mixed121Ports.ports

/-- The ports in the ring of differences. -/
local notation "pR" => Source31Facts.portsR (V := V) Mixed121Ports.ports

/-- **Soundness of the ten-integer equation.** An integer zero gives an internal halt of
machine 215. -/
theorem halts (x : Fin 10 → DiffRing V) (hz : value pR x = 0) :
    ∃ T : V, ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0 := by
  -- the base is a positive natural square and the low word is a natural
  obtain ⟨β, _, _, _, hβ, _, _, _, hb, _, _, _⟩ := Z10Squares.roots pR x hz
  obtain ⟨-, hg0, hgcap, -⟩ := Z10Guard.guard pR x hz
  obtain ⟨gn, hgn⟩ := nonneg_iff.mp (le_of_lt hg0)
  have hbn : 0 < β * β := _root_.mul_pos hβ hβ
  have hbι : (regs pR x).b = ι (β * β) := by rw [hb, map_mul]
  -- the rank is a natural
  obtain ⟨Xn, hXn, hX8⟩ := Z10Prefix.prefix_naturals (β * β) gn hbn
  have hX : (regs pR x).X = ι Xn := by rw [X_def, hbι, hgn]; exact hXn
  have hX3 : 3 ≤ Xn := le_trans (by norm_num) hX8
  -- the base is a power of four
  obtain ⟨s, hs⟩ := Z10BridgeSound.b_pow pR x hz Xn hX hX3
  have hβs : β * β = Exp.exp (2 * s) := ι_injective (hbι.symm.trans hs)
  rw [hβs] at hXn
  -- the central divisibility
  obtain ⟨Yn, hYn, hdvd⟩ := Z10BridgeSound.central pR x hz Xn hX hX8
  have hY : ι Yn = Yc (ι (Exp.exp (2 * s))) := by rw [← hYn, Y_def, hs]
  -- the low word is below the cap
  have hcp := Z10Guard.cap_pos pR x hz
  rw [cap_def, hs] at hcp hgcap
  rw [hgn] at hgcap
  have hgc : ι gn < 4 * cap (ι (Exp.exp (2 * s))) := by linarith
  -- the low word is a multiple of four
  obtain ⟨hx1, -, -, -⟩ := Z10BridgeSound.signs pR x hz Xn hX hX3
  obtain ⟨x1n, hx1n⟩ := nonneg_iff.mp (le_of_lt hx1)
  have hgx : gn = Exp.exp (2 * s) * x1n := by
    apply ι_injective
    rw [map_mul, ← hgn, ← hs, ← hx1n]
    exact g_def pR x
  have h4V : (4 : V) ≤ Exp.exp (2 * s) := by
    have h := Z10Index.b_ge pR x hz
    rw [hs, ← map_ofNat (ι : V →+* DiffRing V) 4] at h
    exact ι_le_ι.mp h
  have h2s : (2 : V) ≤ 2 * s := by
    rw [← exp_two'] at h4V
    exact exp_monotone_le.mp h4V
  have h4e : (4 : V) ∣ Exp.exp (2 * s) := by
    refine ⟨Exp.exp (2 * s - 2), ?_⟩
    rw [← exp_two', ← exp_add, add_tsub_cancel_of_le h2s]
  have h4 : (4 : V) ∣ gn := by
    rw [hgx]
    exact Dvd.dvd.mul_right h4e _
  -- the contract, the parent source and the halt
  obtain ⟨z, -, -, hrows⟩ :=
    (Z10Contract.contract (2 * s) gn Xn Yn hgc h4 hXn.symm hY).mp hdvd
  obtain ⟨y, hy, hyz⟩ := Nine121.N101Contract.source_of_code z hrows
  exact Source31Facts.halts y hy hyz

#print axioms halts

end DiophantineConsistency.Z10Sound
