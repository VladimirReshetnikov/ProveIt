import DiophantineConsistency.BFS943.Trace104Source
import DiophantineConsistency.BFS943.Trace104HaltGraph
import DiophantineConsistency.BFS943.Trace104Syntax
import DiophantineConsistency.BFS943.FixedSourceHalt
import DiophantineConsistency.BFS943.Trace75FixedBounds
import DiophantineConsistency.Compact44.CompactSymbolicBetaCast
import DiophantineConsistency.Compact44.CompactSymbolicMaskData

/-! # Both model directions of the 104/174 circuit at the BFS943 ports

The literal output is `(3 N + 1) (P0 + 1) - 1` (`TenPositiveTrace104.value104_eq`).

* `unit_split`: in the difference ring a zero forces `N = 0` and `P0 = 0` (the
  two factors are units and `3 N + 1 ≠ -1`).
* Soundness: at `N = 0` the core norm is `H² P0` (`core_norm`), so the first ten
  coordinates are a positive core zero with `K = H κ`; it is a
  `BFS943FixedSource.FixedSource` (`Trace104Source.source_of_fixed_zero`) and
  `FixedSourceHalt.source_halts` gives a halting time of machine 215.
* Completeness: a halting time gives a positive core zero and a positive
  `κ` with `K = H κ` (`Trace104HaltGraph.halt_zero_of_model_ports`); then
  `N = 0`, `H² P0 = 0` with `H ≠ 0` (`K > 0`), and `(J, …, ζ, κ)` is a positive
  zero of the literal. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace Trace104ModelIff
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace104
open CompactFixedBeta CompactSymbolicPorts CompactSymbolicKernel
open CompactConstructedRank DirectBFSFourFieldsPacking
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
attribute [local irreducible] DirectBFSFourFieldsPacking.kernel rho
  DirectBFSSymbolicKernel.paramKernel CompactFixedBeta.betaNat Nat.ofDigits lowNat highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- In the difference ring, `(3 N + 1) (P0 + 1) = 1` forces `N = 0`, `P0 = 0`. -/
theorem unit_split (P0 N : DiffRing V) (h : (3*N+1)*(P0+1)-1=0) : N=0 ∧ P0=0 := by
  have hd : ∀ x : DiffRing V, 0<x → 1≤x := fun x hx =>
    one_le_of_pos (fun z hz => pos_iff_one_le.mp hz) hx
  have hab : (3*N+1)*(P0+1)=1 := by linear_combination h
  have hN : N=0 := by
    rcases lt_trichotomy N 0 with hlt|heq|hgt
    · exfalso
      have h1 : 1≤-N := hd (-N) (by linarith)
      have hb : P0+1<0 := by
        by_contra hn
        have hb0 : 0≤P0+1 := le_of_not_gt hn
        have : (3*N+1)*(P0+1)≤0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hb0
        linarith
      have hb1 : 1≤-(P0+1) := hd _ (by linarith)
      have : 2*1≤(-(3*N+1))*(-(P0+1)) := mul_le_mul (by linarith) hb1 (by norm_num) (by linarith)
      nlinarith
    · exact heq
    · exfalso
      have h1 : 1≤N := hd N hgt
      have hb : 0<P0+1 := by
        by_contra hn
        have hb0 : P0+1≤0 := le_of_not_gt hn
        have : (3*N+1)*(P0+1)≤0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hb0
        linarith
      have hb1 : 1≤P0+1 := hd _ hb
      have : 4*1≤(3*N+1)*(P0+1) := mul_le_mul (by linarith) hb1 (by norm_num) (by linarith)
      linarith
  refine ⟨hN,?_⟩
  rw [hN] at hab
  linear_combination hab

/-- The first ten coordinates of an eleven-coordinate valuation. -/
def coreVal (v : Fin 11 → V) : Fin 10 → V := fun j => v j.castSucc

theorem core_cast (v : Fin 11 → V) :
    core (fun j => (ι (v j):DiffRing V))=fun j => ι (coreVal v j) := rfl

/-- Soundness: a positive literal zero is a positive core zero with `H ∣ K`. -/
theorem core_of_literal (p : Fin 4 → ℕ) (v : Fin 11 → V)
    (hz : value104 (Trace104Factors.ports p) (fun j => ι (v j)) = 0) :
    valueC (Trace104Factors.ports p) (fun j => ι (coreVal v j)) = 0 ∧
      (regs (Trace104Factors.ports p) (fun j => ι (coreVal v j))).H∣
        (regs (Trace104Factors.ports p) (fun j => ι (coreVal v j))).K := by
  rw [value104_eq] at hz
  obtain ⟨hN,hP⟩ := unit_split _ _ hz
  have hc := core_norm (Trace104Factors.ports p) (fun j => ι (v j)) hN
  rw [hP,mul_zero,core_cast] at hc
  refine ⟨hc,⟨ι (v 10),?_⟩⟩
  have h := hN
  simp only [N104] at h
  rw [core_cast] at h
  linear_combination h

/-- The eleven-coordinate valuation `(w, κ)`. -/
def extend (w : Fin 10 → V) (kappa : V) : Fin 11 → V :=
  fun j => if h : j.val<10 then w ⟨j.val,h⟩ else kappa

theorem coreVal_extend (w : Fin 10 → V) (kappa : V) : coreVal (extend w kappa)=w := by
  funext j
  simp [coreVal,extend]

theorem extend_last (w : Fin 10 → V) (kappa : V) : extend w kappa 10=kappa := by
  simp [extend]

theorem extend_pos (w : Fin 10 → V) (kappa : V) (hw : ∀ j,0<w j) (hk : 0<kappa) :
    ∀ j,0<extend w kappa j := by
  intro j
  unfold extend
  split_ifs
  · exact hw _
  · exact hk

theorem positive_model_iff (p : Fin 4 → ℕ)
    (hp0 : p 0 = betaNat) (hp1 : p 1 = DirectBFSSymbolicKernel.paramKernel rho)
    (hp2 : p 2 = lowNat) (hp3 : p 3 = betaNat + highNat) :
    (∃ v : Fin 11 → V, (∀ j, 0 < v j) ∧
        value104 (Trace104Factors.ports p) (fun j => ι (v j)) = 0) ↔
      (∃ T : V, ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0) := by
  have hp0m : (p 0 : V) = Exp.exp (590069 : V) - 1 := by
    rw [hp0]
    exact CompactSymbolicBetaCast.beta_model
  have hp1m : (p 1 : V) = (kernel : V) := by
    unfold DirectBFSFourFieldsPacking.kernel
    exact congrArg (fun k : ℕ => (k : V)) hp1
  have hp2m : (p 2 : V) = low := by
    rw [hp2]
    exact CompactSymbolicMaskData.low_eq
  have hp3m : (p 3 : V) = high + (Exp.exp (590069 : V) - 1) := by
    rw [hp3, Nat.cast_add, CompactSymbolicBetaCast.beta_model]
    have hh : (highNat : V) = high := CompactSymbolicMaskData.high_eq
    rw [hh, add_comm]
  obtain ⟨h31, _hl, _hh⟩ := Trace75FixedBounds.fixed_bounds (V := V) p hp0 hp2 hp3
  have hb : 0 < (p 0 : V) := lt_of_lt_of_le (by norm_num) h31
  constructor
  · rintro ⟨v, hv, hz⟩
    obtain ⟨hzc, hHK⟩ := core_of_literal p v hz
    have hcv : ∀ j, 0 < coreVal v j := fun j => hv _
    exact FixedSourceHalt.source_halts p (Trace104Source.sourceVal p (coreVal v)) hp0 hp1 hp2 hp3
      (Trace104Source.source_pos p (coreVal v) hb hcv)
      (Trace104Source.source_of_fixed_zero p (coreVal v) hp0 hp2 hp3 hcv hzc hHK)
  · rintro ⟨T, hT⟩
    obtain ⟨w, hw, hzc, kappa, hk, hK⟩ :=
      Trace104HaltGraph.halt_zero_of_model_ports p T hT hp0m hp1m hp2m hp3m
    refine ⟨extend w kappa, extend_pos w kappa hw hk, ?_⟩
    have hcore : core (fun j => (ι (extend w kappa j):DiffRing V))=fun j => ι (w j) := by
      rw [core_cast, coreVal_extend]
    have hN : N104 (Trace104Factors.ports p) (fun j => ι (extend w kappa j))=0 := by
      simp only [N104]
      rw [hcore, extend_last, hK]
      ring
    have hnorm := core_norm (Trace104Factors.ports p) (fun j => ι (extend w kappa j)) hN
    rw [hcore, hzc] at hnorm
    have hKpos := Trace104NormKpos.graph_K_positive p w _ hb hw hzc
    have hHne : (regs (Trace104Factors.ports p) (fun j => ι (w j))).H≠0 := by
      intro h0
      rw [hK, h0, zero_mul] at hKpos
      exact lt_irrefl _ hKpos
    have hP : P0 (Trace104Factors.ports p) (fun j => ι (extend w kappa j))=0 := by
      have h2 : (regs (Trace104Factors.ports p) (fun j => ι (w j))).H^2≠0 := pow_ne_zero 2 hHne
      exact (mul_eq_zero.mp hnorm.symm).resolve_left h2
    rw [value104_eq, hN, hP]
    ring

#print axioms Trace104ModelIff.unit_split
#print axioms Trace104ModelIff.positive_model_iff
end Trace104ModelIff
