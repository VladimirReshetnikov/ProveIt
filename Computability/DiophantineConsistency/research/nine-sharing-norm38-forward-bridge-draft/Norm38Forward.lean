import DiophantineConsistency.Norm38Reference
import DiophantineConsistency.ForwardWitness38
import FreshCarrierSpheres

/-! UNCOMPILED DRAFT. Forward construction, static-to-seed reconstruction,
and a conditional source-zero-to-seed-zero theorem. Imports and all proposed
proof scripts remain unchecked. No iPRA endpoint is asserted. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Norm38Forward
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 SharingGateModel Norm38SlotExtraction

/-- The natural constructor preserves the first fourteen input coordinates. -/
theorem forward_prefix {S : Type*} [CommSemiring S]
    (ports : Fin 4 → S) (u : Fin 14 → S) (j : Fin 14) :
    SharingForward38.witnessCoordinates ports u
      (Fin.castLE (by decide : 14 ≤ 38) j) = u j := by
  fin_cases j <;> simp [SharingForward38.witnessCoordinates]

/-- Candidate direct verification of all 60 static gate equations for the
generated natural constructor. No source norm hypothesis is used here. -/
theorem forward_gatesHold {S R : Type*} [CommSemiring S] [CommRing R]
    (embed : S →+* R) (ports : Fin 4 → S) (u : Fin 14 → S) :
    NormAssignment38.gatesHold embed ports
      (SharingForward38.witnessCoordinates ports u) := by
  unfold NormAssignment38.gatesHold
  simp only [NormAssignment38.gates, List.mem_cons, forall_eq_or_imp]
  repeat' constructor
  all_goals simp [NormAssignment38.assignment, SharingForward38.witnessCoordinates,
    positiveResidual, negativeResidual, pairCompute, map_add, map_mul]

section Model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The five original unit norms imply the static graph's five targets for
the generated witness, using the separately drafted source-reference theorem. -/
theorem forward_fiveNorms (ports : Fin 4 → V) (u : Fin 14 → V)
    (hu : let d := Carrier65.core (fun j => ι (ports j)) (fun j => ι (u j + 1))
      d.P=1 ∧ d.Q=1 ∧ d.U=1 ∧ Carrier65.strong d=1 ∧ d.W=1) :
    NormAssignment38.fiveNorms ι ports
      (SharingForward38.witnessCoordinates ports u) := by
  let w := SharingForward38.witnessCoordinates ports u
  have hg : NormAssignment38.gatesHold ι ports w := forward_gatesHold ι ports u
  have ht := Norm38Reference.static_terminals_agree ports w hg
  simp only [w, forward_prefix] at ht
  have hc := Norm38Reference.reference_terminal_fields (fun j => ι (ports j))
    (fun j => ι (u j + 1))
  have hscale := Carrier65.strong_scale (fun j => ι (ports j)) (fun j => ι (u j + 1))
  rcases ht with ⟨ht0,ht1,hta,htt,hts,htd⟩
  rcases hc with ⟨hc0,hc1,hca,hct,hcs,hcd⟩
  rcases hu with ⟨hP,hQ,hU,hStrong,hW⟩
  have hZ : (Carrier65.core (fun j => ι (ports j)) (fun j => ι (u j + 1))).Z =
      (Carrier65.core (fun j => ι (ports j)) (fun j => ι (u j + 1))).delta := by
    rw [hscale,hStrong,mul_one]
  unfold NormAssignment38.fiveNorms
  exact ⟨ht0.trans (hc0.trans hP), ht1.trans (hc1.trans hQ),
    hta.trans (hca.trans hU), htt.trans (hct.trans hW),
    hts.trans (hcs.trans (hZ.trans (hcd.symm.trans htd.symm)))⟩

/-- Candidate reverse use of the literal slot identities: all static gate and
norm constraints make every squared residual zero. -/
theorem static_implies_seed_zero (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j))
    (hg : NormAssignment38.gatesHold ι ports w)
    (hn : NormAssignment38.fiveNorms ι ports w) :
    InternalZero (SharingSeed38.seed p) (Fin.cons (1 : V) w) := by
  unfold NormAssignment38.gatesHold at hg
  unfold NormAssignment38.fiveNorms at hn
  rcases hn with ⟨hn0,hn1,hna,hnt,hns⟩
  have gate_23 := hg ⟨23, 22, 22, GateOp.mul⟩ (by simp [NormAssignment38.gates])
  have gate_24 := hg ⟨24, 23, 22, GateOp.mul⟩ (by simp [NormAssignment38.gates])
  have gate_25 := hg ⟨25, 8, 22, GateOp.mul⟩ (by simp [NormAssignment38.gates])
  have gate_26 := hg ⟨26, 7, 24, GateOp.mul⟩ (by simp [NormAssignment38.gates])
  have gate_27 := hg ⟨27, 25, 26, GateOp.mul⟩ (by simp [NormAssignment38.gates])
  have gate_29 := hg ⟨29, 28, 26, GateOp.mul⟩ (by simp [NormAssignment38.gates])
  have gate_30 := hg ⟨30, 27, 29, GateOp.mul⟩ (by simp [NormAssignment38.gates])
  have gate_36 := hg ⟨36, 35, 34, GateOp.add⟩ (by simp [NormAssignment38.gates])
  have gate_40 := hg ⟨40, 38, 39, GateOp.add⟩ (by simp [NormAssignment38.gates])
  have gate_41 := hg ⟨41, 31, 31, GateOp.mul⟩ (by simp [NormAssignment38.gates])
  have gate_42 := hg ⟨42, 36, 41, GateOp.mul⟩ (by simp [NormAssignment38.gates])
  have gate_48 := hg ⟨48, 47, 2, GateOp.add⟩ (by simp [NormAssignment38.gates])
  have gate_57 := hg ⟨57, 56, 54, GateOp.sub⟩ (by simp [NormAssignment38.gates])
  have gate_67 := hg ⟨67, 4, 4, GateOp.mul⟩ (by simp [NormAssignment38.gates])
  have gate_69 := hg ⟨69, 68, 54, GateOp.sub⟩ (by simp [NormAssignment38.gates])
  have gate_71 := hg ⟨71, 70, 31, GateOp.sub⟩ (by simp [NormAssignment38.gates])
  have gate_72 := hg ⟨72, 5, 42, GateOp.mul⟩ (by simp [NormAssignment38.gates])
  have gate_73 := hg ⟨73, 72, 72, GateOp.mul⟩ (by simp [NormAssignment38.gates])
  have gate_76 := hg ⟨76, 74, 75, GateOp.sub⟩ (by simp [NormAssignment38.gates])
  have hz00 : InternalZero (residualAt p 0) (Fin.cons (1 : V) w) := by
    rw [internalZero_iff, slot00 p ports w hp]
    exact gate_23.1
  have hz01 : InternalZero (residualAt p 1) (Fin.cons (1 : V) w) := by
    rw [internalZero_iff, slot01 p ports w hp]
    exact gate_24.1
  have hz02 : InternalZero (residualAt p 2) (Fin.cons (1 : V) w) := by
    rw [internalZero_iff, slot02 p ports w hp]
    exact gate_25.1
  have hz03 : InternalZero (residualAt p 3) (Fin.cons (1 : V) w) := by
    rw [internalZero_iff, slot03 p ports w hp]
    exact gate_26.1
  have hz04 : InternalZero (residualAt p 4) (Fin.cons (1 : V) w) := by
    rw [internalZero_iff, slot04 p ports w hp]
    exact gate_27.1
  have hz05 : InternalZero (residualAt p 5) (Fin.cons (1 : V) w) := by
    rw [internalZero_iff, slot05 p ports w hp]
    exact gate_29.1
  have hz06 : InternalZero (residualAt p 6) (Fin.cons (1 : V) w) := by
    rw [internalZero_iff, slot06 p ports w hp]
    exact gate_30.1
  have hz07 : InternalZero (residualAt p 7) (Fin.cons (1 : V) w) := by
    rw [internalZero_iff, slot07 p ports w hp]
    exact gate_36.1
  have hz08 : InternalZero (residualAt p 8) (Fin.cons (1 : V) w) := by
    rw [internalZero_iff, slot08 p ports w hp]
    exact gate_40.1
  have hz09 : InternalZero (residualAt p 9) (Fin.cons (1 : V) w) := by
    rw [internalZero_iff, slot09 p ports w hp]
    exact gate_41.1
  have hz10 : InternalZero (residualAt p 10) (Fin.cons (1 : V) w) := by
    rw [internalZero_iff, slot10 p ports w hp]
    exact gate_42.1
  have hz11 : InternalZero (residualAt p 11) (Fin.cons (1 : V) w) := by
    rw [internalZero_iff, slot11 p ports w hp]
    exact sub_eq_zero.mpr hn1
  have hz12 : InternalZero (residualAt p 12) (Fin.cons (1 : V) w) := by
    rw [internalZero_iff, slot12 p ports w hp]
    exact gate_48.1
  have hz13 : InternalZero (residualAt p 13) (Fin.cons (1 : V) w) := by
    rw [internalZero_iff, slot13 p ports w hp]
    exact gate_48.2
  have hz14 : InternalZero (residualAt p 14) (Fin.cons (1 : V) w) := by
    rw [internalZero_iff, slot14 p ports w hp]
    exact gate_57.1
  have hz15 : InternalZero (residualAt p 15) (Fin.cons (1 : V) w) := by
    rw [internalZero_iff, slot15 p ports w hp]
    exact gate_57.2
  have hz16 : InternalZero (residualAt p 16) (Fin.cons (1 : V) w) := by
    rw [internalZero_iff, slot16 p ports w hp]
    exact sub_eq_zero.mpr hn0
  have hz17 : InternalZero (residualAt p 17) (Fin.cons (1 : V) w) := by
    rw [internalZero_iff, slot17 p ports w hp]
    exact sub_eq_zero.mpr hnt
  have hz18 : InternalZero (residualAt p 18) (Fin.cons (1 : V) w) := by
    rw [internalZero_iff, slot18 p ports w hp]
    exact gate_67.1
  have hz19 : InternalZero (residualAt p 19) (Fin.cons (1 : V) w) := by
    rw [internalZero_iff, slot19 p ports w hp]
    exact gate_69.1
  have hz20 : InternalZero (residualAt p 20) (Fin.cons (1 : V) w) := by
    rw [internalZero_iff, slot20 p ports w hp]
    exact gate_69.2
  have hz21 : InternalZero (residualAt p 21) (Fin.cons (1 : V) w) := by
    rw [internalZero_iff, slot21 p ports w hp]
    exact gate_71.1
  have hz22 : InternalZero (residualAt p 22) (Fin.cons (1 : V) w) := by
    rw [internalZero_iff, slot22 p ports w hp]
    exact gate_71.2
  have hz23 : InternalZero (residualAt p 23) (Fin.cons (1 : V) w) := by
    rw [internalZero_iff, slot23 p ports w hp]
    exact gate_72.1
  have hz24 : InternalZero (residualAt p 24) (Fin.cons (1 : V) w) := by
    rw [internalZero_iff, slot24 p ports w hp]
    exact gate_73.1
  have hz25 : InternalZero (residualAt p 25) (Fin.cons (1 : V) w) := by
    rw [internalZero_iff, slot25 p ports w hp]
    exact gate_76.1
  have hz26 : InternalZero (residualAt p 26) (Fin.cons (1 : V) w) := by
    rw [internalZero_iff, slot26 p ports w hp]
    exact gate_76.2
  have hz27 : InternalZero (residualAt p 27) (Fin.cons (1 : V) w) := by
    rw [internalZero_iff, slot27 p ports w hp]
    exact sub_eq_zero.mpr hna
  have hz28 : InternalZero (residualAt p 28) (Fin.cons (1 : V) w) := by
    rw [internalZero_iff, slot28 p ports w hp]
    exact sub_eq_zero.mpr hns
  have all (i : Fin 29) : InternalZero (residualAt p i) (Fin.cons (1 : V) w) := by
    fin_cases i <;> assumption
  apply (SharingNormSquares.seed_zero_iff_residuals p (Fin.cons (1 : V) w)).mpr
  intro e he
  obtain ⟨j,hj⟩ := List.get_of_mem he
  let i : Fin 29 := ⟨j.val, by simpa [residuals, SharingSeed38.remainingResiduals] using j.isLt⟩
  have hi := all i
  simpa [residualAt, residuals, hj] using hi

/-- Conditional forward bridge: actual source zero supplies the five norms,
and the generated natural witness gives a literal seed zero. -/
theorem source_zero_implies_seed_zero (p : Fin 4 → ℤ) (ports : Fin 4 → V)
    (u : Fin 14 → V) (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j))
    (hb : (0 : DiffRing V) < ((p 0 : ℤ) : DiffRing V))
    (hs : InternalZero (ObjectCurrentEquation2011.expressionAt p) (fun j => u j+1)) :
    InternalZero (SharingSeed38.seed p)
      (Fin.cons (1 : V) (SharingForward38.witnessCoordinates ports u)) := by
  have hvalue : Carrier65.value (fun j => ι (ports j)) (fun j => ι (u j+1)) = 0 := by
    rw [internalZero_iff, FreshModel106.evalRing_expressionAt65] at hs
    simpa only [hp] using hs
  have hbeta : (0 : DiffRing V) < ι (ports 0) := by simpa only [hp] using hb
  have hpositive : ∀ j, (0 : DiffRing V) < ι (u j+1) := fun j =>
    ι_pos (lt_of_lt_of_le _root_.zero_lt_one le_add_self)
  have hnorm := (FreshCarrierSpheres.value65_zero_iff_norms FreshCarrierSpheres.modelFacts
    (fun j => ι (ports j)) (fun j => ι (u j+1)) hbeta hpositive).mp hvalue
  exact static_implies_seed_zero p ports _ hp (forward_gatesHold ι ports u)
    (forward_fiveNorms ports u hnorm)
end Model
-- Still required: Lean checks, actual fixed-port cast proofs, reverse
-- combination, Jones instantiation and the iPRA consistency endpoint.
end DiophantineConsistency.Norm38Forward
