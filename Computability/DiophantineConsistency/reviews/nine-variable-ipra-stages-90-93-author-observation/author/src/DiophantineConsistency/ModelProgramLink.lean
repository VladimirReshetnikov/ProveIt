import DiophantineConsistency.ModelEnumeratorStep
import DiophantineConsistency.ArithmeticEnumRunPerm222
import DiophantineConsistency.ModelSourceModel

/-! # The program link and `SourceModel`

`DirectEnumerator.boundedRunProgram` iterates `optionStepProgram` from the
standard seed `encodeOption (some initialState)`, and
`DirectEnumerator.program` tests its output for zero. In every model `V` of
`𝗜𝚺₁`:

* the seed is the program code of the machine state `liveValue 0 4 0`
  (`rel_initial`);
* by internal `𝚺₁` induction on time, the program's iterate and the machine
  run `ArithmeticEnumRunPerm222.run` stay related by `StateRel` (`rel_run`),
  one step at a time by `ModelEnumeratorStep.rel_optionStep`;
* related codes vanish together, so the program outputs `1` exactly when the
  machine has halted (`programLink`).

With `ModelSourceModel.sourceModel_of_link` this proves `SourceModel` from the
primitive-recursion case alone (`sourceModel`). -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.ModelProgramLink
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ModelScalarPR ScalarPRCode DirectScalar ModelDirectScalar ModelEnumeratorCantor
  ModelEnumeratorRows ModelEnumeratorStep
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open ArithmeticCommandStepPerm222 ArithmeticEnumStepPerm222 ArithmeticEnumRunPerm222

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

instance liveValue_definable' : 𝚺₁-Function₃[V] (liveValue : V → V → V → V) :=
  live_defined.to_definable

instance stateValue_definable' : 𝚺₁-Function₄[V] (stateValue : V → V → V → V → V) :=
  state_defined.to_definable

/-! ### Code of the iteration and the test, one level deep -/

theorem boundedRunProgram_val : DirectEnumerator.boundedRunProgram.val =
    (iterate DirectEnumerator.optionStepProgram
      (DirectEnumerator.encodeOption (some initialState))).val := rfl

theorem program_val : DirectEnumerator.program.val =
    (ifZero DirectEnumerator.boundedRunProgram (constant 1) Realizes.zero).val := rfl

/-! ### The seed -/

theorem seed_cast :
    ((DirectEnumerator.encodeOption (some initialState) : ℕ) : V) = encV 0 4 0 0 0 0 + 1 := by
  have e : DirectEnumerator.encodeOption (some initialState) =
      Nat.pair 0 (Nat.pair 4 (Nat.pair 0 (Nat.pair 0 (Nat.pair 0 0)))) + 1 := rfl
  rw [e]
  simp only [Nat.cast_add, Nat.cast_one, natCast_pair, Nat.cast_zero, Nat.cast_ofNat, encV]

theorem stateValue_zero : stateValue (0 : V) 0 0 0 = 0 := by
  unfold stateValue
  rw [cantor_zero_zero, cantor_zero_zero, cantor_zero_zero]

theorem rel_initial :
    StateRel (evalV DirectEnumerator.boundedRunProgram.val (0 : V)) (run 0 (liveValue (0 : V) 4 0)) := by
  rw [boundedRunProgram_val, evalV_iterate, iterV_zero, seed_cast, run_zero]
  refine Or.inr ⟨0, 4, 0, 0, 0, 0, rfl, ?_⟩
  rw [stateValue_zero]

theorem boundedRun_succ (t : V) :
    evalV DirectEnumerator.boundedRunProgram.val (t + 1) =
      evalV DirectEnumerator.optionStepProgram.val (evalV DirectEnumerator.boundedRunProgram.val t) := by
  rw [boundedRunProgram_val, evalV_iterate, evalV_iterate, iterV_succ]

/-! ### Internal induction on time -/

/-- Iterated second projections, each with a one-step definability proof. -/
def s2 (n : V) : V := munpair₂ (munpair₂ n)
def s3 (n : V) : V := munpair₂ (s2 n)
def s4 (n : V) : V := munpair₂ (s3 n)
def s5 (n : V) : V := munpair₂ (s4 n)

instance munpair₁_definable : 𝚺₁-Function₁[V] (munpair₁ : V → V) := by
  unfold munpair₁; definability
instance munpair₂_definable : 𝚺₁-Function₁[V] (munpair₂ : V → V) := by
  unfold munpair₂; definability
instance s2_definable : 𝚺₁-Function₁[V] (s2 : V → V) := by unfold s2; definability
instance s3_definable : 𝚺₁-Function₁[V] (s3 : V → V) := by unfold s3; definability
instance s4_definable : 𝚺₁-Function₁[V] (s4 : V → V) := by unfold s4; definability
instance s5_definable : 𝚺₁-Function₁[V] (s5 : V → V) := by unfold s5; definability

/-- Register projections, each a single named definable function. -/
def b2 (n : V) : V := munpair₁ (munpair₂ n)
def a1 (n : V) : V := munpair₁ (s2 n)
def a2 (n : V) : V := munpair₁ (s3 n)
def a3 (n : V) : V := munpair₁ (s4 n)

instance b2_definable : 𝚺₁-Function₁[V] (b2 : V → V) := by unfold b2; definability
instance a1_definable : 𝚺₁-Function₁[V] (a1 : V → V) := by unfold a1; definability
instance a2_definable : 𝚺₁-Function₁[V] (a2 : V → V) := by unfold a2; definability
instance a3_definable : 𝚺₁-Function₁[V] (a3 : V → V) := by unfold a3; definability

/-- The work state of a register tuple. -/
def stOf (n : V) : V := stateValue (a1 n) (a2 n) (a3 n) (s5 n)

instance stOf_definable : 𝚺₁-Function₁[V] (stOf : V → V) := by
  unfold stOf
  exact HierarchySymbol.DefinableFunction₄.comp (F := stateValue)
    (HierarchySymbol.DefinableFunction₁.comp (F := a1) (HierarchySymbol.DefinableFunction.var 0))
    (HierarchySymbol.DefinableFunction₁.comp (F := a2) (HierarchySymbol.DefinableFunction.var 0))
    (HierarchySymbol.DefinableFunction₁.comp (F := a3) (HierarchySymbol.DefinableFunction.var 0))
    (HierarchySymbol.DefinableFunction₁.comp (F := s5) (HierarchySymbol.DefinableFunction.var 0))

/-- The machine state denoted by a pair-coded register tuple. -/
def toM (n : V) : V := liveValue (munpair₁ n) (b2 n) (stOf n)

instance toM_definable : 𝚺₁-Function₁[V] (toM : V → V) := by
  unfold toM
  exact HierarchySymbol.DefinableFunction₃.comp (F := liveValue)
    (HierarchySymbol.DefinableFunction₁.comp (F := munpair₁) (HierarchySymbol.DefinableFunction.var 0))
    (HierarchySymbol.DefinableFunction₁.comp (F := b2) (HierarchySymbol.DefinableFunction.var 0))
    (HierarchySymbol.DefinableFunction₁.comp (F := stOf) (HierarchySymbol.DefinableFunction.var 0))

theorem toM_encV (pl np tw ws d h : V) :
    toM (ModelEnumeratorRows.encV pl np tw ws d h) = liveValue pl np (stateValue tw ws d h) := by
  simp only [toM, stOf, a1, a2, a3, b2, s2, s3, s4, s5, ModelEnumeratorRows.encV, munpair₁_mpair,
    munpair₂_mpair]

theorem encV_unpair (n : V) :
    ModelEnumeratorRows.encV (munpair₁ n) (munpair₁ (munpair₂ n)) (munpair₁ (munpair₂ (munpair₂ n)))
      (munpair₁ (munpair₂ (munpair₂ (munpair₂ n)))) (munpair₁ (munpair₂ (munpair₂ (munpair₂ (munpair₂ n)))))
      (munpair₂ (munpair₂ (munpair₂ (munpair₂ (munpair₂ n))))) = n := by
  simp only [ModelEnumeratorRows.encV, mpair_unpair]

/-- The state relation, with the register tuple read off by projections. -/
theorem stateRel_iff {x m : V} :
    ModelEnumeratorStep.StateRel x m ↔ (x = 0 ∧ m = 0) ∨ (0 < x ∧ m = toM (x - 1)) := by
  constructor
  · rintro (h | ⟨pl, np, tw, ws, d, h, hx, hm⟩)
    · exact Or.inl h
    · refine Or.inr ⟨by rw [hx]; exact lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _), ?_⟩
      rw [hm, hx, add_tsub_cancel_right, toM_encV]
  · rintro (h | ⟨hx, hm⟩)
    · exact Or.inl h
    · refine Or.inr ⟨munpair₁ (x - 1), munpair₁ (munpair₂ (x - 1)),
        munpair₁ (munpair₂ (munpair₂ (x - 1))), munpair₁ (munpair₂ (munpair₂ (munpair₂ (x - 1)))),
        munpair₁ (munpair₂ (munpair₂ (munpair₂ (munpair₂ (x - 1))))),
        munpair₂ (munpair₂ (munpair₂ (munpair₂ (munpair₂ (x - 1))))), ?_, ?_⟩
      · rw [encV_unpair]
        exact (tsub_add_cancel_of_le (pos_iff_one_le.mp hx)).symm
      · rw [hm]; rfl

set_option maxHeartbeats 2000000 in
/-- The time induction for free codes `c`, `o`; its predicate is a
composition of definable functions, with no unbounded register search. -/
theorem rel_run_gen (c o : ScalarPRCode) (s0 : V)
    (h0 : ModelEnumeratorStep.StateRel (evalV c (0 : V)) (run 0 s0))
    (hs : ∀ t : V, evalV c (t + 1) = evalV o (evalV c t))
    (ho : ∀ x m : V, ModelEnumeratorStep.StateRel x m →
      ModelEnumeratorStep.StateRel (evalV o x) (enumValue m)) (t : V) :
    ModelEnumeratorStep.StateRel (evalV c t) (run t s0) := by
  have key : ∀ t : V,
      (evalV c t = 0 ∧ run t s0 = 0) ∨ (0 < evalV c t ∧ run t s0 = toM (evalV c t - 1)) := by
    intro t
    induction t using ISigma1.sigma1_succ_induction
    · -- the predicate, assembled from definable pieces
      have hev : 𝚺₁-Function₁[V] (fun t : V => evalV c t) := inferInstance
      have hrun : 𝚺₁.DefinableFunction (fun v : Fin 1 → V => run (v 0) s0) :=
        HierarchySymbol.DefinableFunction₂.comp (F := run) (HierarchySymbol.DefinableFunction.var 0)
          (HierarchySymbol.DefinableFunction.const s0)
      have hc : 𝚺₁.DefinableFunction (fun v : Fin 1 → V => evalV c (v 0)) :=
        HierarchySymbol.DefinableFunction₁.comp (F := evalV c) (HierarchySymbol.DefinableFunction.var 0)
      have hm : 𝚺₁.DefinableFunction (fun v : Fin 1 → V => toM (evalV c (v 0) - 1)) :=
        HierarchySymbol.DefinableFunction₁.comp (F := toM)
          (HierarchySymbol.DefinableFunction₂.comp (F := (· - ·)) hc
            (HierarchySymbol.DefinableFunction.const 1))
      exact HierarchySymbol.Definable.or
        (HierarchySymbol.Definable.and
          (HierarchySymbol.Definable.comp₂ (P := Eq) hc (HierarchySymbol.DefinableFunction.const 0))
          (HierarchySymbol.Definable.comp₂ (P := Eq) hrun (HierarchySymbol.DefinableFunction.const 0)))
        (HierarchySymbol.Definable.and
          (HierarchySymbol.Definable.comp₂ (P := (· < ·)) (HierarchySymbol.DefinableFunction.const 0) hc)
          (HierarchySymbol.Definable.comp₂ (P := Eq) hrun hm))
    case zero => exact stateRel_iff.mp h0
    case succ t ih =>
      have e := ho _ _ (stateRel_iff.mpr ih)
      rw [← hs t, ← run_succ t s0] at e
      exact stateRel_iff.mp e
  exact stateRel_iff.mpr (key t)

/-- At every internal time the program's iterate and the machine run denote the
same state. -/
theorem rel_run (t : V) :
    StateRel (evalV DirectEnumerator.boundedRunProgram.val t) (run t (liveValue (0 : V) 4 0)) :=
  rel_run_gen _ _ _ rel_initial boundedRun_succ (fun _ _ h => rel_optionStep h) t

/-- Related codes vanish together. -/
theorem rel_zero_iff {x m : V} (hr : StateRel x m) : x = 0 ↔ m = 0 := by
  rcases hr with ⟨hx, hm⟩ | ⟨pl, np, tw, ws, d, h, hx, hm⟩
  · exact ⟨fun _ => hm, fun _ => hx⟩
  · rw [hx, hm]
    exact ⟨fun e => absurd e (succ_ne_zero' _), fun e => absurd e (liveValue_ne_zero _ _ _)⟩

theorem evalV_program_eq_one_iff (t : V) :
    evalV DirectEnumerator.program.val t = 1 ↔ evalV DirectEnumerator.boundedRunProgram.val t = 0 := by
  rw [program_val, evalV_ifZero, evalV_constant, Nat.cast_one, evalV_zeroR]
  by_cases h0 : evalV DirectEnumerator.boundedRunProgram.val t = 0
  · rw [if_pos h0]
    exact ⟨fun _ => h0, fun _ => rfl⟩
  · rw [if_neg h0]
    exact ⟨fun e => absurd e.symm _root_.one_ne_zero, fun e => absurd e h0⟩

/-! ### The link and `SourceModel` -/

/-- **The program link**: in every model of `𝗜𝚺₁`, the literal enumerator
program outputs `1` at some internal input iff the internal C222 machine halts
from `⟨0,4,0,0,0,0⟩`. -/
theorem programLink : ModelSourceModel.ProgramLink := by
  intro V _ _
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, (rel_zero_iff (rel_run t)).mp ((evalV_program_eq_one_iff t).mp ht)⟩
  · rintro ⟨t, ht⟩
    exact ⟨t, (evalV_program_eq_one_iff t).mpr ((rel_zero_iff (rel_run t)).mpr ht)⟩

/-- **`SourceModel`** from the primitive-recursion case of the compiler. -/
theorem sourceModel (hprec : ModelRepBasic.PrecCase) : IPRAExplicitZFCReduction.SourceModel :=
  ModelSourceModel.sourceModel_of_link hprec programLink

end DiophantineConsistency.ModelProgramLink
