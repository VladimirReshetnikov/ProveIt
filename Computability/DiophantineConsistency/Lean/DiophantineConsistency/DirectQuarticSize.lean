import DiophantineConsistency.IterationSize
import DiophantineConsistency.BoundedForallDepth
import DiophantineConsistency.DirectQuarticZFC

/-!
# A finite size bound for the closed direct quartic

Only constructor metadata and natural arithmetic are evaluated here. The
exponent in the final bound is a bit-length estimate, not an exact variable
count and not a claim of optimality.
-/

set_option maxRecDepth 10000
set_option exponentiation.threshold 300000

noncomputable section

namespace DiophantineConsistency.DirectQuarticSize

open Rep (Thin)
open SetTheory SetTheory.BusyBeaver.ZFC EnumPerm Code254 KCode222
open DirectEnumerator (encodeOption)

-- Expose a definition as representation data before applying a scalar fold.
-- The emitted equality is checked by the kernel at the whole-Rep type.
open Lean Elab Term in
local elab "definitionBody% " id:ident : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo id
  let .defnInfo info ← getConstInfo n | throwError "expected a definition"
  unless info.levelParams.isEmpty do throwError "expected a closed monomorphic definition"
  return info.value
open NativeEnumerationSize (allowance)

attribute [local irreducible] NativeZFC.representation Nat.unpair Rep.depth Expr.depth Expr.splitSize

local notation "transition" =>
  (IterationSize.transition (f := DirectEnumerator.optionStep) NativeGraphEnumerator.optionStepProgram)
local notation "bounded" => (Rep.boundedForall transition (Sum.inl (some 0)))


private theorem bounded_depth_arithmetic (m d q : ℕ) (hm : m = 1782) (hd : d ≤ 11204)
    (hq : q ≤ 2 * m + max 16384 (12 * d + 1) + 96) : q ≤ 138109 := by omega

theorem bounded_depth : (bounded).depth ≤ 138109 :=
  bounded_depth_arithmetic _ _ _ IterationSize.native_transition_witnessCount
    IterationSize.native_transition_depth
    (BoundedForallDepth.boundedForall_depth_le transition (Sum.inl (some 0)))

theorem first_depth (initial : ℕ) : (IterationSize.first initial).depth ≤ 602 := by
  have h := IterationSize.first_thin initial
  unfold Thin at h
  rw [IterationSize.first_witnessCount] at h
  exact h

theorem last_depth : IterationSize.last.depth ≤ 602 := by
  have h := IterationSize.last_thin
  unfold Thin at h
  rw [IterationSize.last_witnessCount] at h
  exact h

private theorem rows_depth_le {f : ℕ → ℕ} (p : DirectGraphEnumerator.R f)
    (initial h : ℕ) (hfirst : (IterationSize.first initial).depth ≤ h)
    (hlast : IterationSize.last.depth ≤ h)
    (hb : ((IterationSize.transition p).boundedForall (Sum.inl (some 0))).depth ≤ h) :
    (IterationSize.rows p initial).depth ≤ h + 4 := by
  simp only [IterationSize.rows, Rep.depth_existsBlock, Rep.depth_conjunction]
  omega

private theorem rows_witnessCount {f : ℕ → ℕ} (p : DirectGraphEnumerator.R f) (initial : ℕ) :
    (IterationSize.rows p initial).witnessCount =
      ((IterationSize.transition p).boundedForall (Sum.inl (some 0))).witnessCount + 32 := by
  simp only [IterationSize.rows, Rep.witnessCount_existsBlock, Rep.witnessCount_conjunction,
    IterationSize.first_witnessCount, IterationSize.last_witnessCount]
  omega

theorem iterate_depth (initial : ℕ) :
    (DirectGraphEnumerator.iterate NativeGraphEnumerator.optionStepProgram initial).depth ≤ 138113 := by
  calc
    _ = (IterationSize.rows NativeGraphEnumerator.optionStepProgram initial).depth :=
      IterationSize.iterate_depth _ _
    _ ≤ 138109 + 4 := rows_depth_le _ _ _
      ((first_depth initial).trans (by decide)) (last_depth.trans (by decide)) bounded_depth

theorem iterate_witnessCount (initial : ℕ) :
    (DirectGraphEnumerator.iterate NativeGraphEnumerator.optionStepProgram initial).witnessCount =
      (bounded).witnessCount + 32 :=
  (IterationSize.iterate_witnessCount _ _).trans (rows_witnessCount _ _)

private theorem ofEq_count {f g : ℕ → ℕ} (r : DirectGraphEnumerator.R f) (h : ∀ n, f n = g n) :
    (DirectGraphEnumerator.ofEq r h).witnessCount = r.witnessCount := rfl
private theorem ofEq_depth {f g : ℕ → ℕ} (r : DirectGraphEnumerator.R f) (h : ∀ n, f n = g n) :
    (DirectGraphEnumerator.ofEq r h).depth = r.depth := by
  unfold DirectGraphEnumerator.ofEq
  exact Rep.depth_ofIff _ _

private theorem ifZero_count {f g h : ℕ → ℕ}
    (r : DirectGraphEnumerator.R f) (s : DirectGraphEnumerator.R g) (t : DirectGraphEnumerator.R h) :
    (NativeGraphEnumerator.ifZero r s t).witnessCount =
      5 + r.witnessCount + s.witnessCount + t.witnessCount := by
  simp only [NativeGraphEnumerator.ifZero, NativeGraphEnumerator.ifEq_witnessCount,
    DirectGraphEnumerator.constant, GraphRep.witnessCount_constant]
  omega

private theorem ifZero_fixed_count {f : ℕ → ℕ} (r : DirectGraphEnumerator.R f) :
    (NativeGraphEnumerator.ifZero r (DirectGraphEnumerator.constant 1)
      (DirectGraphEnumerator.constant 0)).witnessCount = 5 + r.witnessCount := by
  have h := ifZero_count r (DirectGraphEnumerator.constant 1) (DirectGraphEnumerator.constant 0)
  simpa only [DirectGraphEnumerator.constant, GraphRep.witnessCount_constant, Nat.add_zero] using h

private theorem existsValue_count {f : ℕ → ℕ} (r : DirectGraphEnumerator.R f) (n : ℕ) :
    (GraphRep.existsValue r n).witnessCount = r.witnessCount + 2 := by
  simp only [GraphRep.existsValue, Rep.witnessCount_ofIff, Rep.witnessCount_existsBlock,
    Rep.witnessCount_conjunction, Rep.witnessCount_reindex, Rep.witnessCount_equality]
  omega

private theorem existsValue_depth_le {f : ℕ → ℕ} (r : DirectGraphEnumerator.R f)
    (n h : ℕ) (hh : 1 ≤ h) (hr : r.depth ≤ h) : (GraphRep.existsValue r n).depth ≤ h + 2 := by
  simp only [GraphRep.existsValue, Rep.depth_ofIff, Rep.depth_existsBlock,
    Rep.depth_conjunction, Rep.depth_reindex, Rep.depth_equality,
    Expr.depth_var, Expr.depth_constant]
  omega

private theorem ifZero_depth_le {f g h : ℕ → ℕ}
    (r : DirectGraphEnumerator.R f) (s : DirectGraphEnumerator.R g) (t : DirectGraphEnumerator.R h)
    (d : ℕ) (hd : 518 ≤ d) (hr : r.depth ≤ d) (hs : s.depth ≤ d) (ht : t.depth ≤ d) :
    (NativeGraphEnumerator.ifZero r s t).depth ≤ d + 10 := by
  have hi : GraphRep.ifEqDirectCoordinates.depth ≤ d := by
    have h := NativeEnumerationSize.ifEqCoordinates_thin
    unfold Thin at h
    rw [GraphRep.ifEqDirectCoordinates_witnessCount] at h
    exact h.trans (by simpa only [allowance] using hd)
  unfold NativeGraphEnumerator.ifZero NativeGraphEnumerator.ifEq GraphRep.ifEqDirect
  refine (GraphRep.composeDirect_depth_le _ _ (by omega) hi ?_).trans (by omega)
  intro i
  fin_cases i
  · exact hr
  · exact (GraphRep.depth_constant _).le.trans (by omega)
  · exact hs
  · exact ht

private theorem boundedRun_count : NativeGraphEnumerator.boundedRunProgram.witnessCount =
    (bounded).witnessCount + 32 := by
  have he : NativeGraphEnumerator.boundedRunProgram =
      definitionBody% NativeGraphEnumerator.boundedRunProgram := rfl
  calc
    _ = (definitionBody% NativeGraphEnumerator.boundedRunProgram).witnessCount :=
      congrArg Rep.witnessCount he
    _ = (DirectGraphEnumerator.iterate NativeGraphEnumerator.optionStepProgram
      (encodeOption (some initialState))).witnessCount := ofEq_count _ _
    _ = _ := iterate_witnessCount _

private theorem boundedRun_depth : NativeGraphEnumerator.boundedRunProgram.depth ≤ 138113 := by
  have he : NativeGraphEnumerator.boundedRunProgram =
      definitionBody% NativeGraphEnumerator.boundedRunProgram := rfl
  have hd : NativeGraphEnumerator.boundedRunProgram.depth =
      (DirectGraphEnumerator.iterate NativeGraphEnumerator.optionStepProgram
        (encodeOption (some initialState))).depth :=
    (congrArg Rep.depth he).trans (ofEq_depth _ _)
  exact hd.le.trans (iterate_depth _)

attribute [local irreducible] NativeGraphEnumerator.boundedRunProgram

private theorem program_count : NativeGraphEnumerator.program.witnessCount =
    5 + NativeGraphEnumerator.boundedRunProgram.witnessCount := by
  unfold NativeGraphEnumerator.program
  exact (ofEq_count _ _).trans (ifZero_fixed_count _)


private theorem program_depth : NativeGraphEnumerator.program.depth ≤ 138123 := by
  have he : NativeGraphEnumerator.program = definitionBody% NativeGraphEnumerator.program := rfl
  have hd : NativeGraphEnumerator.program.depth =
      (NativeGraphEnumerator.ifZero NativeGraphEnumerator.boundedRunProgram
        (DirectGraphEnumerator.constant 1) (DirectGraphEnumerator.constant 0)).depth :=
    (congrArg Rep.depth he).trans (ofEq_depth _ _)
  exact hd.le.trans (ifZero_depth_le _ _ _ _ (by decide) boundedRun_depth
    ((GraphRep.depth_constant _).le.trans (by decide))
    ((GraphRep.depth_constant _).le.trans (by decide)))

private theorem sourceCount_arithmetic (a b c d : ℕ) (ha : a = b + 2)
    (hb : b = 5 + c) (hc : c = d + 32) : a = d + 39 := by omega

theorem representation_witnessCount : NativeZFC.representation.witnessCount = (bounded).witnessCount + 39 := by
  have he : NativeZFC.representation = definitionBody% NativeZFC.representation := by rfl'
  have hr : NativeZFC.representation.witnessCount = NativeGraphEnumerator.program.witnessCount + 2 := by
    calc
      _ = (definitionBody% NativeZFC.representation).witnessCount := congrArg Rep.witnessCount he
      _ = (GraphRep.existsValue NativeGraphEnumerator.program 1).witnessCount := Rep.witnessCount_ofIff _ _
      _ = _ := existsValue_count _ _
  exact sourceCount_arithmetic _ _ _ _ hr program_count boundedRun_count

theorem representation_depth : NativeZFC.representation.depth ≤ 140000 := by
  have he : NativeZFC.representation = definitionBody% NativeZFC.representation := by rfl'
  have hd : NativeZFC.representation.depth =
      (GraphRep.existsValue NativeGraphEnumerator.program 1).depth :=
    (congrArg Rep.depth he).trans (Rep.depth_ofIff _ _)
  exact hd.le.trans ((existsValue_depth_le _ _ _ (by decide) program_depth).trans (by decide))

attribute [local irreducible] IterationSize.transition Rep.boundedForall NativeGraphEnumerator.optionStepProgram

private theorem bounded_count_arithmetic (S P w : ℕ) (hS : S ≤ P)
    (hP : 2 ^ 25 ≤ P)
    (hw : w = 1782 * (4 * S + 11790) + 10 * S + 20674) :
    w + 40 ≤ P * 65536 := by omega

private theorem rep_splitSize_le {σ : Type*} {P : (σ → ℕ) → Prop} (r : Rep σ P) :
    r.expression.splitSize + 2 ≤ 2 ^ (2 * r.depth + 2) := by
  simpa only [Rep.depth] using r.expression.splitSize_le_pow_depth

private theorem source_count_bound_arithmetic (m d S w c : ℕ)
    (hm : m = 1782) (hd : d ≤ 11204) (hs : S + 2 ≤ 2 ^ (2 * d + 2))
    (hw : w = m * (4 * S + 11790) + 10 * S + 20674)
    (hc : c = w + 39) : c + 1 ≤ 2 ^ 22426 := by
  have hp : S ≤ 2 ^ 22410 := (by omega : S ≤ 2 ^ (2 * d + 2)).trans
    (Nat.pow_le_pow_right (n := 2) (i := 2 * d + 2) (j := 22410) (by decide) (by omega))
  have hw' : w = 1782 * (4 * S + 11790) + 10 * S + 20674 := by
    simpa only [hm] using hw
  have hP : 2 ^ 25 ≤ 2 ^ 22410 := Nat.pow_le_pow_right (n := 2) (i := 25) (j := 22410) (by decide) (by decide)
  have h := bounded_count_arithmetic _ _ _ hp hP hw'
  calc
    c + 1 = w + 40 := (congrArg (fun z => z + 1) hc).trans
      (by omega : w + 39 + 1 = w + 40)
    _ ≤ 2 ^ 22410 * 65536 := h
    _ = 2 ^ 22410 * 2 ^ 16 := congrArg (fun z => 2 ^ 22410 * z) (by decide)
    _ = 2 ^ 22426 := (pow_add 2 22410 16).symm

theorem representation_witnessCount_le : NativeZFC.representation.witnessCount + 1 ≤ 2 ^ 22426 :=
  source_count_bound_arithmetic _ _ _ _ _
    IterationSize.native_transition_witnessCount IterationSize.native_transition_depth
    (rep_splitSize_le transition)
    (BoundedForallDepth.boundedForall_witnessCount transition (Sum.inl (some 0)))
    representation_witnessCount

private theorem variable_bound_arithmetic (v w r : ℕ) (hv : v ≤ r)
    (hr : r + 1 ≤ w + 2 ^ (2 * 140000 + 2)) (hw : w + 1 ≤ 2 ^ 22426) : v < 2 ^ 300000 := by
  have hp : 2 ^ (2 * 140000 + 2) ≤ 2 ^ 299999 :=
    Nat.pow_le_pow_right (n := 2) (i := 2 * 140000 + 2) (j := 299999) (by decide) (by decide)
  have hq : 2 ^ 22426 ≤ 2 ^ 299999 :=
    Nat.pow_le_pow_right (n := 2) (i := 22426) (j := 299999) (by decide) (by decide)
  apply Nat.lt_of_succ_le
  calc
    v + 1 ≤ r + 1 := Nat.add_le_add_right hv 1
    _ ≤ w + 2 ^ (2 * 140000 + 2) := hr
    _ ≤ 2 ^ 299999 + 2 ^ 299999 := Nat.add_le_add
      ((Nat.le_add_right w 1).trans (hw.trans hq)) hp
    _ = 2 ^ 299999 * 2 := (Nat.mul_two _).symm
    _ = 2 ^ 300000 := (pow_succ 2 299999).symm

/-- A concrete upper bound obtained without expanding the final syntax tree.
The compacted quartic therefore needs at most 300000 binary digits to write its
number of natural variables. This is deliberately a conservative upper bound. -/
theorem variableCount_lt : DirectQuarticZFC.variableCount < 2 ^ 300000 := by
  rw [DirectQuarticZFC.variableCount_eq]
  exact variable_bound_arithmetic _ _ _
    (Rep.compacted_variables_le NativeZFC.representation)
    (Rep.rawQuarticVariables_le NativeZFC.representation (le_refl _) representation_depth)
    representation_witnessCount_le

end DiophantineConsistency.DirectQuarticSize
