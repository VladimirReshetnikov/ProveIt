import IPRADerivations.Foundations.RealizerComposition
import IPRADerivations.Foundations.RealizerProduct

/-!
# A typed acyclic program frontend for bounded finite-query realizers

The frontend has primitive nodes with literal local laws, sequential nodes,
product/fanout and projection nodes, and actual query-dependent Boolean branches. Its raw PR metadata are computed
recursively from syntax independently of proof compilation. Compilation then
constructs a `Realizer` recursively and proves its metadata agree with the
source calculation.

This extends the acyclic part of FIBER `thm:compilation` with runtime demand
lists, bounded master verification, transformation and observation programs.
The standard canonical master convention and interface-law scope are those
of `RealizerComposition`. Translation of the remaining source node kinds,
cyclic closure/unrolling and arbitrary external master adapters remain separate.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.RealizerGraph

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.RealizerComposition
open LeanProofs.IPRA.Foundations.BoundedReflection (eqb_cases one_ne_zero)
open LeanProofs.IPRA.Foundations.MasterCertificate (sequence entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length block prefixSum flatMap)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- Raw code metadata contain no final target proof. -/
structure Code where
  demand : PR 2
  transform : PR 3
  guard : Fm PTm 2
  residuals : List (Fm PTm 2)

def Code.ofRealizer {X Y : Interface} (R : Realizer X Y) : Code :=
  ⟨R.demand, R.transform, R.guard, R.residuals⟩

/-- A primitive node supplies only its own fixed programs and local checked
contracts. A composite target realizer is constructed by the compiler. -/
structure Primitive (X Y : Interface) where
  code : Code
  sound : [code.guard.shift, (allOf code.residuals).shift,
      masterValid X (ap2 code.demand (var 1) (var 2)) (var 0) (var 2)] ⊢[PRAAx]
    valid Y (ap3 code.transform (var 0) (var 1) (var 2)) (var 1) (var 2)
  stable : [code.guard.shift.shift, (allOf code.residuals).shift.shift,
      masterValid X (ap2 code.demand (var 2) (var 3)) (var 0) (var 3),
      masterValid X (ap2 code.demand (var 2) (var 3)) (var 1) (var 3),
      masterRelated X (ap2 code.demand (var 2) (var 3)) (var 0) (var 1) (var 3)] ⊢[PRAAx]
    related Y (ap3 code.transform (var 0) (var 2) (var 3))
      (ap3 code.transform (var 1) (var 2) (var 3)) (var 2) (var 3)

def Primitive.realizer {X Y : Interface} (op : Primitive X Y) : Realizer X Y where
  demand := op.code.demand
  transform := op.code.transform
  guard := op.code.guard
  residuals := op.code.residuals
  sound := op.sound
  stable := op.stable

/-! ## Independent raw sequential metadata -/

def Code.bundleValue (R : Code) (C outer p j : PTm n) : PTm n :=
  ap3 R.transform (slice C (prefixSum R.demand outer p j) (length (block R.demand outer p j)))
    (entry outer j) p

def Code.bundleBody (R : Code) : PTm 2 :=
  R.bundleValue (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) (var 0)

def Code.bundle (R : Code) (C outer p : PTm n) : PTm n :=
  sequence R.bundleBody (length outer) (pairT C (pairT outer p))

def Code.seqDemand (R S : Code) : PR 2 :=
  PTm.toPR (flatMap R.demand (ap2 S.demand (var 0) (var 1)) (var 1))

def Code.seqTransform (R S : Code) : PR 3 :=
  PTm.toPR (ap3 S.transform (R.bundle (var 0) (ap2 S.demand (var 1) (var 2)) (var 2)) (var 1) (var 2))

def Code.seq (R S : Code) : Code where
  demand := R.seqDemand S
  transform := R.seqTransform S
  guard := S.guard ⋏ specializeAll R.guard (ap2 S.demand (var 0) (var 1)) (var 1)
  residuals := S.residuals ++ R.residuals.map (fun A => specializeAll A (ap2 S.demand (var 0) (var 1)) (var 1))

theorem Code.of_compose {X Y Z : Interface} (R : Realizer X Y) (S : Realizer Y Z) :
    Code.ofRealizer (compose R S) = (Code.ofRealizer R).seq (Code.ofRealizer S) := rfl

/-! ## Actual Boolean choice and branch metadata -/

def bit (test : PR 2) (q p : PTm n) : PTm n := eqb (ap2 test q p) one
def pick (b a c : PTm n) : PTm n := monus one b * a + b * c

@[simp] theorem subst_bit {m : ℕ} (σ : Fin n → PTm m) (test : PR 2) (q p : PTm n) :
    Syn.subst σ (bit test q p) = bit test (Syn.subst σ q) (Syn.subst σ p) := by simp [bit]
@[simp] theorem subst_pick {m : ℕ} (σ : Fin n → PTm m) (b a c : PTm n) :
    Syn.subst σ (pick b a c) = pick (Syn.subst σ b) (Syn.subst σ a) (Syn.subst σ c) := by simp [pick]

theorem bit_cases (test : PR 2) (q p : PTm n) :
    Γ ⊢[PRAAx] (bit test q p ≐ zero) ⋎ (bit test q p ≐ one) := eqb_cases _ _

theorem pick_zero {b : PTm n} (a c : PTm n) (hb : Γ ⊢[PRAAx] b ≐ zero) :
    Γ ⊢[PRAAx] pick b a c ≐ a := by
  have b := natEq hb
  have complement := natEq ((congrMonus (Γ := Γ) (.eqRefl one) hb).eqTrans (monus_zero one))
  unfold pick
  apply deriveNat
  ipra_simps
  linear_combination 𝔞(a) * complement + 𝔞(c) * b

theorem pick_one {b : PTm n} (a c : PTm n) (hb : Γ ⊢[PRAAx] b ≐ one) :
    Γ ⊢[PRAAx] pick b a c ≐ c := by
  have b := natEq hb
  have complement := natEq ((congrMonus (Γ := Γ) (.eqRefl one) hb).eqTrans (monus_self one))
  unfold pick
  apply deriveNat
  ipra_simps
  linear_combination 𝔞(a) * complement + 𝔞(c) * b

def Code.branchDemandTerm (test : PR 2) (L R : Code) (q p : PTm n) : PTm n :=
  pick (bit test q p) (ap2 L.demand q p) (ap2 R.demand q p)

def Code.branchDemand (test : PR 2) (L R : Code) : PR 2 :=
  PTm.toPR (branchDemandTerm test L R (var 0) (var 1))

def Code.branchTransformTerm (test : PR 2) (L R : Code) (C q p : PTm n) : PTm n :=
  pick (bit test q p) (ap3 L.transform C q p) (ap3 R.transform C q p)

def Code.branchTransform (test : PR 2) (L R : Code) : PR 3 :=
  PTm.toPR (branchTransformTerm test L R (var 0) (var 1) (var 2))

def caseResidual (test : PR 2) (value : PTm 2) (A : Fm PTm 2) : Fm PTm 2 :=
  (bit test (var 0) (var 1) ≐ value) ⟶ A

def Code.branch (test : PR 2) (L R : Code) : Code where
  demand := branchDemand test L R
  transform := branchTransform test L R
  guard := caseResidual test zero L.guard ⋏ caseResidual test one R.guard
  residuals := L.residuals.map (caseResidual test zero) ++ R.residuals.map (caseResidual test one)

@[simp] theorem subst_branchDemandTerm {m : ℕ} (σ : Fin n → PTm m) (test : PR 2) (L R : Code) (q p : PTm n) :
    Syn.subst σ (Code.branchDemandTerm test L R q p) =
      Code.branchDemandTerm test L R (Syn.subst σ q) (Syn.subst σ p) := by simp [Code.branchDemandTerm]

@[simp] theorem subst_branchTransformTerm {m : ℕ} (σ : Fin n → PTm m) (test : PR 2) (L R : Code) (C q p : PTm n) :
    Syn.subst σ (Code.branchTransformTerm test L R C q p) =
      Code.branchTransformTerm test L R (Syn.subst σ C) (Syn.subst σ q) (Syn.subst σ p) := by
  simp [Code.branchTransformTerm]

theorem branch_demand_at (test : PR 2) (L R : Code) (q p : PTm n) :
    Γ ⊢[PRAAx] ap2 (Code.branchDemand test L R) q p ≐ Code.branchDemandTerm test L R q p := by
  have h := toPR_eq (Γ := Γ) (Code.branchDemandTerm test L R (var 0) (var 1)) ![q, p]
  simpa [Code.branchDemand, ap2] using h

theorem branch_transform_at (test : PR 2) (L R : Code) (C q p : PTm n) :
    Γ ⊢[PRAAx] ap3 (Code.branchTransform test L R) C q p ≐ Code.branchTransformTerm test L R C q p := by
  have h := toPR_eq (Γ := Γ) (Code.branchTransformTerm test L R (var 0) (var 1) (var 2)) ![C, q, p]
  simpa [Code.branchTransform, ap3] using h

theorem branch_demand_zero (test : PR 2) (L R : Code) (q p : PTm n) (hb : Γ ⊢[PRAAx] bit test q p ≐ zero) :
    Γ ⊢[PRAAx] ap2 (Code.branchDemand test L R) q p ≐ ap2 L.demand q p :=
  (branch_demand_at _ _ _ _ _).eqTrans (pick_zero _ _ hb)

theorem branch_demand_one (test : PR 2) (L R : Code) (q p : PTm n) (hb : Γ ⊢[PRAAx] bit test q p ≐ one) :
    Γ ⊢[PRAAx] ap2 (Code.branchDemand test L R) q p ≐ ap2 R.demand q p :=
  (branch_demand_at _ _ _ _ _).eqTrans (pick_one _ _ hb)

theorem branch_transform_zero (test : PR 2) (L R : Code) (C q p : PTm n) (hb : Γ ⊢[PRAAx] bit test q p ≐ zero) :
    Γ ⊢[PRAAx] ap3 (Code.branchTransform test L R) C q p ≐ ap3 L.transform C q p :=
  (branch_transform_at _ _ _ _ _ _).eqTrans (pick_zero _ _ hb)

theorem branch_transform_one (test : PR 2) (L R : Code) (C q p : PTm n) (hb : Γ ⊢[PRAAx] bit test q p ≐ one) :
    Γ ⊢[PRAAx] ap3 (Code.branchTransform test L R) C q p ≐ ap3 R.transform C q p :=
  (branch_transform_at _ _ _ _ _ _).eqTrans (pick_one _ _ hb)

#print axioms branch_transform_zero

theorem branch_guard_zero (test : PR 2) (L R : Code) (q p : PTm n)
    (h : Γ ⊢[PRAAx] queryAt (Code.branch test L R).guard q p)
    (hb : Γ ⊢[PRAAx] bit test q p ≐ zero) : Γ ⊢[PRAAx] queryAt L.guard q p := by
  have guards : Γ ⊢[PRAAx] ((bit test q p ≐ zero) ⟶ queryAt L.guard q p) ⋏
      ((bit test q p ≐ one) ⟶ queryAt R.guard q p) := by
    simpa [queryAt, Code.branch, caseResidual] using h
  exact Prf.impE (Prf.andE₁ guards) hb

theorem branch_guard_one (test : PR 2) (L R : Code) (q p : PTm n)
    (h : Γ ⊢[PRAAx] queryAt (Code.branch test L R).guard q p)
    (hb : Γ ⊢[PRAAx] bit test q p ≐ one) : Γ ⊢[PRAAx] queryAt R.guard q p := by
  have guards : Γ ⊢[PRAAx] ((bit test q p ≐ zero) ⟶ queryAt L.guard q p) ⋏
      ((bit test q p ≐ one) ⟶ queryAt R.guard q p) := by
    simpa [queryAt, Code.branch, caseResidual] using h
  exact Prf.impE (Prf.andE₂ guards) hb

theorem branch_residuals_zero (test : PR 2) (L R : Code) (q p : PTm n)
    (h : Γ ⊢[PRAAx] queryAt (allOf (Code.branch test L R).residuals) q p)
    (hb : Γ ⊢[PRAAx] bit test q p ≐ zero) : Γ ⊢[PRAAx] queryAt (allOf L.residuals) q p := by
  apply allOf_at_intro L.residuals ![q, p]
  intro A hA
  have member : caseResidual test zero A ∈ (Code.branch test L R).residuals :=
    List.mem_append_left _ (List.mem_map.mpr ⟨A, hA, rfl⟩)
  have one := allOf_at_elim (Code.branch test L R).residuals ![q, p] h member
  have guarded : Γ ⊢[PRAAx] (bit test q p ≐ zero) ⟶ queryAt A q p := by
    simpa [caseResidual, queryAt] using one
  exact Prf.impE guarded hb

theorem branch_residuals_one (test : PR 2) (L R : Code) (q p : PTm n)
    (h : Γ ⊢[PRAAx] queryAt (allOf (Code.branch test L R).residuals) q p)
    (hb : Γ ⊢[PRAAx] bit test q p ≐ one) : Γ ⊢[PRAAx] queryAt (allOf R.residuals) q p := by
  apply allOf_at_intro R.residuals ![q, p]
  intro A hA
  have member : caseResidual test one A ∈ (Code.branch test L R).residuals :=
    List.mem_append_right _ (List.mem_map.mpr ⟨A, hA, rfl⟩)
  have selectedClause := allOf_at_elim (Code.branch test L R).residuals ![q, p] h member
  have guarded : Γ ⊢[PRAAx] (bit test q p ≐ one) ⟶ queryAt A q p := by
    simpa [caseResidual, queryAt] using selectedClause
  exact Prf.impE guarded hb

theorem branch_sound {X Y : Interface} (test : PR 2) (L R : Realizer X Y) (C q p : PTm n)
    (hg : Γ ⊢[PRAAx] queryAt (Code.branch test (Code.ofRealizer L) (Code.ofRealizer R)).guard q p)
    (hr : Γ ⊢[PRAAx] queryAt (allOf (Code.branch test (Code.ofRealizer L) (Code.ofRealizer R)).residuals) q p)
    (hC : Γ ⊢[PRAAx] masterValid X
      (ap2 (Code.branchDemand test (Code.ofRealizer L) (Code.ofRealizer R)) q p) C p) :
    Γ ⊢[PRAAx] valid Y
      (ap3 (Code.branchTransform test (Code.ofRealizer L) (Code.ofRealizer R)) C q p) q p := by
  refine .orE (bit_cases test q p) ?_ ?_
  · have d := branch_demand_zero test (Code.ofRealizer L) (Code.ofRealizer R) q p
      (Prf.hyp0 : (bit test q p ≐ zero) :: Γ ⊢[PRAAx] _)
    have selected := L.applySound C q p
      (branch_guard_zero _ _ _ _ _ hg.wk Prf.hyp0)
      (branch_residuals_zero _ _ _ _ _ hr.wk Prf.hyp0)
      (masterValid_congr X d (.eqRefl _) (.eqRefl _) hC.wk)
    exact valid_congr Y (branch_transform_zero _ _ _ _ _ _ Prf.hyp0).eqSymm (.eqRefl _) (.eqRefl _) selected
  · have d := branch_demand_one test (Code.ofRealizer L) (Code.ofRealizer R) q p
      (Prf.hyp0 : (bit test q p ≐ one) :: Γ ⊢[PRAAx] _)
    have selected := R.applySound C q p
      (branch_guard_one _ _ _ _ _ hg.wk Prf.hyp0)
      (branch_residuals_one _ _ _ _ _ hr.wk Prf.hyp0)
      (masterValid_congr X d (.eqRefl _) (.eqRefl _) hC.wk)
    exact valid_congr Y (branch_transform_one _ _ _ _ _ _ Prf.hyp0).eqSymm (.eqRefl _) (.eqRefl _) selected

theorem branch_stable {X Y : Interface} (test : PR 2) (L R : Realizer X Y) (C C' q p : PTm n)
    (hg : Γ ⊢[PRAAx] queryAt (Code.branch test (Code.ofRealizer L) (Code.ofRealizer R)).guard q p)
    (hr : Γ ⊢[PRAAx] queryAt (allOf (Code.branch test (Code.ofRealizer L) (Code.ofRealizer R)).residuals) q p)
    (hC : Γ ⊢[PRAAx] masterValid X
      (ap2 (Code.branchDemand test (Code.ofRealizer L) (Code.ofRealizer R)) q p) C p)
    (hC' : Γ ⊢[PRAAx] masterValid X
      (ap2 (Code.branchDemand test (Code.ofRealizer L) (Code.ofRealizer R)) q p) C' p)
    (hrel : Γ ⊢[PRAAx] masterRelated X
      (ap2 (Code.branchDemand test (Code.ofRealizer L) (Code.ofRealizer R)) q p) C C' p) :
    Γ ⊢[PRAAx] related Y
      (ap3 (Code.branchTransform test (Code.ofRealizer L) (Code.ofRealizer R)) C q p)
      (ap3 (Code.branchTransform test (Code.ofRealizer L) (Code.ofRealizer R)) C' q p) q p := by
  refine .orE (bit_cases test q p) ?_ ?_
  · have d := branch_demand_zero test (Code.ofRealizer L) (Code.ofRealizer R) q p
      (Prf.hyp0 : (bit test q p ≐ zero) :: Γ ⊢[PRAAx] _)
    have selected := L.applyStable C C' q p
      (branch_guard_zero _ _ _ _ _ hg.wk Prf.hyp0)
      (branch_residuals_zero _ _ _ _ _ hr.wk Prf.hyp0)
      (masterValid_congr X d (.eqRefl _) (.eqRefl _) hC.wk)
      (masterValid_congr X d (.eqRefl _) (.eqRefl _) hC'.wk)
      (masterRelated_congr X d (.eqRefl _) (.eqRefl _) (.eqRefl _) hrel.wk)
    exact related_congr Y (branch_transform_zero _ _ _ _ _ _ Prf.hyp0).eqSymm
      (branch_transform_zero _ _ _ _ _ _ Prf.hyp0).eqSymm (.eqRefl _) (.eqRefl _) selected
  · have d := branch_demand_one test (Code.ofRealizer L) (Code.ofRealizer R) q p
      (Prf.hyp0 : (bit test q p ≐ one) :: Γ ⊢[PRAAx] _)
    have selected := R.applyStable C C' q p
      (branch_guard_one _ _ _ _ _ hg.wk Prf.hyp0)
      (branch_residuals_one _ _ _ _ _ hr.wk Prf.hyp0)
      (masterValid_congr X d (.eqRefl _) (.eqRefl _) hC.wk)
      (masterValid_congr X d (.eqRefl _) (.eqRefl _) hC'.wk)
      (masterRelated_congr X d (.eqRefl _) (.eqRefl _) (.eqRefl _) hrel.wk)
    exact related_congr Y (branch_transform_one _ _ _ _ _ _ Prf.hyp0).eqSymm
      (branch_transform_one _ _ _ _ _ _ Prf.hyp0).eqSymm (.eqRefl _) (.eqRefl _) selected

def branchRealizer {X Y : Interface} (test : PR 2) (L R : Realizer X Y) : Realizer X Y where
  demand := Code.branchDemand test (Code.ofRealizer L) (Code.ofRealizer R)
  transform := Code.branchTransform test (Code.ofRealizer L) (Code.ofRealizer R)
  guard := (Code.branch test (Code.ofRealizer L) (Code.ofRealizer R)).guard
  residuals := (Code.branch test (Code.ofRealizer L) (Code.ofRealizer R)).residuals
  sound := by
    let data := Code.branch test (Code.ofRealizer L) (Code.ofRealizer R)
    let Δ : List (Fm PTm 3) := [data.guard.shift, (allOf data.residuals).shift,
      masterValid X (ap2 data.demand (var 1) (var 2)) (var 0) (var 2)]
    have hg : Δ ⊢[PRAAx] queryAt data.guard (var 1) (var 2) := by
      rw [queryAt_shift3]
      exact Prf.hyp0
    have hr : Δ ⊢[PRAAx] queryAt (allOf data.residuals) (var 1) (var 2) := by
      rw [queryAt_shift3]
      exact Prf.hyp1
    exact branch_sound test L R (var 0) (var 1) (var 2) hg hr hyp2
  stable := by
    let data := Code.branch test (Code.ofRealizer L) (Code.ofRealizer R)
    let Δ : List (Fm PTm 4) := [data.guard.shift.shift, (allOf data.residuals).shift.shift,
      masterValid X (ap2 data.demand (var 2) (var 3)) (var 0) (var 3),
      masterValid X (ap2 data.demand (var 2) (var 3)) (var 1) (var 3),
      masterRelated X (ap2 data.demand (var 2) (var 3)) (var 0) (var 1) (var 3)]
    have hg : Δ ⊢[PRAAx] queryAt data.guard (var 2) (var 3) := by
      rw [queryAt_shift4]
      exact Prf.hyp0
    have hr : Δ ⊢[PRAAx] queryAt (allOf data.residuals) (var 2) (var 3) := by
      rw [queryAt_shift4]
      exact Prf.hyp1
    exact branch_stable test L R (var 0) (var 1) (var 2) (var 3) hg hr hyp2 hyp2.wk hyp2.wk.wk

theorem Code.of_branch {X Y : Interface} (test : PR 2) (L R : Realizer X Y) :
    Code.ofRealizer (branchRealizer test L R) = Code.branch test (Code.ofRealizer L) (Code.ofRealizer R) := rfl

/-! ## Independent metadata for product and projection nodes -/

def Code.fanoutDemandTerm (L R : Code) (q p : PTm n) : PTm n :=
  SequenceComposition.append (ap2 L.demand (fstT q) p) (ap2 R.demand (sndT q) p)

def Code.fanoutTransformTerm (L R : Code) (C q p : PTm n) : PTm n :=
  pairT (ap3 L.transform (slice C zero (length (ap2 L.demand (fstT q) p))) (fstT q) p)
    (ap3 R.transform (slice C (length (ap2 L.demand (fstT q) p))
      (length (ap2 R.demand (sndT q) p))) (sndT q) p)

def Code.fanout (L R : Code) : Code where
  demand := PTm.toPR (Code.fanoutDemandTerm L R (var 0) (var 1))
  transform := PTm.toPR (Code.fanoutTransformTerm L R (var 0) (var 1) (var 2))
  guard := RealizerProduct.leftTemplate L.guard ⋏ RealizerProduct.rightTemplate R.guard
  residuals := L.residuals.map RealizerProduct.leftTemplate ++
    R.residuals.map RealizerProduct.rightTemplate

def Code.projectLeft (companion : PR 2) : Code :=
  ⟨RealizerProduct.leftDemandF companion, RealizerProduct.leftTransformF,
    (zero ≐ zero : Fm PTm 2), []⟩

def Code.projectRight (companion : PR 2) : Code :=
  ⟨RealizerProduct.rightDemandF companion, RealizerProduct.rightTransformF,
    (zero ≐ zero : Fm PTm 2), []⟩

theorem Code.of_fanout {X Y Z : Interface} (L : Realizer X Y) (R : Realizer X Z) :
    Code.ofRealizer (RealizerProduct.fanout L R) = Code.fanout (Code.ofRealizer L) (Code.ofRealizer R) := rfl

theorem Code.of_projectLeft (Y Z : Interface) (companion : PR 2) :
    Code.ofRealizer (RealizerProduct.projectLeft Y Z companion) = Code.projectLeft companion := rfl

theorem Code.of_projectRight (Y Z : Interface) (companion : PR 2) :
    Code.ofRealizer (RealizerProduct.projectRight Y Z companion) = Code.projectRight companion := rfl

/-! ## Typed acyclic syntax and independent recursive metadata -/

inductive Program : Interface → Interface → Type
  | primitive {X Y : Interface} (op : Primitive X Y) : Program X Y
  | seq {X Y Z : Interface} (first : Program X Y) (second : Program Y Z) : Program X Z
  | fanout {X Y Z : Interface} (first : Program X Y) (second : Program X Z) :
      Program X (RealizerProduct.product Y Z)
  | projectLeft (Y Z : Interface) (companion : PR 2) : Program (RealizerProduct.product Y Z) Y
  | projectRight (Y Z : Interface) (companion : PR 2) : Program (RealizerProduct.product Y Z) Z
  | booleanBranch {X Y : Interface} (test : PR 2) (zeroBranch oneBranch : Program X Y) : Program X Y

def Program.code : {X Y : Interface} → Program X Y → Code
  | _, _, .primitive op => op.code
  | _, _, .seq first second => first.code.seq second.code
  | _, _, .fanout first second => Code.fanout first.code second.code
  | _, _, .projectLeft _ _ companion => Code.projectLeft companion
  | _, _, .projectRight _ _ companion => Code.projectRight companion
  | _, _, .booleanBranch test left right => Code.branch test left.code right.code

def Program.compile : {X Y : Interface} → Program X Y → Realizer X Y
  | _, _, .primitive op => op.realizer
  | _, _, .seq first second => compose first.compile second.compile
  | _, _, .fanout first second => RealizerProduct.fanout first.compile second.compile
  | _, _, .projectLeft Y Z companion => RealizerProduct.projectLeft Y Z companion
  | _, _, .projectRight Y Z companion => RealizerProduct.projectRight Y Z companion
  | _, _, .booleanBranch test left right => branchRealizer test left.compile right.compile

/-- Compilation inspects the source program recursively. This theorem links
its checked realizer to the independently computed raw PR metadata. -/
theorem Program.compile_code {X Y : Interface} (P : Program X Y) :
    Code.ofRealizer P.compile = P.code := by
  induction P with
  | primitive op => rfl
  | seq first second ihFirst ihSecond =>
    rw [Program.compile, Code.of_compose, ihFirst, ihSecond]
    rfl
  | fanout first second ihFirst ihSecond =>
    rw [Program.compile, Code.of_fanout, ihFirst, ihSecond]
    rfl
  | projectLeft Y Z companion => rfl
  | projectRight Y Z companion => rfl
  | booleanBranch test left right ihLeft ihRight =>
    rw [Program.compile, Code.of_branch, ihLeft, ihRight]
    rfl

#print axioms branchRealizer
#print axioms Program.compile
#print axioms Program.compile_code

/-! ## Source-level PR metadata and the compiler linkage -/

def Code.boundF (X : Interface) (data : Code) : PR 2 :=
  PTm.toPR (masterBound X (ap2 data.demand (var 0) (var 1)) (var 1))

def Code.verifierF (X : Interface) (data : Code) : PR 3 :=
  PTm.toPR (masterBit X (ap2 data.demand (var 1) (var 2)) (var 0) (var 2))

def Code.observationF (Y : Interface) (data : Code) : PR 3 :=
  PTm.toPR (ap3 Y.observe (ap3 data.transform (var 0) (var 1) (var 2)) (var 1) (var 2))

def Program.demandF {X Y : Interface} (P : Program X Y) : PR 2 := P.code.demand
def Program.transformF {X Y : Interface} (P : Program X Y) : PR 3 := P.code.transform
def Program.guard {X Y : Interface} (P : Program X Y) : Fm PTm 2 := P.code.guard
def Program.residuals {X Y : Interface} (P : Program X Y) : List (Fm PTm 2) := P.code.residuals
def Program.boundF {X Y : Interface} (P : Program X Y) : PR 2 := P.code.boundF X
def Program.verifierF {X Y : Interface} (P : Program X Y) : PR 3 := P.code.verifierF X
def Program.observationF {X Y : Interface} (P : Program X Y) : PR 3 := P.code.observationF Y

theorem Program.compile_demand {X Y : Interface} (P : Program X Y) : P.compile.demand = P.demandF :=
  congrArg Code.demand P.compile_code
theorem Program.compile_transform {X Y : Interface} (P : Program X Y) : P.compile.transform = P.transformF :=
  congrArg Code.transform P.compile_code
theorem Program.compile_guard {X Y : Interface} (P : Program X Y) : P.compile.guard = P.guard :=
  congrArg Code.guard P.compile_code
theorem Program.compile_residuals {X Y : Interface} (P : Program X Y) : P.compile.residuals = P.residuals :=
  congrArg Code.residuals P.compile_code

theorem Program.compile_bound {X Y : Interface} (P : Program X Y) : P.compile.inputBoundF = P.boundF := by
  unfold Realizer.inputBoundF Program.boundF Code.boundF
  rw [P.compile_demand]
  rfl
theorem Program.compile_verifier {X Y : Interface} (P : Program X Y) : P.compile.inputVerifierF = P.verifierF := by
  unfold Realizer.inputVerifierF Program.verifierF Code.verifierF
  rw [P.compile_demand]
  rfl
theorem Program.compile_observation {X Y : Interface} (P : Program X Y) : P.compile.outputObservationF = P.observationF := by
  unfold Realizer.outputObservationF Program.observationF Code.observationF
  rw [P.compile_transform]
  rfl

theorem Program.verifier_sound {X Y : Interface} (P : Program X Y) (C q p : PTm n)
    (hv : Γ ⊢[PRAAx] ap3 P.verifierF C q p ≐ one) :
    Γ ⊢[PRAAx] masterValid X (ap2 P.demandF q p) C p := by
  have checked : Γ ⊢[PRAAx] ap3 P.compile.inputVerifierF C q p ≐ one := by
    simpa only [P.compile_verifier] using hv
  simpa only [P.compile_demand] using P.compile.verifier_sound C q p checked

theorem Program.sound {X Y : Interface} (P : Program X Y) (C q p : PTm n)
    (hg : Γ ⊢[PRAAx] queryAt P.guard q p) (hr : Γ ⊢[PRAAx] queryAt (allOf P.residuals) q p)
    (hv : Γ ⊢[PRAAx] ap3 P.verifierF C q p ≐ one) :
    Γ ⊢[PRAAx] valid Y (ap3 P.transformF C q p) q p := by
  have guard : Γ ⊢[PRAAx] queryAt P.compile.guard q p := by simpa only [P.compile_guard] using hg
  have residual : Γ ⊢[PRAAx] queryAt (allOf P.compile.residuals) q p := by simpa only [P.compile_residuals] using hr
  have input : Γ ⊢[PRAAx] masterValid X (ap2 P.compile.demand q p) C p := by
    simpa only [P.compile_demand] using P.verifier_sound C q p hv
  simpa only [P.compile_transform] using P.compile.applySound C q p guard residual input

theorem Program.stable {X Y : Interface} (P : Program X Y) (C C' q p : PTm n)
    (hg : Γ ⊢[PRAAx] queryAt P.guard q p) (hr : Γ ⊢[PRAAx] queryAt (allOf P.residuals) q p)
    (hv : Γ ⊢[PRAAx] ap3 P.verifierF C q p ≐ one) (hv' : Γ ⊢[PRAAx] ap3 P.verifierF C' q p ≐ one)
    (hrel : Γ ⊢[PRAAx] masterRelated X (ap2 P.demandF q p) C C' p) :
    Γ ⊢[PRAAx] ap4 Y.related (ap3 P.observationF C q p) (ap3 P.observationF C' q p) q p ≐ one := by
  have guard : Γ ⊢[PRAAx] queryAt P.compile.guard q p := by simpa only [P.compile_guard] using hg
  have residual : Γ ⊢[PRAAx] queryAt (allOf P.compile.residuals) q p := by simpa only [P.compile_residuals] using hr
  have input : Γ ⊢[PRAAx] masterValid X (ap2 P.compile.demand q p) C p := by
    simpa only [P.compile_demand] using P.verifier_sound C q p hv
  have input' : Γ ⊢[PRAAx] masterValid X (ap2 P.compile.demand q p) C' p := by
    simpa only [P.compile_demand] using P.verifier_sound C' q p hv'
  have related : Γ ⊢[PRAAx] masterRelated X (ap2 P.compile.demand q p) C C' p := by
    simpa only [P.compile_demand] using hrel
  simpa only [P.compile_observation] using P.compile.observe_stable C C' q p guard residual input input' related

def Program.inputTotal {X Y : Interface} (P : Program X Y) (q p : PTm n) : Fm PTm n :=
  .ex (ap3 P.verifierF (var 0) (Syn.shift q) (Syn.shift p) ≐ one)

theorem Program.seal {X Y : Interface} (P : Program X Y) (q p : PTm n)
    (hg : Γ ⊢[PRAAx] queryAt P.guard q p) (hr : Γ ⊢[PRAAx] queryAt (allOf P.residuals) q p)
    (ht : Γ ⊢[PRAAx] P.inputTotal q p) : Γ ⊢[PRAAx] outputTotal Y q p := by
  have guard : Γ ⊢[PRAAx] queryAt P.compile.guard q p := by simpa only [P.compile_guard] using hg
  have residual : Γ ⊢[PRAAx] queryAt (allOf P.compile.residuals) q p := by simpa only [P.compile_residuals] using hr
  have input : Γ ⊢[PRAAx] RealizerComposition.inputTotal P.compile q p := by
    simpa only [RealizerComposition.inputTotal, Program.inputTotal, P.compile_verifier] using ht
  exact P.compile.seal q p guard residual input

/-- Discharge the exact residuals calculated from syntax under arbitrary
client hypotheses. No final target proof is an input to this compiler. -/
theorem Program.emit {X Y : Interface} (P : Program X Y) (C q p : PTm n)
    (hg : Γ ⊢[PRAAx] queryAt P.guard q p) (hv : Γ ⊢[PRAAx] ap3 P.verifierF C q p ≐ one)
    (producers : ∀ A, A ∈ P.residuals → (Γ ⊢[PRAAx] queryAt A q p)) :
    Γ ⊢[PRAAx] valid Y (ap3 P.transformF C q p) q p :=
  P.sound C q p hg (allOf_at_intro P.residuals ![q, p] producers) hv

/-! ## Source constructor equations -/

@[simp] theorem Code.subst_bundleValue {m : ℕ} (σ : Fin n → PTm m) (R : Code) (C outer p j : PTm n) :
    Syn.subst σ (R.bundleValue C outer p j) =
      R.bundleValue (Syn.subst σ C) (Syn.subst σ outer) (Syn.subst σ p) (Syn.subst σ j) := by
  simp [Code.bundleValue]

@[simp] theorem Code.subst_bundle {m : ℕ} (σ : Fin n → PTm m) (R : Code) (C outer p : PTm n) :
    Syn.subst σ (R.bundle C outer p) = R.bundle (Syn.subst σ C) (Syn.subst σ outer) (Syn.subst σ p) := by
  simp [Code.bundle]

theorem Code.seqDemand_at (R S : Code) (q p : PTm n) :
    Γ ⊢[PRAAx] ap2 (R.seqDemand S) q p ≐ flatMap R.demand (ap2 S.demand q p) p := by
  have h := toPR_eq (Γ := Γ) (flatMap R.demand (ap2 S.demand (var 0) (var 1)) (var 1)) ![q, p]
  have clean : Γ ⊢[PRAAx] ConciseIPRA.PTm.app (R.seqDemand S) ![q, p] ≐
      flatMap R.demand (ap2 S.demand q p) p := by
    simpa only [Code.seqDemand, SequenceComposition.subst_flatMap, subst_ap2,
      Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one] using h
  simpa only [ap2] using clean

theorem Code.seqTransform_at (R S : Code) (C q p : PTm n) :
    Γ ⊢[PRAAx] ap3 (R.seqTransform S) C q p ≐ ap3 S.transform (R.bundle C (ap2 S.demand q p) p) q p := by
  have h := toPR_eq (Γ := Γ) (ap3 S.transform
    (R.bundle (var 0) (ap2 S.demand (var 1) (var 2)) (var 2)) (var 1) (var 2)) ![C, q, p]
  have clean : Γ ⊢[PRAAx] ConciseIPRA.PTm.app (R.seqTransform S) ![C, q, p] ≐
      ap3 S.transform (R.bundle C (ap2 S.demand q p) p) q p := by
    simpa only [Code.seqTransform, subst_ap3, Code.subst_bundle, subst_ap2,
      Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] using h
  simpa only [ap3] using clean

#print axioms Program.sound
#print axioms Program.stable
#print axioms Program.seal
#print axioms Code.seqTransform_at

/-! ## Only the reached branch's producer obligations are needed -/

theorem branch_scope_zero (test : PR 2) (L R : Code) (q p : PTm n)
    (hb : Γ ⊢[PRAAx] bit test q p ≐ zero)
    (hg : Γ ⊢[PRAAx] queryAt L.guard q p)
    (hr : Γ ⊢[PRAAx] queryAt (allOf L.residuals) q p) :
    Γ ⊢[PRAAx] queryAt (Code.branch test L R).guard q p ⋏
      queryAt (allOf (Code.branch test L R).residuals) q p := by
  refine .andI ?_ ?_
  · have clauses : Γ ⊢[PRAAx] ((bit test q p ≐ zero) ⟶ queryAt L.guard q p) ⋏
        ((bit test q p ≐ one) ⟶ queryAt R.guard q p) :=
      .andI (.impI hg.wk) (.impI (one_ne_zero _ (Prf.hyp0.eqSymm.eqTrans hb.wk)))
    simpa [queryAt, Code.branch, caseResidual] using clauses
  · apply allOf_at_intro (Code.branch test L R).residuals ![q, p]
    intro A hA
    rcases List.mem_append.1 hA with left | right
    · rcases List.mem_map.1 left with ⟨B, hB, rfl⟩
      have clause : Γ ⊢[PRAAx] (bit test q p ≐ zero) ⟶ queryAt B q p :=
        .impI ((allOf_at_elim L.residuals ![q, p] hr hB).wk)
      simpa [caseResidual, queryAt] using clause
    · rcases List.mem_map.1 right with ⟨B, _, rfl⟩
      have clause : Γ ⊢[PRAAx] (bit test q p ≐ one) ⟶ queryAt B q p :=
        .impI (one_ne_zero _ (Prf.hyp0.eqSymm.eqTrans hb.wk))
      simpa [caseResidual, queryAt] using clause

theorem branch_scope_one (test : PR 2) (L R : Code) (q p : PTm n)
    (hb : Γ ⊢[PRAAx] bit test q p ≐ one)
    (hg : Γ ⊢[PRAAx] queryAt R.guard q p)
    (hr : Γ ⊢[PRAAx] queryAt (allOf R.residuals) q p) :
    Γ ⊢[PRAAx] queryAt (Code.branch test L R).guard q p ⋏
      queryAt (allOf (Code.branch test L R).residuals) q p := by
  refine .andI ?_ ?_
  · have clauses : Γ ⊢[PRAAx] ((bit test q p ≐ zero) ⟶ queryAt L.guard q p) ⋏
        ((bit test q p ≐ one) ⟶ queryAt R.guard q p) :=
      .andI (.impI (one_ne_zero _ (hb.wk.eqSymm.eqTrans Prf.hyp0))) (.impI hg.wk)
    simpa [queryAt, Code.branch, caseResidual] using clauses
  · apply allOf_at_intro (Code.branch test L R).residuals ![q, p]
    intro A hA
    rcases List.mem_append.1 hA with left | right
    · rcases List.mem_map.1 left with ⟨B, _, rfl⟩
      have clause : Γ ⊢[PRAAx] (bit test q p ≐ zero) ⟶ queryAt B q p :=
        .impI (one_ne_zero _ (hb.wk.eqSymm.eqTrans Prf.hyp0))
      simpa [caseResidual, queryAt] using clause
    · rcases List.mem_map.1 right with ⟨B, hB, rfl⟩
      have clause : Γ ⊢[PRAAx] (bit test q p ≐ one) ⟶ queryAt B q p :=
        .impI ((allOf_at_elim R.residuals ![q, p] hr hB).wk)
      simpa [caseResidual, queryAt] using clause

/-! ## Closed object-theory compilation endpoints -/

/-- Variables `0=C`, `1=q`, `2=p`. -/
def programSoundFormula {X Y : Interface} (P : Program X Y) : Fm PTm 3 :=
  queryAt P.guard (var 1) (var 2) ⟶ queryAt (allOf P.residuals) (var 1) (var 2) ⟶
    (ap3 P.verifierF (var 0) (var 1) (var 2) ≐ one) ⟶
      valid Y (ap3 P.transformF (var 0) (var 1) (var 2)) (var 1) (var 2)

theorem acyclic_program_soundness {X Y : Interface} (P : Program X Y) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 (programSoundFormula P) :=
  closeUniv 3 (.impI (.impI (.impI (P.sound _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

/-- Variables `0=C`, `1=C'`, `2=q`, `3=p`. -/
def programStabilityFormula {X Y : Interface} (P : Program X Y) : Fm PTm 4 :=
  queryAt P.guard (var 2) (var 3) ⟶ queryAt (allOf P.residuals) (var 2) (var 3) ⟶
    (ap3 P.verifierF (var 0) (var 2) (var 3) ≐ one) ⟶
    (ap3 P.verifierF (var 1) (var 2) (var 3) ≐ one) ⟶
    masterRelated X (ap2 P.demandF (var 2) (var 3)) (var 0) (var 1) (var 3) ⟶
      (ap4 Y.related (ap3 P.observationF (var 0) (var 2) (var 3))
        (ap3 P.observationF (var 1) (var 2) (var 3)) (var 2) (var 3) ≐ one)

theorem acyclic_program_stability {X Y : Interface} (P : Program X Y) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4 (programStabilityFormula P) :=
  closeUniv 4 (.impI (.impI (.impI (.impI (.impI
    (P.stable _ _ _ _ hyp2.wk.wk hyp2.wk hyp2 Prf.hyp1 Prf.hyp0))))))

/-- Variables `0=q`, `1=p`. -/
def programSealedFormula {X Y : Interface} (P : Program X Y) : Fm PTm 2 :=
  queryAt P.guard (var 0) (var 1) ⟶ queryAt (allOf P.residuals) (var 0) (var 1) ⟶
    P.inputTotal (var 0) (var 1) ⟶ outputTotal Y (var 0) (var 1)

theorem acyclic_program_sealed {X Y : Interface} (P : Program X Y) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 (programSealedFormula P) :=
  closeUniv 2 (.impI (.impI (.impI (P.seal _ _ hyp2 Prf.hyp1 Prf.hyp0))))

/-- Variables `0=C`, `1=q`, `2=p`. -/
def programMetadataFormula {X Y : Interface} (P : Program X Y) : Fm PTm 3 :=
  (ap2 P.boundF (var 1) (var 2) ≐ masterBound X (ap2 P.demandF (var 1) (var 2)) (var 2)) ⋏
    ((ap3 P.verifierF (var 0) (var 1) (var 2) ≐ masterBit X
      (ap2 P.demandF (var 1) (var 2)) (var 0) (var 2)) ⋏
      (ap3 P.observationF (var 0) (var 1) (var 2) ≐
        ap3 Y.observe (ap3 P.transformF (var 0) (var 1) (var 2)) (var 1) (var 2)))

theorem acyclic_program_metadata {X Y : Interface} (P : Program X Y) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 (programMetadataFormula P) := by
  simpa only [metadataFormula, programMetadataFormula, P.compile_bound, P.compile_verifier,
    P.compile_observation, P.compile_demand, P.compile_transform] using realizer_program_metadata P.compile

theorem acyclic_program_verifier {X Y : Interface} (P : Program X Y) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (((ap3 P.verifierF (var 0) (var 1) (var 2) ≐ zero) ⋎
          (ap3 P.verifierF (var 0) (var 1) (var 2) ≐ one)) ⋏
        (((ap3 P.verifierF (var 0) (var 1) (var 2) ≐ one) ⟶
            masterValid X (ap2 P.demandF (var 1) (var 2)) (var 0) (var 2)) ⋏
          (masterValid X (ap2 P.demandF (var 1) (var 2)) (var 0) (var 2) ⟶
            (ap3 P.verifierF (var 0) (var 1) (var 2) ≐ one)))) := by
  simpa only [verifierFormula, P.compile_verifier, P.compile_demand] using bounded_master_verifier P.compile

/-- Variables `0=C`, `1=q`, `2=p`. -/
def sequentialProgramsFormula (R S : Code) : Fm PTm 3 :=
  (ap2 (R.seqDemand S) (var 1) (var 2) ≐ flatMap R.demand (ap2 S.demand (var 1) (var 2)) (var 2)) ⋏
    (ap3 (R.seqTransform S) (var 0) (var 1) (var 2) ≐
      ap3 S.transform (R.bundle (var 0) (ap2 S.demand (var 1) (var 2)) (var 2)) (var 1) (var 2))

theorem source_sequential_programs (R S : Code) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 (sequentialProgramsFormula R S) :=
  closeUniv 3 (.andI (R.seqDemand_at S _ _) (R.seqTransform_at S _ _ _))

/-- Variables `0=C`, `1=q`, `2=p`. -/
def branchProgramsFormula (test : PR 2) (L R : Code) : Fm PTm 3 :=
  ((bit test (var 1) (var 2) ≐ zero) ⟶
    ((ap2 (Code.branchDemand test L R) (var 1) (var 2) ≐ ap2 L.demand (var 1) (var 2)) ⋏
      (ap3 (Code.branchTransform test L R) (var 0) (var 1) (var 2) ≐ ap3 L.transform (var 0) (var 1) (var 2)))) ⋏
  ((bit test (var 1) (var 2) ≐ one) ⟶
    ((ap2 (Code.branchDemand test L R) (var 1) (var 2) ≐ ap2 R.demand (var 1) (var 2)) ⋏
      (ap3 (Code.branchTransform test L R) (var 0) (var 1) (var 2) ≐ ap3 R.transform (var 0) (var 1) (var 2))))

theorem source_branch_programs (test : PR 2) (L R : Code) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 (branchProgramsFormula test L R) :=
  closeUniv 3 (.andI
    (.impI (.andI (branch_demand_zero _ _ _ _ _ Prf.hyp0) (branch_transform_zero _ _ _ _ _ _ Prf.hyp0)))
    (.impI (.andI (branch_demand_one _ _ _ _ _ Prf.hyp0) (branch_transform_one _ _ _ _ _ _ Prf.hyp0))))

/-- Variables `0=q`, `1=p`; the inactive branch requires no producer. -/
def branchScopeFormula (test : PR 2) (L R : Code) : Fm PTm 2 :=
  ((bit test (var 0) (var 1) ≐ zero) ⟶ queryAt L.guard (var 0) (var 1) ⟶
    queryAt (allOf L.residuals) (var 0) (var 1) ⟶
      (queryAt (Code.branch test L R).guard (var 0) (var 1) ⋏
        queryAt (allOf (Code.branch test L R).residuals) (var 0) (var 1))) ⋏
  ((bit test (var 0) (var 1) ≐ one) ⟶ queryAt R.guard (var 0) (var 1) ⟶
    queryAt (allOf R.residuals) (var 0) (var 1) ⟶
      (queryAt (Code.branch test L R).guard (var 0) (var 1) ⋏
        queryAt (allOf (Code.branch test L R).residuals) (var 0) (var 1)))

theorem reached_branch_obligations (test : PR 2) (L R : Code) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 (branchScopeFormula test L R) :=
  closeUniv 2 (.andI
    (.impI (.impI (.impI (branch_scope_zero _ _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))
    (.impI (.impI (.impI (branch_scope_one _ _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0)))))

/-! ## Literal client sequents retain each computed residual separately -/

def Program.residualContext {X Y : Interface} (P : Program X Y) (q p : PTm n) : List (Fm PTm n) :=
  P.residuals.map (fun A => queryAt A q p)

theorem acyclic_program_sequent {X Y : Interface} (P : Program X Y) (C q p : PTm n) :
    (P.residualContext q p ++ [queryAt P.guard q p, ap3 P.verifierF C q p ≐ one]) ⊢[PRAAx]
      valid Y (ap3 P.transformF C q p) q p := by
  apply P.emit C q p
  · exact .hyp (List.mem_append_right _ (List.mem_cons_self))
  · exact .hyp (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
  · intro A hA
    exact .hyp (List.mem_append_left _ (List.mem_map.mpr ⟨A, hA, rfl⟩))

theorem acyclic_program_sealed_sequent {X Y : Interface} (P : Program X Y) (q p : PTm n) :
    (P.residualContext q p ++ [queryAt P.guard q p, P.inputTotal q p]) ⊢[PRAAx] outputTotal Y q p := by
  apply P.seal q p
  · exact .hyp (List.mem_append_right _ (List.mem_cons_self))
  · apply allOf_at_intro P.residuals ![q, p]
    intro A hA
    exact .hyp (List.mem_append_left _ (List.mem_map.mpr ⟨A, hA, rfl⟩))
  · exact .hyp (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self)))

#print axioms acyclic_program_soundness
#print axioms acyclic_program_stability
#print axioms acyclic_program_sealed
#print axioms acyclic_program_metadata
#print axioms acyclic_program_verifier
#print axioms source_sequential_programs
#print axioms source_branch_programs
#print axioms reached_branch_obligations
#print axioms acyclic_program_sequent
#print axioms acyclic_program_sealed_sequent

end LeanProofs.IPRA.Foundations.RealizerGraph
