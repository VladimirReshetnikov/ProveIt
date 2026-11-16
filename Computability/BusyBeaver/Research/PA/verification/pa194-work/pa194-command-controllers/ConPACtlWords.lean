import Foundation.FirstOrder.Arithmetic.HFS.PRF
import Foundation.FirstOrder.Arithmetic.HFS.Vec
import Foundation.FirstOrder.Arithmetic.Schemata
import BusyBeaver.ZFC.ArithmeticCantor

/-!
# Command words inside a model of `𝗜𝚺₁`

The PA194 scheduler runs words over three commands on a store `⟪t, w, d, h⟫`: `t` is the top
formula, `w` a stack coded by the triangular pairing `cantor`, and `d`, `h` are two caches.
This file executes such words inside an arbitrary model `V` of `𝗜𝚺₁`. A word is an element of
`V`, a Foundation vector of command codes, so its length may be nonstandard.

This is `ConPACommandWords` of `pa194-model-fairness` with the controller as a parameter, in
two fields of `Sem`. `mp : MPKind` says what a successful MP returns: with `b = d + y` it is
`⟪b, cantor 0 w, b, 0⟫` (`push`, the primary PA194 table), `⟪b, w, b, 0⟫` (`top`, PA194N and
PA194H) or `⟪0, w, 0, b⟫` (`cache`, PA194C). `cacheTest : Bool` says whether SHIFT halts on
`h = 1` (PA194C, PA194H) or on `t + h = 1`. `Sem.Halts` is that test, `mpStore` the store
after a successful MP and `Sem.up` the number of stack entries it adds.

The store step `cstep` is a parameter: a `𝚺₁` function of a command code `⟪tag, y, x⟫` and a
store. Its three defining equations enter later as hypotheses.

* `tstep`, `texec`: the tracked executor. A tracked state `⟪σ, δ, f⟫` carries the store `σ`,
  the height `δ` of the stack above the level at which the word started, and a flag `f`:
  `0` running, `1` halted (the halting test of a SHIFT held), `2` underflow (a SHIFT below the
  starting level). Flags `1` and `2` are final.
* Words are stored last command first, so `texec (c ∷ W) τ = tstep c (texec W τ)`.
* `seqApp U W` (`U ⧺ W`) executes `U` and then `W`: `texec_seqApp`.
-/
set_option autoImplicit false
noncomputable section
namespace ConPA.Ctl
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor (cantor first second triangle)

/-- The defining formula of the triangular pairing. -/
abbrev cantorDef : 𝚺₀.Semisentence 3 := SetTheory.BusyBeaver.ZFC.ArithmeticCantor.pairDef
abbrev firstDef : 𝚺₀.Semisentence 2 := SetTheory.BusyBeaver.ZFC.ArithmeticCantor.firstDef
abbrev secondDef : 𝚺₀.Semisentence 2 := SetTheory.BusyBeaver.ZFC.ArithmeticCantor.secondDef

section model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Iterated second projection -/

namespace Drop

def blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y u. y = u”
  succ := .mkSigma “y ih n u. !secondDef y ih”

def construction : PR.Construction V blueprint where
  zero := fun v ↦ v 0
  succ := fun _ _ ih ↦ second ih
  zero_defined := .mk fun v ↦ by simp [blueprint]
  succ_defined := .mk fun v ↦ by simp [blueprint]

end Drop

/-- `drop u j`: the stack `u` without its top `j` entries. -/
def drop (u j : V) : V := Drop.construction.result ![u] j

@[simp] lemma drop_zero (u : V) : drop u 0 = u := by simp [drop, Drop.construction]

@[simp] lemma drop_succ (u j : V) : drop u (j + 1) = second (drop u j) := by
  simp [drop, Drop.construction]

def dropDef : 𝚺₁.Semisentence 3 := Drop.blueprint.resultDef |>.rew (Rew.subst ![#0, #2, #1])

instance drop_defined : 𝚺₁-Function₂ (drop : V → V → V) via dropDef := .mk
  fun v ↦ by simp [Drop.construction.result_defined_iff, dropDef]; rfl

instance drop_definable : 𝚺₁-Function₂ (drop : V → V → V) := drop_defined.to_definable

instance drop_definable' (Γ m) : Γ-[m + 1]-Function₂ (drop : V → V → V) := drop_definable.of_sigmaOne

instance cantor_definable (ℌ : HierarchySymbol) : ℌ-Function₂ (cantor : V → V → V) :=
  (SetTheory.BusyBeaver.ZFC.ArithmeticCantor.cantor_defined (V := V)).to_definable.of_zero

instance first_definable (ℌ : HierarchySymbol) : ℌ-Function₁ (first : V → V) :=
  (SetTheory.BusyBeaver.ZFC.ArithmeticCantor.first_defined (V := V)).to_definable.of_zero

instance second_definable (ℌ : HierarchySymbol) : ℌ-Function₁ (second : V → V) :=
  (SetTheory.BusyBeaver.ZFC.ArithmeticCantor.second_defined (V := V)).to_definable.of_zero

lemma drop_second (u j : V) : drop (second u) j = drop u (j + 1) := by
  induction j using ISigma1.sigma1_succ_induction
  · definability
  case zero => simpa using (drop_succ u 0).symm
  case succ j ih => rw [drop_succ (second u) j, ih, drop_succ u (j + 1)]

@[simp] lemma drop_cantor_succ (x u j : V) : drop (cantor x u) (j + 1) = drop u j := by
  rw [← drop_second]; simp

/-! ## Command semantics -/

/-- The stack after an AX command: eight leaf formulas, a generalization, the old top. -/
def stack10 (f : ℕ → V) (g t w : V) : V :=
  cantor (f 0) (cantor (f 1) (cantor (f 2) (cantor (f 3) (cantor (f 4) (cantor (f 5)
    (cantor (f 6) (cantor (f 7) (cantor g (cantor t w)))))))))

/-- What a successful MP returns, with `b = d + y`: `push` is `⟪b, cantor 0 w, b, 0⟫`, `top` is
`⟪b, w, b, 0⟫`, `cache` is `⟪0, w, 0, b⟫`. -/
inductive MPKind where
  | push
  | top
  | cache
  deriving DecidableEq

/-- The store after a successful MP with consequent `b` on the stack `w`. -/
def mpStore (k : MPKind) (b w : V) : V :=
  match k with
  | .push => ⟪b, cantor 0 w, b, 0⟫
  | .top => ⟪b, w, b, 0⟫
  | .cache => ⟪0, w, 0, b⟫

variable (V) in
/-- The store step of the three commands. A command is `⟪tag, y, x, z⟫`: SHIFT has tag `0`, MP
tag `1` and argument `y`, AX tag `A + 2` and arguments `y`, `x`, and in the eleven-entry
layout also `z`. A store is `⟪t, w, d, h⟫`. -/
structure Sem where
  cstep : V → V → V
  cstepDef : 𝚺₁.Semisentence 3
  cstep_defined : 𝚺₁-Function₂ cstep via cstepDef
  /-- What a successful MP returns. -/
  mp : MPKind
  /-- Whether SHIFT halts on `h = 1` (otherwise on `t + h = 1`). -/
  cacheTest : Bool
  /-- Whether AX pushes its gate as an eleventh stack entry, leaves the top `0` and sets `d`
  to its fourth argument (otherwise the gate is the top and `d` is cleared). -/
  ax11 : Bool
  /-- The top after AX, as a function of `H D A`. -/
  axT : V → V → V → V
  /-- The eight leaf formulas pushed by AX, as functions of `D H A d`. -/
  leaf : ℕ → V → V → V → V → V
  /-- The label of the generalization pushed by AX, as a function of `A d`: the register `d`
  for the binder `U(d, h)`, the argument `A` for the binder `U(c, h)`. -/
  genL : V → V → V
  shift_eq : ∀ y x t w d h : V, cstep ⟪0, y, x⟫ ⟪t, w, d, h⟫ = ⟪h, second w, d, first w⟫
  mp_eq : ∀ y x t w d h : V, cstep ⟪1, y, x⟫ ⟪t, w, d, h⟫ =
    if 4 * cantor t (d + y) = h then mpStore mp (d + y) w else ⟪0, w, d + y, 0⟫
  ax_eq : ∀ A y x z t w d h : V, cstep ⟪A + 1 + 1, y, x, z⟫ ⟪t, w, d, h⟫ =
    if ax11 then
      ⟪0, cantor (axT (h + y) (d + x) A)
        (stack10 (fun i => leaf i (d + x) (h + y) A d) (4 * cantor h (genL A d) + 2) t w), z, 0⟫
    else
      ⟪axT (h + y) (d + x) A,
        stack10 (fun i => leaf i (d + x) (h + y) A d) (4 * cantor h (genL A d) + 2) t w, 0, 0⟫
  axT_ne_one : ∀ H D A : V, axT H D A ≠ 1
  leaf_ne_one : ∀ (i : ℕ) (D H A d : V), leaf i D H A d ≠ 1
  genL_self : ∀ i : V, genL i i = i

attribute [instance] Sem.cstep_defined

/-- The number of stack entries a successful MP adds. -/
def Sem.up (S : Sem V) : ℕ :=
  match S.mp with
  | .push => 1
  | _ => 0

/-- The weight of the top in the halting test of SHIFT: the test is `k * t + h = 1`, which is
`t + h = 1` for `k = 1` and `h = 1` for `k = 0`. -/
def Sem.k (S : Sem V) : ℕ := if S.cacheTest then 0 else 1

/-- The halting test of SHIFT on the top `t` and the cache `h`. -/
def Sem.Halts (S : Sem V) (t h : V) : Prop := (S.k : V) * t + h = 1

/-- The number of stack entries of AX beyond ten: `1` when the gate is pushed. -/
def Sem.g (S : Sem V) : ℕ := if S.ax11 then 1 else 0

/-- The number of stack entries that AX pushes. -/
def Sem.n (S : Sem V) : ℕ := if S.ax11 then 11 else 10

variable (S : Sem V)

/-- One command on a tracked state `⟪σ, δ, f⟫`. -/
def tstep (c τ : V) : V :=
  if π₂ (π₂ τ) = 0 then
    if π₁ c = 0 then
      if (S.k : V) * π₁ (π₁ τ) + π₂ (π₂ (π₂ (π₁ τ))) = 1 then ⟪π₁ τ, π₁ (π₂ τ), 1⟫
      else if π₁ (π₂ τ) = 0 then ⟪π₁ τ, 0, 2⟫
      else ⟪S.cstep c (π₁ τ), π₁ (π₂ τ) - 1, 0⟫
    else if π₁ c = 1 then
      if 4 * cantor (π₁ (π₁ τ)) (π₁ (π₂ (π₂ (π₁ τ))) + π₁ (π₂ c)) = π₂ (π₂ (π₂ (π₁ τ))) then
        ⟪S.cstep c (π₁ τ), π₁ (π₂ τ) + (S.up : V), 0⟫
      else ⟪S.cstep c (π₁ τ), π₁ (π₂ τ), 0⟫
    else ⟪S.cstep c (π₁ τ), π₁ (π₂ τ) + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + (S.g : V), 0⟫
  else τ

def tstepDef (k up g : ℕ) (cstepDef : 𝚺₁.Semisentence 3) : 𝚺₁.Semisentence 3 :=
  .mkSigma “tn c tau. ∃ s, !pi₁Def s tau ∧ ∃ r, !pi₂Def r tau ∧ ∃ dl, !pi₁Def dl r ∧
    ∃ f, !pi₂Def f r ∧ ∃ tag, !pi₁Def tag c ∧ ∃ t, !pi₁Def t s ∧ ∃ s2, !pi₂Def s2 s ∧
    ∃ s3, !pi₂Def s3 s2 ∧ ∃ d, !pi₁Def d s3 ∧ ∃ h, !pi₂Def h s3 ∧ ∃ c2, !pi₂Def c2 c ∧
    ∃ y, !pi₁Def y c2 ∧ ∃ sn, !cstepDef sn c s ∧ ∃ p, !cantorDef p t (d + y) ∧
    ((f ≠ 0 ∧ tn = tau) ∨
     (f = 0 ∧ tag = 0 ∧ ↑k * t + h = 1 ∧ !pair₃Def tn s dl 1) ∨
     (f = 0 ∧ tag = 0 ∧ ↑k * t + h ≠ 1 ∧ dl = 0 ∧ !pair₃Def tn s 0 2) ∨
     (f = 0 ∧ tag = 0 ∧ ↑k * t + h ≠ 1 ∧ dl ≠ 0 ∧ ∃ dp, !subDef dp dl 1 ∧ !pair₃Def tn sn dp 0) ∨
     (f = 0 ∧ tag = 1 ∧ 4 * p = h ∧ !pair₃Def tn sn (dl + ↑up) 0) ∨
     (f = 0 ∧ tag = 1 ∧ 4 * p ≠ h ∧ !pair₃Def tn sn dl 0) ∨
     (f = 0 ∧ tag ≠ 0 ∧ tag ≠ 1 ∧
       !pair₃Def tn sn (dl + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + ↑g) 0))”

lemma tstepDef_iff (tn c τ : V) :
    (tstepDef S.k S.up S.g S.cstepDef).val.Evalb ![tn, c, τ] ↔ tn = tstep S c τ := by
  unfold tstep
  by_cases hf : π₂ (π₂ τ) = 0
  · by_cases h0 : π₁ c = 0
    · by_cases hh : (S.k : V) * π₁ (π₁ τ) + π₂ (π₂ (π₂ (π₁ τ))) = 1
      · simp [tstepDef, hf, h0, hh, numeral_eq_natCast]
      · by_cases hd : π₁ (π₂ τ) = 0
        · simp [tstepDef, hf, h0, hh, hd, numeral_eq_natCast]
        · simp [tstepDef, hf, h0, hh, hd, numeral_eq_natCast]
    · by_cases h1 : π₁ c = 1
      · by_cases hm : 4 * cantor (π₁ (π₁ τ)) (π₁ (π₂ (π₂ (π₁ τ))) + π₁ (π₂ c)) =
            π₂ (π₂ (π₂ (π₁ τ)))
        · simp [tstepDef, hf, h1, hm, numeral_eq_natCast]
        · simp [tstepDef, hf, h1, hm]
      · simp [tstepDef, hf, h0, h1, numeral_eq_natCast]
  · simp [tstepDef, hf]

/-! ## The executor -/

namespace Exec

def blueprint (k up g : ℕ) (cstepDef : 𝚺₁.Semisentence 3) : VecRec.Blueprint 1 where
  nil := .mkSigma “y tau. y = tau”
  adjoin := .mkSigma “y x xs ih tau. !(tstepDef k up g cstepDef) y x ih”

def construction : VecRec.Construction V (blueprint S.k S.up S.g S.cstepDef) where
  nil := fun v ↦ v 0
  adjoin := fun _ x _ ih ↦ tstep S x ih
  nil_defined := .mk fun v ↦ by simp [blueprint]
  adjoin_defined := .mk fun v ↦ by simp [blueprint, tstepDef_iff]

end Exec

/-- The tracked state after the word `W` (last command first) from `τ`. -/
def texec (W τ : V) : V := (Exec.construction S).result ![τ] W

@[simp] lemma texec_nil (τ : V) : texec S 0 τ = τ := by simp [texec, Exec.construction]

@[simp] lemma texec_adjoin (c W τ : V) : texec S (c ∷ W) τ = tstep S c (texec S W τ) := by
  simp [texec, Exec.construction]

def texecDef (k up g : ℕ) (cstepDef : 𝚺₁.Semisentence 3) : 𝚺₁.Semisentence 3 :=
  (Exec.blueprint k up g cstepDef).resultDef

instance texec_defined : 𝚺₁-Function₂ (texec S) via texecDef S.k S.up S.g S.cstepDef :=
  (Exec.construction S).result_defined

instance texec_definable : 𝚺₁-Function₂ (texec S) := (texec_defined S).to_definable

instance texec_definable' (Γ m) : Γ-[m + 1]-Function₂ (texec S) := (texec_definable S).of_sigmaOne

/-! ## Concatenation -/

namespace App

def blueprint : VecRec.Blueprint 1 where
  nil := .mkSigma “y u. y = u”
  adjoin := .mkSigma “y x xs ih u. !adjoinDef y x ih”

def construction : VecRec.Construction V blueprint where
  nil := fun v ↦ v 0
  adjoin := fun _ x _ ih ↦ x ∷ ih
  nil_defined := .mk fun v ↦ by simp [blueprint]
  adjoin_defined := .mk fun v ↦ by simp [blueprint]

end App

/-- The word `U` followed by the word `W`. -/
def seqApp (U W : V) : V := App.construction.result ![U] W

scoped infixl:65 " ⧺ " => seqApp

@[simp] lemma seqApp_nil (U : V) : U ⧺ (0 : V) = U := by simp [seqApp, App.construction]

@[simp] lemma seqApp_adjoin (U c W : V) : U ⧺ (c ∷ W) = c ∷ (U ⧺ W) := by
  simp [seqApp, App.construction]

def seqAppDef : 𝚺₁.Semisentence 3 := App.blueprint.resultDef |>.rew (Rew.subst ![#0, #2, #1])

instance seqApp_defined : 𝚺₁-Function₂ (seqApp : V → V → V) via seqAppDef := .mk
  fun v ↦ by simp [(App.construction (V := V)).eval_resultDef, seqAppDef]; rfl

instance seqApp_definable : 𝚺₁-Function₂ (seqApp : V → V → V) := seqApp_defined.to_definable

instance seqApp_definable' (Γ m) : Γ-[m + 1]-Function₂ (seqApp : V → V → V) :=
  seqApp_definable.of_sigmaOne

lemma texec_seqApp (U W τ : V) : texec S (U ⧺ W) τ = texec S W (texec S U τ) := by
  induction W using adjoin_ISigma1.sigma1_succ_induction
  · definability
  case nil => simp
  case adjoin c W ih => simp [ih]

@[simp] lemma len_seqApp (U W : V) : len (U ⧺ W) = len U + len W := by
  induction W using adjoin_ISigma1.sigma1_succ_induction
  · definability
  case nil => simp
  case adjoin c W ih => simp [ih, add_assoc]

end model
end ConPA.Ctl
