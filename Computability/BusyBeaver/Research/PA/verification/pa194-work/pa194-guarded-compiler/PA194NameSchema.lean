import PA194Schematic
import PA194NameForms
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
/-!
# The name formulas as instances of standard schemas

Letters stand for the fixed formulas of the ordinal domain (domain, source equality, order
isomorphism, zero, successor, addition, multiplication) and for up to four value formulas of
terms. The translated name formulas of `PA194NameForms` are instances, in the sense of
`PA194Schematic`, of closed standard formulas over these letters:

* the standard combinators `sNameAll`, `sUniq`, `sExName`, `sEqVal` and the value schemas
  `sZeroV`, `sSuccV`, `sAddV`, `sMulV`;
* their typed internal mirrors `tNameAll`, …, with `instS (sig A) (sX …) = tX …`;
* the identities `(tNameAll A B).val = tr (nameAll s s')` and so on, when the typed formulas
  `A`, `B` have the codes `valBody s`, `valBody s'`.
-/
namespace PA194GuardedCompiler
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher
open PA194FormulaDispatcher PA194Schematic

/-! ### Letters and closed standard formulas -/

/-- The predicate letters. -/
inductive Letter : Type
  | dom | eq | iso | zero | succ | add | mul
  | val (i : Fin 4)

/-- Arities of the letters. -/
def Letter.ar : Letter → ℕ
  | .dom => 1
  | .eq => 2
  | .iso => 2
  | .zero => 1
  | .succ => 2
  | .add => 3
  | .mul => 3
  | .val _ => 1

/-- The language of the letters. -/
abbrev NL : Language := boxL Letter.ar
/-- Standard terms without free variables: bound variables. -/
abbrev ST (n : ℕ) := FirstOrder.Semiterm NL Empty n
/-- Standard formulas without free variables. -/
abbrev SF (n : ℕ) := FirstOrder.Semiformula NL Empty n

def sDom {n : ℕ} (t : ST n) : SF n :=
  FirstOrder.Semiformula.rel (L := NL) (BoxRel.box Letter.dom) ![t]
def sEq {n : ℕ} (t u : ST n) : SF n :=
  FirstOrder.Semiformula.rel (L := NL) (BoxRel.box Letter.eq) ![t,u]
def sIso {n : ℕ} (t u : ST n) : SF n :=
  FirstOrder.Semiformula.rel (L := NL) (BoxRel.box Letter.iso) ![t,u]
def sZero {n : ℕ} (t : ST n) : SF n :=
  FirstOrder.Semiformula.rel (L := NL) (BoxRel.box Letter.zero) ![t]
def sSucc {n : ℕ} (t u : ST n) : SF n :=
  FirstOrder.Semiformula.rel (L := NL) (BoxRel.box Letter.succ) ![t,u]
def sAdd {n : ℕ} (t u w : ST n) : SF n :=
  FirstOrder.Semiformula.rel (L := NL) (BoxRel.box Letter.add) ![t,u,w]
def sMul {n : ℕ} (t u w : ST n) : SF n :=
  FirstOrder.Semiformula.rel (L := NL) (BoxRel.box Letter.mul) ![t,u,w]
/-- The `i`-th value letter at its bound variable. -/
def sLet (i : Fin 4) : SF 1 :=
  FirstOrder.Semiformula.rel (L := NL) (BoxRel.box (Letter.val i)) ![#0]
/-- A formula of arity one at a term. -/
def sAt (W : SF 1) {n : ℕ} (t : ST n) : SF n := W ⇜ ![t]
/-- `v` is a value of the variable `x`. -/
def sVarV {n : ℕ} (v x : ST n) : SF n := sDom v ⋏ sEq v x
/-- `∃v∃w (a ∧ b ∧ Iso(v, w))`. -/
def sEqForm {n : ℕ} (a b : SF (n+2)) : SF n := ∃⁰ ∃⁰ (a ⋏ (b ⋏ sIso #1 #0))
/-- `x = W` under the binder of `x`. -/
def sNameAtom (W : SF 1) : SF 1 := sEqForm (n := 1) (sVarV #1 #2) (sAt W #0)
/-- Every name of `W` is a name of `W'`. -/
def sNameAll (W W' : SF 1) : SF 0 := ∀⁰ (∼(sDom #0) ⋎ (∼(sNameAtom W) ⋎ sNameAtom W'))
/-- `W` has a name. -/
def sExName (W : SF 1) : SF 0 := ∃⁰ (sDom #0 ⋏ sNameAtom W)
/-- Any two names of `W` are equal. -/
def sUniq (W : SF 1) : SF 0 :=
  ∀⁰ (∼(sDom #0) ⋎ (∀⁰ (∼(sDom #0) ⋎
    (∼(sEqForm (n := 2) (sVarV #1 #3) (sAt W #0)) ⋎
      (∼(sEqForm (n := 2) (sVarV #1 #2) (sAt W #0)) ⋎
        sEqForm (n := 2) (sVarV #1 #3) (sVarV #0 #2))))))
/-- The values of `W` and `W'` are isomorphic: the translated equality of two terms. -/
def sEqVal (W W' : SF 1) : SF 0 := sEqForm (n := 0) (sAt W #1) (sAt W' #0)
/-- The value formula of zero. -/
def sZeroV : SF 1 := sDom #0 ⋏ sZero #0
/-- The value formula of a successor. -/
def sSuccV (W : SF 1) : SF 1 := sDom #0 ⋏ (∃⁰ (sAt W #0 ⋏ sSucc #0 #1))
/-- The value formula of a sum. -/
def sAddV (W W' : SF 1) : SF 1 := sDom #0 ⋏ (∃⁰ ∃⁰ (sAt W #1 ⋏ (sAt W' #0 ⋏ sAdd #1 #0 #2)))
/-- The value formula of a product. -/
def sMulV (W W' : SF 1) : SF 1 := sDom #0 ⋏ (∃⁰ ∃⁰ (sAt W #1 ⋏ (sAt W' #0 ⋏ sMul #1 #0 #2)))

section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### Typed internal formulas -/

noncomputable def tDom {n : ℕ} (t : Bootstrapping.Semiterm V SourceL n) :
    Bootstrapping.Semiformula V SourceL n :=
  (⌜(domainTemplate : Semiproposition SourceL 1)⌝ : Bootstrapping.Semiformula V SourceL 1).subst ![t]
noncomputable def tEq {n : ℕ} (t u : Bootstrapping.Semiterm V SourceL n) :
    Bootstrapping.Semiformula V SourceL n :=
  (⌜(equalityTemplate : Semiproposition SourceL 2)⌝ : Bootstrapping.Semiformula V SourceL 2).subst ![t,u]
noncomputable def tIso {n : ℕ} (t u : Bootstrapping.Semiterm V SourceL n) :
    Bootstrapping.Semiformula V SourceL n :=
  (⌜(orderIsoTemplate : Semiproposition SourceL 2)⌝ : Bootstrapping.Semiformula V SourceL 2).subst ![t,u]
noncomputable def tZero {n : ℕ} (t : Bootstrapping.Semiterm V SourceL n) :
    Bootstrapping.Semiformula V SourceL n :=
  (⌜(zeroTemplate : Semiproposition SourceL 1)⌝ : Bootstrapping.Semiformula V SourceL 1).subst ![t]
noncomputable def tSucc {n : ℕ} (t u : Bootstrapping.Semiterm V SourceL n) :
    Bootstrapping.Semiformula V SourceL n :=
  (⌜(successorTemplate : Semiproposition SourceL 2)⌝ : Bootstrapping.Semiformula V SourceL 2).subst ![t,u]
noncomputable def tAdd {n : ℕ} (t u w : Bootstrapping.Semiterm V SourceL n) :
    Bootstrapping.Semiformula V SourceL n :=
  (⌜(additionTemplate : Semiproposition SourceL 3)⌝ : Bootstrapping.Semiformula V SourceL 3).subst ![t,u,w]
noncomputable def tMul {n : ℕ} (t u w : Bootstrapping.Semiterm V SourceL n) :
    Bootstrapping.Semiformula V SourceL n :=
  (⌜(multiplicationTemplate : Semiproposition SourceL 3)⌝ :
    Bootstrapping.Semiformula V SourceL 3).subst ![t,u,w]

@[simp] theorem tDom_val {n : ℕ} (t : Bootstrapping.Semiterm V SourceL n) :
    (tDom t).val = domainCode t.val := by
  simp [tDom, domainCode, templateOne, substs1, Semiformula.quote_def]
@[simp] theorem tEq_val {n : ℕ} (t u : Bootstrapping.Semiterm V SourceL n) :
    (tEq t u).val = equalityCode t.val u.val := by
  simp [tEq, equalityCode, templateTwo, Semiformula.quote_def]
@[simp] theorem tIso_val {n : ℕ} (t u : Bootstrapping.Semiterm V SourceL n) :
    (tIso t u).val = orderIsoCode t.val u.val := by
  simp [tIso, orderIsoCode, templateTwo, Semiformula.quote_def]
@[simp] theorem tZero_val {n : ℕ} (t : Bootstrapping.Semiterm V SourceL n) :
    (tZero t).val = zeroCode t.val := by
  simp [tZero, zeroCode, templateOne, substs1, Semiformula.quote_def]
@[simp] theorem tSucc_val {n : ℕ} (t u : Bootstrapping.Semiterm V SourceL n) :
    (tSucc t u).val = successorCode t.val u.val := by
  simp [tSucc, successorCode, templateTwo, Semiformula.quote_def]
@[simp] theorem tAdd_val {n : ℕ} (t u w : Bootstrapping.Semiterm V SourceL n) :
    (tAdd t u w).val = templateThree additionTemplate t.val u.val w.val := by
  simp [tAdd, templateThree, Semiformula.quote_def]
@[simp] theorem tMul_val {n : ℕ} (t u w : Bootstrapping.Semiterm V SourceL n) :
    (tMul t u w).val = templateThree multiplicationTemplate t.val u.val w.val := by
  simp [tMul, templateThree, Semiformula.quote_def]

noncomputable def tVarV {n : ℕ} (v x : Bootstrapping.Semiterm V SourceL n) :
    Bootstrapping.Semiformula V SourceL n := tDom v ⋏ tEq v x
noncomputable def tEqForm {n : ℕ} (a b : Bootstrapping.Semiformula V SourceL (n+2)) :
    Bootstrapping.Semiformula V SourceL n :=
  ∃⁰ ∃⁰ (a ⋏ (b ⋏ tIso (Bootstrapping.Semiterm.bvar 1) (Bootstrapping.Semiterm.bvar 0)))
noncomputable def tNameAtom (A : Bootstrapping.Semiformula V SourceL 1) :
    Bootstrapping.Semiformula V SourceL 1 :=
  tEqForm (n := 1) (tVarV (Bootstrapping.Semiterm.bvar 1) (Bootstrapping.Semiterm.bvar 2))
    (A.subst ![Bootstrapping.Semiterm.bvar 0])
noncomputable def tNameAll (A B : Bootstrapping.Semiformula V SourceL 1) :
    Bootstrapping.Semiformula V SourceL 0 :=
  ∀⁰ (∼(tDom (Bootstrapping.Semiterm.bvar 0)) ⋎ (∼(tNameAtom A) ⋎ tNameAtom B))
noncomputable def tExName (A : Bootstrapping.Semiformula V SourceL 1) :
    Bootstrapping.Semiformula V SourceL 0 :=
  ∃⁰ (tDom (Bootstrapping.Semiterm.bvar 0) ⋏ tNameAtom A)
noncomputable def tUniq (A : Bootstrapping.Semiformula V SourceL 1) :
    Bootstrapping.Semiformula V SourceL 0 :=
  ∀⁰ (∼(tDom (Bootstrapping.Semiterm.bvar 0)) ⋎ (∀⁰ (∼(tDom (Bootstrapping.Semiterm.bvar 0)) ⋎
    (∼(tEqForm (n := 2) (tVarV (Bootstrapping.Semiterm.bvar 1) (Bootstrapping.Semiterm.bvar 3))
        (A.subst ![Bootstrapping.Semiterm.bvar 0])) ⋎
      (∼(tEqForm (n := 2) (tVarV (Bootstrapping.Semiterm.bvar 1) (Bootstrapping.Semiterm.bvar 2))
          (A.subst ![Bootstrapping.Semiterm.bvar 0])) ⋎
        tEqForm (n := 2) (tVarV (Bootstrapping.Semiterm.bvar 1) (Bootstrapping.Semiterm.bvar 3))
          (tVarV (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.bvar 2)))))))
noncomputable def tEqVal (A B : Bootstrapping.Semiformula V SourceL 1) :
    Bootstrapping.Semiformula V SourceL 0 :=
  tEqForm (n := 0) (A.subst ![Bootstrapping.Semiterm.bvar 1]) (B.subst ![Bootstrapping.Semiterm.bvar 0])
noncomputable def tZeroV : Bootstrapping.Semiformula V SourceL 1 :=
  tDom (Bootstrapping.Semiterm.bvar 0) ⋏ tZero (Bootstrapping.Semiterm.bvar 0)
noncomputable def tSuccV (A : Bootstrapping.Semiformula V SourceL 1) :
    Bootstrapping.Semiformula V SourceL 1 :=
  tDom (Bootstrapping.Semiterm.bvar 0) ⋏ (∃⁰ (A.subst ![Bootstrapping.Semiterm.bvar 0] ⋏
    tSucc (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.bvar 1)))
noncomputable def tAddV (A B : Bootstrapping.Semiformula V SourceL 1) :
    Bootstrapping.Semiformula V SourceL 1 :=
  tDom (Bootstrapping.Semiterm.bvar 0) ⋏ (∃⁰ ∃⁰ (A.subst ![Bootstrapping.Semiterm.bvar 1] ⋏
    (B.subst ![Bootstrapping.Semiterm.bvar 0] ⋏
      tAdd (Bootstrapping.Semiterm.bvar 1) (Bootstrapping.Semiterm.bvar 0)
        (Bootstrapping.Semiterm.bvar 2))))
noncomputable def tMulV (A B : Bootstrapping.Semiformula V SourceL 1) :
    Bootstrapping.Semiformula V SourceL 1 :=
  tDom (Bootstrapping.Semiterm.bvar 0) ⋏ (∃⁰ ∃⁰ (A.subst ![Bootstrapping.Semiterm.bvar 1] ⋏
    (B.subst ![Bootstrapping.Semiterm.bvar 0] ⋏
      tMul (Bootstrapping.Semiterm.bvar 1) (Bootstrapping.Semiterm.bvar 0)
        (Bootstrapping.Semiterm.bvar 2))))

/-! ### The assignment of the letters -/

/-- The fixed letters are the typed quotes of the source templates; the value letters are the
given formulas. -/
noncomputable def sig (A : Fin 4 → Bootstrapping.Semiformula V SourceL 1) :
    (l : Letter) → Bootstrapping.Semiformula V SourceL l.ar
  | .dom => (⌜(domainTemplate : Semiproposition SourceL 1)⌝ : Bootstrapping.Semiformula V SourceL 1)
  | .eq => (⌜(equalityTemplate : Semiproposition SourceL 2)⌝ : Bootstrapping.Semiformula V SourceL 2)
  | .iso => (⌜(orderIsoTemplate : Semiproposition SourceL 2)⌝ : Bootstrapping.Semiformula V SourceL 2)
  | .zero => (⌜(zeroTemplate : Semiproposition SourceL 1)⌝ : Bootstrapping.Semiformula V SourceL 1)
  | .succ => (⌜(successorTemplate : Semiproposition SourceL 2)⌝ : Bootstrapping.Semiformula V SourceL 2)
  | .add => (⌜(additionTemplate : Semiproposition SourceL 3)⌝ : Bootstrapping.Semiformula V SourceL 3)
  | .mul => (⌜(multiplicationTemplate : Semiproposition SourceL 3)⌝ :
      Bootstrapping.Semiformula V SourceL 3)
  | .val i => A i

variable (A : Fin 4 → Bootstrapping.Semiformula V SourceL 1)

@[simp] theorem instS_sDom {n : ℕ} (t : ST n) : instS (sig A) (sDom t) = tDom (tqS t) := by
  unfold sDom tDom
  rw [instS_rel]
  exact congrArg (fun w => (⌜(domainTemplate : Semiproposition SourceL 1)⌝ :
    Bootstrapping.Semiformula V SourceL 1).subst w) (tqS_vec1 t)
@[simp] theorem instS_sZero {n : ℕ} (t : ST n) : instS (sig A) (sZero t) = tZero (tqS t) := by
  unfold sZero tZero
  rw [instS_rel]
  exact congrArg (fun w => (⌜(zeroTemplate : Semiproposition SourceL 1)⌝ :
    Bootstrapping.Semiformula V SourceL 1).subst w) (tqS_vec1 t)
@[simp] theorem instS_sEq {n : ℕ} (t u : ST n) :
    instS (sig A) (sEq t u) = tEq (tqS t) (tqS u) := by
  unfold sEq tEq
  rw [instS_rel]
  exact congrArg (fun w => (⌜(equalityTemplate : Semiproposition SourceL 2)⌝ :
    Bootstrapping.Semiformula V SourceL 2).subst w) (tqS_vec2 t u)
@[simp] theorem instS_sIso {n : ℕ} (t u : ST n) :
    instS (sig A) (sIso t u) = tIso (tqS t) (tqS u) := by
  unfold sIso tIso
  rw [instS_rel]
  exact congrArg (fun w => (⌜(orderIsoTemplate : Semiproposition SourceL 2)⌝ :
    Bootstrapping.Semiformula V SourceL 2).subst w) (tqS_vec2 t u)
@[simp] theorem instS_sSucc {n : ℕ} (t u : ST n) :
    instS (sig A) (sSucc t u) = tSucc (tqS t) (tqS u) := by
  unfold sSucc tSucc
  rw [instS_rel]
  exact congrArg (fun w => (⌜(successorTemplate : Semiproposition SourceL 2)⌝ :
    Bootstrapping.Semiformula V SourceL 2).subst w) (tqS_vec2 t u)
@[simp] theorem instS_sAdd {n : ℕ} (t u w : ST n) :
    instS (sig A) (sAdd t u w) = tAdd (tqS t) (tqS u) (tqS w) := by
  unfold sAdd tAdd
  rw [instS_rel]
  exact congrArg (fun x => (⌜(additionTemplate : Semiproposition SourceL 3)⌝ :
    Bootstrapping.Semiformula V SourceL 3).subst x) (tqS_vec3 t u w)
@[simp] theorem instS_sMul {n : ℕ} (t u w : ST n) :
    instS (sig A) (sMul t u w) = tMul (tqS t) (tqS u) (tqS w) := by
  unfold sMul tMul
  rw [instS_rel]
  exact congrArg (fun x => (⌜(multiplicationTemplate : Semiproposition SourceL 3)⌝ :
    Bootstrapping.Semiformula V SourceL 3).subst x) (tqS_vec3 t u w)
@[simp] theorem instS_sLet (i : Fin 4) : instS (sig A) (sLet i) = A i := by
  unfold sLet
  rw [instS_rel]
  have e := congrArg (fun w => (A i).subst w)
    (tqS_vec1 (V := V) (L := SourceL) (#0 : ST 1))
  exact e.trans (by simp)
@[simp] theorem instS_sAt (W : SF 1) {n : ℕ} (t : ST n) :
    instS (sig A) (sAt W t) = (instS (sig A) W).subst ![tqS t] := by
  unfold sAt
  rw [instS_substs, tqS_vec1]

@[simp] theorem instS_sVarV {n : ℕ} (v x : ST n) :
    instS (sig A) (sVarV v x) = tVarV (tqS v) (tqS x) := by
  simp [sVarV, tVarV]
@[simp] theorem instS_sEqForm {n : ℕ} (a b : SF (n+2)) :
    instS (sig A) (sEqForm a b) = tEqForm (instS (sig A) a) (instS (sig A) b) := by
  simp [sEqForm, tEqForm]
@[simp] theorem instS_sNameAtom (W : SF 1) :
    instS (sig A) (sNameAtom W) = tNameAtom (instS (sig A) W) := by
  simp [sNameAtom, tNameAtom]
@[simp] theorem instS_sNameAll (W W' : SF 1) :
    instS (sig A) (sNameAll W W') = tNameAll (instS (sig A) W) (instS (sig A) W') := by
  simp [sNameAll, tNameAll]
@[simp] theorem instS_sExName (W : SF 1) :
    instS (sig A) (sExName W) = tExName (instS (sig A) W) := by
  simp [sExName, tExName]
@[simp] theorem instS_sUniq (W : SF 1) :
    instS (sig A) (sUniq W) = tUniq (instS (sig A) W) := by
  simp [sUniq, tUniq]
@[simp] theorem instS_sEqVal (W W' : SF 1) :
    instS (sig A) (sEqVal W W') = tEqVal (instS (sig A) W) (instS (sig A) W') := by
  simp [sEqVal, tEqVal]
@[simp] theorem instS_sZeroV : instS (sig A) sZeroV = tZeroV := by
  simp [sZeroV, tZeroV]
@[simp] theorem instS_sSuccV (W : SF 1) :
    instS (sig A) (sSuccV W) = tSuccV (instS (sig A) W) := by
  simp [sSuccV, tSuccV]
@[simp] theorem instS_sAddV (W W' : SF 1) :
    instS (sig A) (sAddV W W') = tAddV (instS (sig A) W) (instS (sig A) W') := by
  simp [sAddV, tAddV]
@[simp] theorem instS_sMulV (W W' : SF 1) :
    instS (sig A) (sMulV W W') = tMulV (instS (sig A) W) (instS (sig A) W') := by
  simp [sMulV, tMulV]

/-! ### Codes of the typed formulas -/

theorem tVarV_val {n : ℕ} (v x : Bootstrapping.Semiterm V SourceL n) :
    (tVarV v x).val = variableValue v.val x.val := by
  simp [tVarV, variableValue]
theorem tEqForm_val {n : ℕ} (a b : Bootstrapping.Semiformula V SourceL (n+2)) :
    (tEqForm a b).val = eqForm a.val b.val := by
  simp [tEqForm, eqForm]
theorem tNameAtom_val (B : Bootstrapping.Semiformula V SourceL 1) :
    (tNameAtom B).val = eqForm (variableValue (^#(1 : V)) (^#(2 : V)))
      (substs1 SourceL (^#(0 : V)) B.val) := by
  simp [tNameAtom, tEqForm_val, tVarV_val, substs1]

/-- The typed formula with the code `valBody s`. -/
noncomputable def valT (s : V) (hs : IsSemiterm PA194PAeq.language 0 s) :
    Bootstrapping.Semiformula V SourceL 1 := ⟨valBody s, by simpa using valBody_valid hs⟩
@[simp] theorem valT_val (s : V) (hs : IsSemiterm PA194PAeq.language 0 s) :
    (valT s hs).val = valBody s := rfl

variable {B C : Bootstrapping.Semiformula V SourceL 1} {s s' : V}

theorem tNameAll_tr (hs : IsSemiterm PA194PAeq.language 0 s)
    (hs' : IsSemiterm PA194PAeq.language 0 s') (hB : B.val = valBody s) (hC : C.val = valBody s') :
    (tNameAll B C).val = tr (nameAll s s') := by
  rw [tr_nameAll hs hs', ← hB, ← hC]
  simp [tNameAll, tNameAtom_val, guardBody]
theorem tExName_tr (hs : IsSemiterm PA194PAeq.language 0 s) (hB : B.val = valBody s) :
    (tExName B).val = tr (exName s) := by
  rw [tr_exName hs, ← hB]
  simp [tExName, tNameAtom_val]
theorem tUniq_tr (hs : IsSemiterm PA194PAeq.language 0 s) (hB : B.val = valBody s) :
    (tUniq B).val = tr (uniq s) := by
  rw [tr_uniq hs, ← hB]
  simp [tUniq, tEqForm_val, tVarV_val, substs1, guardBody]
theorem tEqVal_tr (hs : IsSemiterm PA194PAeq.language 0 s)
    (hs' : IsSemiterm PA194PAeq.language 0 s') (hB : B.val = valBody s) (hC : C.val = valBody s') :
    (tEqVal B C).val = tr (peq s s') := by
  rw [tr_peq hs hs', ← hB, ← hC]
  simp [tEqVal, tEqForm_val, eqForm, substs1]
theorem tZeroV_val : (tZeroV : Bootstrapping.Semiformula V SourceL 1).val = valBody (zeroT : V) := by
  rw [valBody_zero]
  simp [tZeroV, zeroValue]
theorem tSuccV_val (hs : IsSemiterm PA194PAeq.language 0 s) (hB : B.val = valBody s) :
    (tSuccV B).val = valBody (succT s) := by
  rw [valBody_succ hs, ← hB]
  simp [tSuccV, successorValue, substs1]
theorem tAddV_val (hs : IsSemiterm PA194PAeq.language 0 s)
    (hs' : IsSemiterm PA194PAeq.language 0 s') (hB : B.val = valBody s) (hC : C.val = valBody s') :
    (tAddV B C).val = valBody (addT s s') := by
  rw [valBody_add hs hs', ← hB, ← hC]
  simp [tAddV, binaryValue, substs1, one_add_one_eq_two]
theorem tMulV_val (hs : IsSemiterm PA194PAeq.language 0 s)
    (hs' : IsSemiterm PA194PAeq.language 0 s') (hB : B.val = valBody s) (hC : C.val = valBody s') :
    (tMulV B C).val = valBody (mulT s s') := by
  rw [valBody_mul hs hs', ← hB, ← hC]
  simp [tMulV, binaryValue, substs1, one_add_one_eq_two]

#print axioms instS_sNameAll
#print axioms instS_sUniq
#print axioms tNameAll_tr
#print axioms tUniq_tr
#print axioms tExName_tr
#print axioms tEqVal_tr
#print axioms tSuccV_val
#print axioms tAddV_val
end generic
end PA194GuardedCompiler
