import PA194NameSchema
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
/-!
# Truth of the name schemas in an arbitrary structure

For a structure `M` of the language of the letters, the letters are relations on `M` and each
closed standard schema of `PA194NameSchema` has an explicit meaning: `ev_sNameAll` and so on.
The facts about names are then ordinary statements about relations on a set.
-/
namespace PA194GuardedCompiler
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PA194Schematic

section semantics
variable {M : Type} [s : Structure NL M]

def mD (x : M) : Prop := s.rel (BoxRel.box Letter.dom) ![x]
def mE (x y : M) : Prop := s.rel (BoxRel.box Letter.eq) ![x,y]
def mI (x y : M) : Prop := s.rel (BoxRel.box Letter.iso) ![x,y]
def mZ (x : M) : Prop := s.rel (BoxRel.box Letter.zero) ![x]
def mS (x y : M) : Prop := s.rel (BoxRel.box Letter.succ) ![x,y]
def mA (x y z : M) : Prop := s.rel (BoxRel.box Letter.add) ![x,y,z]
def mMu (x y z : M) : Prop := s.rel (BoxRel.box Letter.mul) ![x,y,z]
def mL (i : Fin 4) (x : M) : Prop := s.rel (BoxRel.box (Letter.val i)) ![x]

/-- Truth of a closed formula at values of its bound variables. -/
abbrev ev {n : ℕ} (b : Fin n → M) (φ : SF n) : Prop :=
  FirstOrder.Semiformula.Eval (s := s) b Empty.elim φ
/-- The value of a bound variable. -/
abbrev tv {n : ℕ} (b : Fin n → M) (t : ST n) : M :=
  FirstOrder.Semiterm.val (s := s) b Empty.elim t
/-- The set defined by a closed formula of arity one. -/
def wOf (W : SF 1) (x : M) : Prop := ev ![x] W

theorem cv1 {α β : Type} (f : α → β) (a : α) : (f ∘ (![a] : Fin 1 → α)) = ![f a] := by
  funext j
  have hj : j = 0 := Subsingleton.elim _ _
  subst hj
  rfl
theorem cv2 {α β : Type} (f : α → β) (a b : α) :
    (f ∘ (![a,b] : Fin 2 → α)) = ![f a, f b] := by
  funext j
  cases j using Fin.cases with
  | zero => rfl
  | succ j =>
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    rfl
theorem cv3 {α β : Type} (f : α → β) (a b c : α) :
    (f ∘ (![a,b,c] : Fin 3 → α)) = ![f a, f b, f c] := by
  funext j
  cases j using Fin.cases with
  | zero => rfl
  | succ j =>
    cases j using Fin.cases with
    | zero => rfl
    | succ j =>
      have hj : j = 0 := Subsingleton.elim _ _
      subst hj
      rfl

@[simp] theorem ev_sDom {n : ℕ} (b : Fin n → M) (t : ST n) : ev b (sDom t) ↔ mD (tv b t) :=
  iff_of_eq (congrArg (s.rel (BoxRel.box Letter.dom))
    (cv1 (FirstOrder.Semiterm.val (s := s) b Empty.elim) t))
@[simp] theorem ev_sZero {n : ℕ} (b : Fin n → M) (t : ST n) : ev b (sZero t) ↔ mZ (tv b t) :=
  iff_of_eq (congrArg (s.rel (BoxRel.box Letter.zero))
    (cv1 (FirstOrder.Semiterm.val (s := s) b Empty.elim) t))
@[simp] theorem ev_sEq {n : ℕ} (b : Fin n → M) (t u : ST n) :
    ev b (sEq t u) ↔ mE (tv b t) (tv b u) :=
  iff_of_eq (congrArg (s.rel (BoxRel.box Letter.eq))
    (cv2 (FirstOrder.Semiterm.val (s := s) b Empty.elim) t u))
@[simp] theorem ev_sIso {n : ℕ} (b : Fin n → M) (t u : ST n) :
    ev b (sIso t u) ↔ mI (tv b t) (tv b u) :=
  iff_of_eq (congrArg (s.rel (BoxRel.box Letter.iso))
    (cv2 (FirstOrder.Semiterm.val (s := s) b Empty.elim) t u))
@[simp] theorem ev_sSucc {n : ℕ} (b : Fin n → M) (t u : ST n) :
    ev b (sSucc t u) ↔ mS (tv b t) (tv b u) :=
  iff_of_eq (congrArg (s.rel (BoxRel.box Letter.succ))
    (cv2 (FirstOrder.Semiterm.val (s := s) b Empty.elim) t u))
@[simp] theorem ev_sAdd {n : ℕ} (b : Fin n → M) (t u w : ST n) :
    ev b (sAdd t u w) ↔ mA (tv b t) (tv b u) (tv b w) :=
  iff_of_eq (congrArg (s.rel (BoxRel.box Letter.add))
    (cv3 (FirstOrder.Semiterm.val (s := s) b Empty.elim) t u w))
@[simp] theorem ev_sMul {n : ℕ} (b : Fin n → M) (t u w : ST n) :
    ev b (sMul t u w) ↔ mMu (tv b t) (tv b u) (tv b w) :=
  iff_of_eq (congrArg (s.rel (BoxRel.box Letter.mul))
    (cv3 (FirstOrder.Semiterm.val (s := s) b Empty.elim) t u w))
@[simp] theorem wOf_sLet (i : Fin 4) (x : M) : wOf (sLet i) x ↔ mL i x :=
  iff_of_eq (congrArg (s.rel (BoxRel.box (Letter.val i)))
    (cv1 (FirstOrder.Semiterm.val (s := s) ![x] Empty.elim) (#0 : ST 1)))
@[simp] theorem ev_sAt (W : SF 1) {n : ℕ} (b : Fin n → M) (t : ST n) :
    ev b (sAt W t) ↔ wOf W (tv b t) := by
  unfold sAt wOf
  have h : ev b (W ⇜ (![t] : Fin 1 → ST n)) ↔ _ :=
    FirstOrder.Semiformula.eval_substs _ _
  rw [cv1] at h
  exact h

/-! ### Meanings of the schemas -/

/-- `v` is a value of the variable `x`. -/
def mVarV (v x : M) : Prop := mD v ∧ mE v x
/-- `x` is a name of `P`: some value of `x` is isomorphic to a member of `P`. -/
def mName (P : M → Prop) (x : M) : Prop := ∃ v w : M, mVarV v x ∧ P w ∧ mI v w
def mNameAll (P Q : M → Prop) : Prop := ∀ x : M, mD x → mName P x → mName Q x
def mExName (P : M → Prop) : Prop := ∃ x : M, mD x ∧ mName P x
/-- The variables `x` and `y` have isomorphic values. -/
def mEq2 (x y : M) : Prop := ∃ v w : M, mVarV v x ∧ mVarV w y ∧ mI v w
def mUniq (P : M → Prop) : Prop :=
  ∀ x : M, mD x → ∀ y : M, mD y → mName P x → mName P y → mEq2 x y
def mEqVal (P Q : M → Prop) : Prop := ∃ v w : M, P v ∧ Q w ∧ mI v w
def mZeroV (x : M) : Prop := mD x ∧ mZ x
def mSuccV (P : M → Prop) (x : M) : Prop := mD x ∧ ∃ u : M, P u ∧ mS u x
def mAddV (P Q : M → Prop) (x : M) : Prop := mD x ∧ ∃ u u' : M, P u ∧ Q u' ∧ mA u u' x
def mMulV (P Q : M → Prop) (x : M) : Prop := mD x ∧ ∃ u u' : M, P u ∧ Q u' ∧ mMu u u' x

theorem wOf_sNameAtom (W : SF 1) (x : M) : wOf (sNameAtom W) x ↔ mName (wOf W) x := by
  simp [wOf, sNameAtom, sEqForm, sVarV, mName, mVarV]
theorem ev_sNameAll (W W' : SF 1) :
    ev (![] : Fin 0 → M) (sNameAll W W') ↔ mNameAll (M := M) (wOf W) (wOf W') := by
  have h : ∀ (W : SF 1) (x : M), ev ![x] (sNameAtom W) ↔ mName (wOf W) x := wOf_sNameAtom
  simp only [sNameAll, mNameAll, FirstOrder.Semiformula.eval_all, LogicalConnective.HomClass.map_or,
    LogicalConnective.HomClass.map_neg, ev_sDom, h, FirstOrder.Semiterm.val_bvar,
    Matrix.cons_val_zero, LogicalConnective.Prop.or_eq, LogicalConnective.Prop.neg_eq]
  exact forall_congr' fun x => by tauto
theorem ev_sExName (W : SF 1) : ev (![] : Fin 0 → M) (sExName W) ↔ mExName (M := M) (wOf W) := by
  have h : ∀ (W : SF 1) (x : M), ev ![x] (sNameAtom W) ↔ mName (wOf W) x := wOf_sNameAtom
  simp [sExName, mExName, h]
theorem ev_name2o (W : SF 1) (x y : M) :
    ev ![y, x] (sEqForm (n := 2) (sVarV #1 #3) (sAt W #0)) ↔ mName (wOf W) x := by
  simp [sEqForm, sVarV, mName, mVarV]
theorem ev_name2i (W : SF 1) (x y : M) :
    ev ![y, x] (sEqForm (n := 2) (sVarV #1 #2) (sAt W #0)) ↔ mName (wOf W) y := by
  simp [sEqForm, sVarV, mName, mVarV]
theorem ev_eq2 (x y : M) :
    ev ![y, x] (sEqForm (n := 2) (sVarV #1 #3) (sVarV #0 #2)) ↔ mEq2 x y := by
  simp [sEqForm, sVarV, mEq2, mVarV]
theorem uniq_shape {D N E : M → Prop} {Dx Nx : Prop} :
    (¬Dx ∨ ∀ y, ¬D y ∨ ¬Nx ∨ ¬N y ∨ E y) ↔ (Dx → ∀ y, D y → Nx → N y → E y) := by
  constructor
  · intro h hx y hy a b
    rcases h with h | h
    · exact absurd hx h
    · rcases h y with h | h | h | h
      · exact absurd hy h
      · exact absurd a h
      · exact absurd b h
      · exact h
  · intro h
    by_cases hx : Dx
    · right
      intro y
      by_cases hy : D y
      · by_cases a : Nx
        · by_cases b : N y
          · exact Or.inr (Or.inr (Or.inr (h hx y hy a b)))
          · exact Or.inr (Or.inr (Or.inl b))
        · exact Or.inr (Or.inl a)
      · exact Or.inl hy
    · exact Or.inl hx
theorem ev_sUniq (W : SF 1) : ev (![] : Fin 0 → M) (sUniq W) ↔ mUniq (M := M) (wOf W) := by
  have h1 : ∀ x y : M, ev ![y, x] (sEqForm (n := 2) (sVarV #1 #3) (sAt W #0)) ↔
      mName (wOf W) x := ev_name2o W
  have h2 : ∀ x y : M, ev ![y, x] (sEqForm (n := 2) (sVarV #1 #2) (sAt W #0)) ↔
      mName (wOf W) y := ev_name2i W
  have h3 : ∀ x y : M, ev ![y, x] (sEqForm (n := 2) (sVarV #1 #3) (sVarV #0 #2)) ↔
      mEq2 x y := ev_eq2
  simp only [sUniq, mUniq, FirstOrder.Semiformula.eval_all, LogicalConnective.HomClass.map_or,
    LogicalConnective.HomClass.map_neg, ev_sDom, h1, h2, h3, FirstOrder.Semiterm.val_bvar,
    Matrix.cons_val_zero, LogicalConnective.Prop.or_eq, LogicalConnective.Prop.neg_eq]
  exact forall_congr' fun x => uniq_shape
theorem ev_sEqVal (W W' : SF 1) :
    ev (![] : Fin 0 → M) (sEqVal W W') ↔ mEqVal (M := M) (wOf W) (wOf W') := by
  simp [sEqVal, sEqForm, mEqVal]
theorem wOf_sZeroV (x : M) : wOf sZeroV x ↔ mZeroV x := by
  simp [wOf, sZeroV, mZeroV]
theorem wOf_sSuccV (W : SF 1) (x : M) : wOf (sSuccV W) x ↔ mSuccV (wOf W) x := by
  simp [wOf, sSuccV, mSuccV]
theorem wOf_sAddV (W W' : SF 1) (x : M) : wOf (sAddV W W') x ↔ mAddV (wOf W) (wOf W') x := by
  simp [wOf, sAddV, mAddV]
theorem wOf_sMulV (W W' : SF 1) (x : M) : wOf (sMulV W W') x ↔ mMulV (wOf W) (wOf W') x := by
  simp [wOf, sMulV, mMulV]

theorem ev_imp {n : ℕ} (b : Fin n → M) (φ ψ : SF n) : ev b (φ 🡒 ψ) ↔ (ev b φ → ev b ψ) := by
  simp

theorem wOf_sSuccV' (W : SF 1) : wOf (M := M) (sSuccV W) = mSuccV (wOf W) :=
  funext fun x => propext (wOf_sSuccV W x)
theorem wOf_sAddV' (W W' : SF 1) : wOf (M := M) (sAddV W W') = mAddV (wOf W) (wOf W') :=
  funext fun x => propext (wOf_sAddV W W' x)
theorem wOf_sMulV' (W W' : SF 1) : wOf (M := M) (sMulV W W') = mMulV (wOf W) (wOf W') :=
  funext fun x => propext (wOf_sMulV W W' x)
theorem wOf_sZeroV' : wOf (M := M) sZeroV = mZeroV :=
  funext fun x => propext (wOf_sZeroV x)

end semantics

/-! ### Value formulas with their domain conjunct, and the fixed hypotheses -/

/-- A value formula whose part after the domain conjunct is the `i`-th value letter. -/
def sBox (i : Fin 4) : SF 1 := sDom #0 ⋏ sLet i
/-- Any two members of the domain that satisfy the `i`-th value letter are isomorphic. -/
def sPair (i : Fin 4) : SF 0 :=
  ∀⁰ ∀⁰ (sDom #1 🡒 sDom #0 🡒 sAt (sLet i) #1 🡒 sAt (sLet i) #0 🡒 sIso #1 #0)

/-- Source equality is reflexive. -/
def sE1 : SF 0 := ∀⁰ (sEq #0 #0)
/-- Two members of the domain equal to the same thing are isomorphic. -/
def sEI : SF 0 := ∀⁰ ∀⁰ ∀⁰ (sDom #1 🡒 sDom #0 🡒 sEq #1 #2 🡒 sEq #0 #2 🡒 sIso #1 #0)
/-- Order isomorphism is symmetric on the domain. -/
def sIs : SF 0 := ∀⁰ ∀⁰ (sDom #1 🡒 sDom #0 🡒 sIso #1 #0 🡒 sIso #0 #1)
/-- Order isomorphism is transitive on the domain. -/
def sIt : SF 0 :=
  ∀⁰ ∀⁰ ∀⁰ (sDom #2 🡒 sDom #1 🡒 sDom #0 🡒 sIso #2 #1 🡒 sIso #1 #0 🡒 sIso #2 #0)
/-- The domain has a zero. -/
def sZ1 : SF 0 := ∃⁰ (sDom #0 ⋏ sZero #0)
/-- Any two zeros of the domain are isomorphic. -/
def sZ2 : SF 0 := ∀⁰ ∀⁰ (sDom #1 🡒 sZero #1 🡒 sDom #0 🡒 sZero #0 🡒 sIso #1 #0)
/-- Every member of the domain has a successor in the domain. -/
def sS1 : SF 0 := ∀⁰ (sDom #0 🡒 (∃⁰ (sDom #0 ⋏ sSucc #1 #0)))
/-- Successors of isomorphic members are isomorphic. -/
def sS2 : SF 0 :=
  ∀⁰ ∀⁰ ∀⁰ ∀⁰ (sDom #3 🡒 sDom #2 🡒 sDom #1 🡒 sDom #0 🡒 sSucc #3 #2 🡒 sSucc #1 #0 🡒
    sIso #3 #1 🡒 sIso #2 #0)
/-- Any two members of the domain have a sum in the domain. -/
def sA1 : SF 0 := ∀⁰ ∀⁰ (sDom #1 🡒 sDom #0 🡒 (∃⁰ (sDom #0 ⋏ sAdd #2 #1 #0)))
/-- Sums of isomorphic members are isomorphic. -/
def sA2 : SF 0 :=
  ∀⁰ ∀⁰ ∀⁰ ∀⁰ ∀⁰ ∀⁰ (sDom #5 🡒 sDom #4 🡒 sDom #3 🡒 sDom #2 🡒 sDom #1 🡒 sDom #0 🡒
    sAdd #5 #4 #3 🡒 sAdd #2 #1 #0 🡒 sIso #5 #2 🡒 sIso #4 #1 🡒 sIso #3 #0)
/-- Any two members of the domain have a product in the domain. -/
def sM1 : SF 0 := ∀⁰ ∀⁰ (sDom #1 🡒 sDom #0 🡒 (∃⁰ (sDom #0 ⋏ sMul #2 #1 #0)))
/-- Products of isomorphic members are isomorphic. -/
def sM2 : SF 0 :=
  ∀⁰ ∀⁰ ∀⁰ ∀⁰ ∀⁰ ∀⁰ (sDom #5 🡒 sDom #4 🡒 sDom #3 🡒 sDom #2 🡒 sDom #1 🡒 sDom #0 🡒
    sMul #5 #4 #3 🡒 sMul #2 #1 #0 🡒 sIso #5 #2 🡒 sIso #4 #1 🡒 sIso #3 #0)

/-- A sentence under the twelve fixed hypotheses. -/
def sWith (F : SF 0) : SF 0 :=
  sE1 🡒 sEI 🡒 sIs 🡒 sIt 🡒 sZ1 🡒 sZ2 🡒 sS1 🡒 sS2 🡒 sA1 🡒 sA2 🡒 sM1 🡒 sM2 🡒 F

section semantics2
variable {M : Type} [s : Structure NL M]

/-- The twelve fixed hypotheses in a structure. -/
structure MTheta (M : Type) [s : Structure NL M] : Prop where
  e1 : ∀ x : M, mE x x
  ei : ∀ x a b : M, mD a → mD b → mE a x → mE b x → mI a b
  is : ∀ a b : M, mD a → mD b → mI a b → mI b a
  it : ∀ a b c : M, mD a → mD b → mD c → mI a b → mI b c → mI a c
  z1 : ∃ z : M, mD z ∧ mZ z
  z2 : ∀ a b : M, mD a → mZ a → mD b → mZ b → mI a b
  s1 : ∀ u : M, mD u → ∃ w : M, mD w ∧ mS u w
  s2 : ∀ u w u' w' : M, mD u → mD w → mD u' → mD w' → mS u w → mS u' w' → mI u u' → mI w w'
  a1 : ∀ u u' : M, mD u → mD u' → ∃ w : M, mD w ∧ mA u u' w
  a2 : ∀ u₁ u₂ w v₁ v₂ w' : M, mD u₁ → mD u₂ → mD w → mD v₁ → mD v₂ → mD w' →
    mA u₁ u₂ w → mA v₁ v₂ w' → mI u₁ v₁ → mI u₂ v₂ → mI w w'
  m1 : ∀ u u' : M, mD u → mD u' → ∃ w : M, mD w ∧ mMu u u' w
  m2 : ∀ u₁ u₂ w v₁ v₂ w' : M, mD u₁ → mD u₂ → mD w → mD v₁ → mD v₂ → mD w' →
    mMu u₁ u₂ w → mMu v₁ v₂ w' → mI u₁ v₁ → mI u₂ v₂ → mI w w'

theorem ev_sE1 : ev (![] : Fin 0 → M) sE1 ↔ ∀ x : M, mE x x := by
  simp [sE1]
theorem ev_sEI : ev (![] : Fin 0 → M) sEI ↔
    ∀ x a b : M, mD a → mD b → mE a x → mE b x → mI a b := by
  simp [sEI]
theorem ev_sIs : ev (![] : Fin 0 → M) sIs ↔ ∀ a b : M, mD a → mD b → mI a b → mI b a := by
  simp [sIs]
theorem ev_sIt : ev (![] : Fin 0 → M) sIt ↔
    ∀ a b c : M, mD a → mD b → mD c → mI a b → mI b c → mI a c := by
  simp [sIt]
theorem ev_sZ1 : ev (![] : Fin 0 → M) sZ1 ↔ ∃ z : M, mD z ∧ mZ z := by
  simp [sZ1]
theorem ev_sZ2 : ev (![] : Fin 0 → M) sZ2 ↔
    ∀ a b : M, mD a → mZ a → mD b → mZ b → mI a b := by
  simp [sZ2]
theorem ev_sS1 : ev (![] : Fin 0 → M) sS1 ↔ ∀ u : M, mD u → ∃ w : M, mD w ∧ mS u w := by
  simp [sS1]
theorem ev_sS2 : ev (![] : Fin 0 → M) sS2 ↔
    ∀ u w u' w' : M, mD u → mD w → mD u' → mD w' → mS u w → mS u' w' → mI u u' → mI w w' := by
  simp [sS2]
theorem ev_sA1 : ev (![] : Fin 0 → M) sA1 ↔
    ∀ u u' : M, mD u → mD u' → ∃ w : M, mD w ∧ mA u u' w := by
  simp [sA1]
theorem ev_sA2 : ev (![] : Fin 0 → M) sA2 ↔
    ∀ u₁ u₂ w v₁ v₂ w' : M, mD u₁ → mD u₂ → mD w → mD v₁ → mD v₂ → mD w' →
      mA u₁ u₂ w → mA v₁ v₂ w' → mI u₁ v₁ → mI u₂ v₂ → mI w w' := by
  simp [sA2]
theorem ev_sM1 : ev (![] : Fin 0 → M) sM1 ↔
    ∀ u u' : M, mD u → mD u' → ∃ w : M, mD w ∧ mMu u u' w := by
  simp [sM1]
theorem ev_sM2 : ev (![] : Fin 0 → M) sM2 ↔
    ∀ u₁ u₂ w v₁ v₂ w' : M, mD u₁ → mD u₂ → mD w → mD v₁ → mD v₂ → mD w' →
      mMu u₁ u₂ w → mMu v₁ v₂ w' → mI u₁ v₁ → mI u₂ v₂ → mI w w' := by
  simp [sM2]
theorem ev_sPair (i : Fin 4) : ev (![] : Fin 0 → M) (sPair i) ↔
    ∀ a b : M, mD a → mD b → mL i a → mL i b → mI a b := by
  simp [sPair]
theorem wOf_sBox (i : Fin 4) (x : M) : wOf (sBox i) x ↔ mD x ∧ mL i x := by
  have h : ev ![x] (sLet i) ↔ mL i x := wOf_sLet i x
  simp [wOf, sBox, h]
theorem wOf_sBox_dom (i : Fin 4) : ∀ x : M, wOf (sBox i) x → mD x :=
  fun x h => ((wOf_sBox i x).mp h).1

theorem ev_sWith (F : SF 0) :
    ev (![] : Fin 0 → M) (sWith F) ↔ (MTheta M → ev (![] : Fin 0 → M) F) := by
  unfold sWith
  simp only [ev_imp, ev_sE1, ev_sEI, ev_sIs, ev_sIt, ev_sZ1, ev_sZ2, ev_sS1, ev_sS2, ev_sA1,
    ev_sA2, ev_sM1, ev_sM2]
  constructor
  · intro h H
    exact h H.e1 H.ei H.is H.it H.z1 H.z2 H.s1 H.s2 H.a1 H.a2 H.m1 H.m2
  · intro h a b c d e f g i j k l m
    exact h ⟨a,b,c,d,e,f,g,i,j,k,l,m⟩

/-! ### The facts as statements about relations -/

section facts
variable (H : MTheta M)
include H

theorem m_selfName {P : M → Prop} {u : M} (hu : mD u) (pu : P u) : mName P u :=
  ⟨u, u, ⟨hu, H.e1 u⟩, pu, H.ei u u u hu hu (H.e1 u) (H.e1 u)⟩

theorem m_atomTransfer {P₁ Q₁ P₂ Q₂ : M → Prop} (h1 : ∀ x, P₁ x → mD x) (h2 : ∀ x, P₂ x → mD x)
    (k1 : ∀ x, Q₁ x → mD x) (k2 : ∀ x, Q₂ x → mD x) (n1 : mNameAll P₁ Q₁) (n2 : mNameAll P₂ Q₂)
    (e : mEqVal P₁ P₂) : mEqVal Q₁ Q₂ := by
  obtain ⟨v, w, hv, hw, hvw⟩ := e
  have dv := h1 v hv
  have dw := h2 w hw
  obtain ⟨v₁, w₁, ⟨dv₁, ev₁⟩, qw₁, i₁⟩ := n1 v dv (m_selfName H dv hv)
  obtain ⟨v₂, w₂, ⟨dv₂, ev₂⟩, qw₂, i₂⟩ := n2 w dw (m_selfName H dw hw)
  have dw₁ := k1 w₁ qw₁
  have dw₂ := k2 w₂ qw₂
  have a1 : mI w₁ v₁ := H.is v₁ w₁ dv₁ dw₁ i₁
  have a2 : mI v₁ v := H.ei v v₁ v dv₁ dv ev₁ (H.e1 v)
  have a3 : mI w v₂ := H.ei w w v₂ dw dv₂ (H.e1 w) ev₂
  have b1 : mI w₁ v := H.it w₁ v₁ v dw₁ dv₁ dv a1 a2
  have b2 : mI w₁ w := H.it w₁ v w dw₁ dv dw b1 hvw
  have b3 : mI w₁ v₂ := H.it w₁ w v₂ dw₁ dw dv₂ b2 a3
  exact ⟨w₁, w₂, qw₁, qw₂, H.it w₁ v₂ w₂ dw₁ dv₂ dw₂ b3 i₂⟩

theorem m_nSucc {P Q : M → Prop} (hP : ∀ x, P x → mD x) (hQ : ∀ x, Q x → mD x)
    (n : mNameAll P Q) : mNameAll (mSuccV P) (mSuccV Q) := by
  rintro x hx ⟨v, w, hv, ⟨dw, u, pu, suw⟩, ivw⟩
  have du := hP u pu
  obtain ⟨v₁, w₁, ⟨dv₁, ev₁⟩, qw₁, i₁⟩ := n u du (m_selfName H du pu)
  have dw₁ := hQ w₁ qw₁
  obtain ⟨w', dw', sw'⟩ := H.s1 w₁ dw₁
  have a1 : mI u v₁ := H.ei u u v₁ du dv₁ (H.e1 u) ev₁
  have a2 : mI u w₁ := H.it u v₁ w₁ du dv₁ dw₁ a1 i₁
  have a3 : mI w w' := H.s2 u w w₁ w' du dw dw₁ dw' suw sw' a2
  exact ⟨v, w', hv, ⟨dw', w₁, qw₁, sw'⟩, H.it v w w' hv.1 dw dw' ivw a3⟩

theorem m_nAdd {P₁ Q₁ P₂ Q₂ : M → Prop} (h1 : ∀ x, P₁ x → mD x) (h2 : ∀ x, P₂ x → mD x)
    (k1 : ∀ x, Q₁ x → mD x) (k2 : ∀ x, Q₂ x → mD x) (n1 : mNameAll P₁ Q₁) (n2 : mNameAll P₂ Q₂) :
    mNameAll (mAddV P₁ P₂) (mAddV Q₁ Q₂) := by
  rintro x hx ⟨v, w, hv, ⟨dw, u₁, u₂, p1, p2, auw⟩, ivw⟩
  have du₁ := h1 u₁ p1
  have du₂ := h2 u₂ p2
  obtain ⟨v₁, w₁, ⟨dv₁, ev₁⟩, q1, i₁⟩ := n1 u₁ du₁ (m_selfName H du₁ p1)
  obtain ⟨v₂, w₂, ⟨dv₂, ev₂⟩, q2, i₂⟩ := n2 u₂ du₂ (m_selfName H du₂ p2)
  have dw₁ := k1 w₁ q1
  have dw₂ := k2 w₂ q2
  obtain ⟨w', dw', aw'⟩ := H.a1 w₁ w₂ dw₁ dw₂
  have c1 : mI u₁ w₁ :=
    H.it u₁ v₁ w₁ du₁ dv₁ dw₁ (H.ei u₁ u₁ v₁ du₁ dv₁ (H.e1 u₁) ev₁) i₁
  have c2 : mI u₂ w₂ :=
    H.it u₂ v₂ w₂ du₂ dv₂ dw₂ (H.ei u₂ u₂ v₂ du₂ dv₂ (H.e1 u₂) ev₂) i₂
  have a3 : mI w w' := H.a2 u₁ u₂ w w₁ w₂ w' du₁ du₂ dw dw₁ dw₂ dw' auw aw' c1 c2
  exact ⟨v, w', hv, ⟨dw', w₁, w₂, q1, q2, aw'⟩, H.it v w w' hv.1 dw dw' ivw a3⟩

theorem m_nMul {P₁ Q₁ P₂ Q₂ : M → Prop} (h1 : ∀ x, P₁ x → mD x) (h2 : ∀ x, P₂ x → mD x)
    (k1 : ∀ x, Q₁ x → mD x) (k2 : ∀ x, Q₂ x → mD x) (n1 : mNameAll P₁ Q₁) (n2 : mNameAll P₂ Q₂) :
    mNameAll (mMulV P₁ P₂) (mMulV Q₁ Q₂) := by
  rintro x hx ⟨v, w, hv, ⟨dw, u₁, u₂, p1, p2, auw⟩, ivw⟩
  have du₁ := h1 u₁ p1
  have du₂ := h2 u₂ p2
  obtain ⟨v₁, w₁, ⟨dv₁, ev₁⟩, q1, i₁⟩ := n1 u₁ du₁ (m_selfName H du₁ p1)
  obtain ⟨v₂, w₂, ⟨dv₂, ev₂⟩, q2, i₂⟩ := n2 u₂ du₂ (m_selfName H du₂ p2)
  have dw₁ := k1 w₁ q1
  have dw₂ := k2 w₂ q2
  obtain ⟨w', dw', aw'⟩ := H.m1 w₁ w₂ dw₁ dw₂
  have c1 : mI u₁ w₁ :=
    H.it u₁ v₁ w₁ du₁ dv₁ dw₁ (H.ei u₁ u₁ v₁ du₁ dv₁ (H.e1 u₁) ev₁) i₁
  have c2 : mI u₂ w₂ :=
    H.it u₂ v₂ w₂ du₂ dv₂ dw₂ (H.ei u₂ u₂ v₂ du₂ dv₂ (H.e1 u₂) ev₂) i₂
  have a3 : mI w w' := H.m2 u₁ u₂ w w₁ w₂ w' du₁ du₂ dw dw₁ dw₂ dw' auw aw' c1 c2
  exact ⟨v, w', hv, ⟨dw', w₁, w₂, q1, q2, aw'⟩, H.it v w w' hv.1 dw dw' ivw a3⟩

/-- If names are unique, any two members are isomorphic. -/
theorem m_valIso {P : M → Prop} (hP : ∀ x, P x → mD x) (U : mUniq P) {u u' : M}
    (pu : P u) (pu' : P u') : mI u u' := by
  have du := hP u pu
  have du' := hP u' pu'
  obtain ⟨a, b, ⟨da, ea⟩, ⟨db, eb⟩, iab⟩ :=
    U u du u' du' (m_selfName H du pu) (m_selfName H du' pu')
  have c1 : mI u a := H.ei u u a du da (H.e1 u) ea
  have c2 : mI b u' := H.ei u' b u' db du' eb (H.e1 u')
  exact H.it u b u' du db du' (H.it u a b du da db c1 iab) c2

/-- If any two members are isomorphic, names are unique. -/
theorem m_uniqOfValIso {P : M → Prop} (hP : ∀ x, P x → mD x)
    (h : ∀ u u', P u → P u' → mI u u') : mUniq P := by
  rintro x hx y hy ⟨v, w, hv, pw, ivw⟩ ⟨v', w', hv', pw', ivw'⟩
  have dw := hP w pw
  have dw' := hP w' pw'
  have c1 : mI v w' := H.it v w w' hv.1 dw dw' ivw (h w w' pw pw')
  have c2 : mI w' v' := H.is v' w' hv'.1 dw' ivw'
  exact ⟨v, v', hv, hv', H.it v w' v' hv.1 dw' hv'.1 c1 c2⟩

theorem m_uZero : mUniq (mZeroV (M := M)) :=
  m_uniqOfValIso H (fun x h => h.1) (fun u u' hu hu' => H.z2 u u' hu.1 hu.2 hu'.1 hu'.2)

theorem m_uSucc {P : M → Prop} (hP : ∀ x, P x → mD x) (U : mUniq P) : mUniq (mSuccV P) := by
  refine m_uniqOfValIso H (fun x h => h.1) ?_
  rintro w w' ⟨dw, u, pu, su⟩ ⟨dw', u', pu', su'⟩
  exact H.s2 u w u' w' (hP u pu) dw (hP u' pu') dw' su su' (m_valIso H hP U pu pu')

theorem m_uAdd {P Q : M → Prop} (hP : ∀ x, P x → mD x) (hQ : ∀ x, Q x → mD x)
    (U : mUniq P) (U' : mUniq Q) : mUniq (mAddV P Q) := by
  refine m_uniqOfValIso H (fun x h => h.1) ?_
  rintro w w' ⟨dw, u₁, u₂, p1, p2, a⟩ ⟨dw', v₁, v₂, q1, q2, a'⟩
  exact H.a2 u₁ u₂ w v₁ v₂ w' (hP u₁ p1) (hQ u₂ p2) dw (hP v₁ q1) (hQ v₂ q2) dw' a a'
    (m_valIso H hP U p1 q1) (m_valIso H hQ U' p2 q2)

theorem m_uMul {P Q : M → Prop} (hP : ∀ x, P x → mD x) (hQ : ∀ x, Q x → mD x)
    (U : mUniq P) (U' : mUniq Q) : mUniq (mMulV P Q) := by
  refine m_uniqOfValIso H (fun x h => h.1) ?_
  rintro w w' ⟨dw, u₁, u₂, p1, p2, a⟩ ⟨dw', v₁, v₂, q1, q2, a'⟩
  exact H.m2 u₁ u₂ w v₁ v₂ w' (hP u₁ p1) (hQ u₂ p2) dw (hP v₁ q1) (hQ v₂ q2) dw' a a'
    (m_valIso H hP U p1 q1) (m_valIso H hQ U' p2 q2)

theorem m_eZero : mExName (mZeroV (M := M)) := by
  obtain ⟨z, dz, zz⟩ := H.z1
  exact ⟨z, dz, m_selfName H dz ⟨dz, zz⟩⟩

theorem m_eSucc {P : M → Prop} (hP : ∀ x, P x → mD x) (E : mExName P) : mExName (mSuccV P) := by
  obtain ⟨x, hx, v, w, hv, pw, ivw⟩ := E
  obtain ⟨w', dw', sw'⟩ := H.s1 w (hP w pw)
  exact ⟨w', dw', m_selfName H dw' ⟨dw', w, pw, sw'⟩⟩

theorem m_eAdd {P Q : M → Prop} (hP : ∀ x, P x → mD x) (hQ : ∀ x, Q x → mD x)
    (E : mExName P) (E' : mExName Q) : mExName (mAddV P Q) := by
  obtain ⟨x, hx, v, w, hv, pw, ivw⟩ := E
  obtain ⟨x', hx', v', w', hv', qw', ivw'⟩ := E'
  obtain ⟨z, dz, az⟩ := H.a1 w w' (hP w pw) (hQ w' qw')
  exact ⟨z, dz, m_selfName H dz ⟨dz, w, w', pw, qw', az⟩⟩

theorem m_eMul {P Q : M → Prop} (hP : ∀ x, P x → mD x) (hQ : ∀ x, Q x → mD x)
    (E : mExName P) (E' : mExName Q) : mExName (mMulV P Q) := by
  obtain ⟨x, hx, v, w, hv, pw, ivw⟩ := E
  obtain ⟨x', hx', v', w', hv', qw', ivw'⟩ := E'
  obtain ⟨z, dz, az⟩ := H.m1 w w' (hP w pw) (hQ w' qw')
  exact ⟨z, dz, m_selfName H dz ⟨dz, w, w', pw, qw', az⟩⟩

theorem m_nameOfUniq {T C : M → Prop} (hT : ∀ x, T x → mD x) (hC : ∀ x, C x → mD x)
    (U : mUniq T) (e : mEqVal C T) : mNameAll T C := by
  obtain ⟨v', w', cv', tw', i'⟩ := e
  rintro x hx ⟨v, w, hv, tw, ivw⟩
  have dw := hT w tw
  have dw' := hT w' tw'
  have dv' := hC v' cv'
  have c1 : mI w w' := m_valIso H hT U tw tw'
  have c2 : mI w' v' := H.is v' w' dv' dw' i'
  exact ⟨v, v', hv, cv', H.it v w' v' hv.1 dw' dv' (H.it v w w' hv.1 dw dw' ivw c1) c2⟩

theorem m_nameOfEq {T C : M → Prop} (hT : ∀ x, T x → mD x) (hC : ∀ x, C x → mD x)
    (pc : ∀ a b, C a → C b → mI a b) (e : mEqVal C T) : mNameAll C T := by
  obtain ⟨v', w', cv', tw', i'⟩ := e
  rintro x hx ⟨v, w, hv, cw, ivw⟩
  have dw := hC w cw
  have dv' := hC v' cv'
  have dw' := hT w' tw'
  exact ⟨v, w', hv, tw', H.it v v' w' hv.1 dv' dw'
    (H.it v w v' hv.1 dw dv' ivw (pc w v' cw cv')) i'⟩

end facts

#print axioms ev_sNameAll
#print axioms ev_sUniq
#print axioms ev_sWith
#print axioms m_atomTransfer
#print axioms m_nAdd
#print axioms m_uAdd
#print axioms m_eAdd
#print axioms m_nameOfUniq
#print axioms m_nameOfEq
end semantics2
end PA194GuardedCompiler
