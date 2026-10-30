import ZFCinPA.LFinalRepl

set_option autoImplicit false
noncomputable section

/-!
# The base layer of the `hSchema` driver

The internal induction that produces the reflection invariant for every
formula code compiles the fixed step templates (`LStepAnd`, `LStepBasic`,
`LStepAtom`, `LStepExT`) at internal placeholder codes. This module fixes the
vocabulary it chains:

* `K6`: a six-slot placeholder tuple over the step language `L6`
  (predicates at the even slots, functions at the odd ones);
* `TotT F`, `ReflT P F` and `InvT P F = TotT F ⋏ ReflT P F`: the translation
  of the common conclusion `totS F₅ ⋏ reflS P₄ F₅` at `P`, `F`, with the
  pair lemmas identifying the translations of the hypotheses at the slot
  pairs `(0, 1)` and `(2, 3)` with the same `InvT`;
* the translations of every definitional hypothesis of the step templates,
  in closed form.
-/

namespace LeanProofs.ZFCinPA.LDriverBase

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA LeanProofs.ZFCinPA.SetPlaceholders LeanProofs.ZFCinPA.LTemplate
open LeanProofs.ZFCinPA.LInvariant LeanProofs.ZFCinPA.LStepAnd LeanProofs.ZFCinPA.LStepBasic
open LeanProofs.ZFCinPA.LStepAtom LeanProofs.ZFCinPA.LStepExT

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Typed internal semiformulas of `ℒₛₑₜ`. -/
abbrev SF (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (n : ℕ) :=
  Bootstrapping.Semiformula V ℒₛₑₜ n

/-- A placeholder tuple for the step language. -/
def K6 (p₀ : SF V 1) (f₁ : SF V 2) (p₂ : SF V 1) (f₃ : SF V 2) (p₄ : SF V 1) (f₅ : SF V 2) :
    (i : Fin 6) → SF V (ar6 i)
  | ⟨0, _⟩ => p₀
  | ⟨1, _⟩ => f₁
  | ⟨2, _⟩ => p₂
  | ⟨3, _⟩ => f₃
  | ⟨4, _⟩ => p₄
  | ⟨5, _⟩ => f₅

/-- The totality half of the invariant, translated at `F`. -/
def TotT (F : SF V 2) : Bootstrapping.Formula V ℒₛₑₜ :=
  translateFormula (K6 ⊤ F ⊤ F ⊤ F) (Rewriting.emb (totS F₅ : Sentence L6))

/-- The reflection half of the invariant, translated at `P`, `F`. -/
def ReflT (P : SF V 1) (F : SF V 2) : Bootstrapping.Formula V ℒₛₑₜ :=
  translateFormula (K6 P F P F P F) (Rewriting.emb (reflS P₄ F₅ : Sentence L6))

/-- **The reflection invariant** at internal codes `P`, `F`. -/
def InvT (P : SF V 1) (F : SF V 2) : Bootstrapping.Formula V ℒₛₑₜ := TotT F ⋏ ReflT P F

/-! ## Placeholder-free formulas translate independently of the tuple -/

/-- `φ` mentions no placeholder. -/
def NoPh {ξ : Type} : {n : ℕ} → Semiformula L6 ξ n → Prop
  | _, ⊤ => True
  | _, ⊥ => True
  | _, .rel (Sum.inl _) _ => True
  | _, .rel (Sum.inr _) _ => False
  | _, .nrel (Sum.inl _) _ => True
  | _, .nrel (Sum.inr _) _ => False
  | _, p ⋏ q => NoPh p ∧ NoPh q
  | _, p ⋎ q => NoPh p ∧ NoPh q
  | _, ∀⁰ p => NoPh p
  | _, ∃⁰ p => NoPh p

theorem noPh_rew {ξ₁ ξ₂ : Type} {n₁ : ℕ} (φ : Semiformula L6 ξ₁ n₁) :
    ∀ {n₂ : ℕ} (ω : Rew L6 ξ₁ n₁ ξ₂ n₂), NoPh (ω ▹ φ) ↔ NoPh φ := by
  induction φ using Semiformula.rec' with
  | hverum => intros; simp [NoPh]
  | hfalsum => intros; simp [NoPh]
  | hrel r v => intro _ ω; rcases r with r | r <;> simp [NoPh]
  | hnrel r v => intro _ ω; rcases r with r | r <;> simp [NoPh]
  | hand p q hp hq => intro _ ω; simp [NoPh, hp, hq]
  | hor p q hp hq => intro _ ω; simp [NoPh, hp, hq]
  | hall p hp => intro _ ω; simp [NoPh, hp]
  | hexs p hp => intro _ ω; simp [NoPh, hp]

theorem noPh_lMap {ξ : Type} {n : ℕ} (σ : Semiformula ℒₛₑₜ ξ n) :
    NoPh (Semiformula.lMap (setHom 6 ar6) σ) := by
  induction σ using Semiformula.rec' with
  | hverum => simp [NoPh]
  | hfalsum => simp [NoPh]
  | hrel r v => simp [NoPh, Semiformula.lMap_rel]
  | hnrel r v => simp [NoPh, Semiformula.lMap_nrel]
  | hand p q hp hq => simp [NoPh, hp, hq]
  | hor p q hp hq => simp [NoPh, hp, hq]
  | hall p hp => simp [NoPh, hp]
  | hexs p hp => simp [NoPh, hp]

@[simp] theorem noPh_lift {n : ℕ} (σ : SetTheorySemisentence n) :
    NoPh (lift σ : Semisentence L6 n) := noPh_lMap σ

theorem noPh_rewLift {ξ₂ : Type} {n m : ℕ} (σ : SetTheorySemisentence n) (ω : Rew L6 Empty n ξ₂ m) :
    NoPh (ω ▹ (lift σ : Semisentence L6 n)) :=
  (noPh_rew _ ω).2 (noPh_lMap σ)

theorem translate_noPh (Ks Ks' : (i : Fin 6) → SF V (ar6 i)) {n : ℕ}
    (p : Semiproposition L6 n) (h : NoPh p) : translateFormula Ks p = translateFormula Ks' p := by
  induction p using Semiformula.rec' with
  | hverum => rfl
  | hfalsum => rfl
  | hrel r v => rcases r with r | r <;> first | rfl | exact h.elim
  | hnrel r v => rcases r with r | r <;> first | rfl | exact h.elim
  | hand p q hp hq => exact congrArg₂ (· ⋏ ·) (hp h.1) (hq h.2)
  | hor p q hp hq => exact congrArg₂ (· ⋎ ·) (hp h.1) (hq h.2)
  | hall p hp => exact congrArg (∀⁰ ·) (hp h)
  | hexs p hp => exact congrArg (∃⁰ ·) (hp h)

section Pairs

variable (Ks : (i : Fin 6) → SF V (ar6 i))

/-- Lifted `ℒₛₑₜ` pieces translate to their quotations, whatever the tuple. -/
@[simp] theorem tr_lift {n : ℕ} (σ : SetTheorySemisentence n) :
    translateFormula Ks (Rewriting.emb (lift σ : Semisentence L6 n)) = ⌜σ⌝ :=
  translateFormula_emb_liftSet Ks σ

/-- Substituted lifted pieces translate to substituted quotations. -/
@[simp] theorem tr_lift_subst {n m : ℕ} (σ : SetTheorySemisentence n)
    (v : Fin n → Semiterm L6 Empty m) :
    translateFormula Ks (Rewriting.emb ((lift σ : Semisentence L6 n) ⇜ v)) =
      (⌜σ⌝ : SF V n).subst (fun i ↦ translateTerm (Rew.emb (v i))) := by
  rw [Rewriting.emb_subst_eq_subst_emb]
  exact (translateFormula_subst Ks _ _).trans (by rw [tr_lift])

/-- The identity substitution at one bound variable. -/
@[simp] theorem subst_ph₁ (φ : SF V 1) :
    φ.subst (fun j ↦ translateTerm (V := V) ((![#0] : Fin 1 → SyntacticSemiterm L6 1) j)) = φ :=
  Bootstrapping.Semiformula.subst_eq_self _ _ fun i ↦ by
    match i with
    | 0 => rfl

/-- A placeholder atom translates to a substitution instance of its slot. -/
theorem tr_ph {n : ℕ} (i : Fin 6) (v : Fin (ar6 i) → SyntacticSemiterm L6 n) :
    translateFormula Ks (.rel (placeholderRel i) v) = (Ks i).subst (fun j ↦ translateTerm (v j)) :=
  rfl

@[simp] theorem tr_P₀' :
    translateFormula Ks (@Semiformula.rel L6 ℕ 1 1 (placeholderRel (0 : Fin 6))
      ![(#0 : SyntacticSemiterm L6 1)]) = Ks 0 := subst_ph₁ (Ks 0)

@[simp] theorem tr_P₀ :
    translateFormula Ks (.rel (placeholderRel (0 : Fin 6)) ![(#0 : SyntacticSemiterm L6 1)]) =
      Ks 0 := subst_ph₁ (Ks 0)

@[simp] theorem tr_P₂' :
    translateFormula Ks (@Semiformula.rel L6 ℕ 1 1 (placeholderRel (2 : Fin 6))
      ![(#0 : SyntacticSemiterm L6 1)]) = Ks 2 := subst_ph₁ (Ks 2)

@[simp] theorem tr_P₂ :
    translateFormula Ks (.rel (placeholderRel (2 : Fin 6)) ![(#0 : SyntacticSemiterm L6 1)]) =
      Ks 2 := subst_ph₁ (Ks 2)

@[simp] theorem tr_P₄' :
    translateFormula Ks (@Semiformula.rel L6 ℕ 1 1 (placeholderRel (4 : Fin 6))
      ![(#0 : SyntacticSemiterm L6 1)]) = Ks 4 := subst_ph₁ (Ks 4)

@[simp] theorem tr_P₄ :
    translateFormula Ks (.rel (placeholderRel (4 : Fin 6)) ![(#0 : SyntacticSemiterm L6 1)]) =
      Ks 4 := subst_ph₁ (Ks 4)

@[simp] theorem subst_bvar0 (φ : SF V 1) :
    φ.subst (fun _ ↦ Bootstrapping.Semiterm.bvar 0) = φ :=
  Bootstrapping.Semiformula.subst_eq_self _ _ fun i ↦ by
    match i with
    | 0 => rfl

/-- Placeholder atoms of arity one, at any level and argument. -/
@[simp] theorem tr_Pv₀ {n : ℕ} (v : Fin 1 → SyntacticSemiterm L6 n) :
    translateFormula Ks (@Semiformula.rel L6 ℕ n 1 (placeholderRel (0 : Fin 6)) v) =
      (Ks 0).subst (fun j ↦ translateTerm (v j)) := rfl

@[simp] theorem tr_Pv₂ {n : ℕ} (v : Fin 1 → SyntacticSemiterm L6 n) :
    translateFormula Ks (@Semiformula.rel L6 ℕ n 1 (placeholderRel (2 : Fin 6)) v) =
      (Ks 2).subst (fun j ↦ translateTerm (v j)) := rfl

@[simp] theorem tr_nPv₀ {n : ℕ} (v : Fin 1 → SyntacticSemiterm L6 n) :
    translateFormula Ks (@Semiformula.nrel L6 ℕ n 1 (placeholderRel (0 : Fin 6)) v) =
      ∼(Ks 0).subst (fun j ↦ translateTerm (v j)) := rfl

@[simp] theorem tr_nP₀' :
    translateFormula Ks (@Semiformula.nrel L6 ℕ 1 1 (placeholderRel (0 : Fin 6))
      ![(#0 : SyntacticSemiterm L6 1)]) = ∼Ks 0 := congrArg (∼·) (subst_ph₁ (Ks 0))

/-- The two renderings of the swap vector agree. -/
@[simp] theorem swap_emb :
    (fun i ↦ translateTerm (V := V) (Rew.emb ((![#1, #0] : Fin 2 → Semiterm L6 Empty 2) i))) =
      (fun j ↦ translateTerm (V := V) ((![#1, #0] : Fin 2 → SyntacticSemiterm L6 2) j)) := by
  funext i
  match i with
  | 0 => rfl
  | 1 => rfl

theorem tr_tot₁ : translateFormula Ks (Rewriting.emb (totS F₁ : Sentence L6)) = TotT (Ks 1) := by
  simp [TotT, totS, F₁, F₅, translateFormula]
  and_intros <;> first
    | exact translate_noPh _ _ _ (by simp [Rewriting.emb, Rewriting.subst, noPh_rew, noPh_rewLift, NoPh])
    | rfl

theorem tr_tot₃ : translateFormula Ks (Rewriting.emb (totS F₃ : Sentence L6)) = TotT (Ks 3) := by
  simp [TotT, totS, F₃, F₅, translateFormula]
  and_intros <;> first
    | exact translate_noPh _ _ _ (by simp [Rewriting.emb, Rewriting.subst, noPh_rew, noPh_rewLift, NoPh])
    | rfl

theorem tr_tot₅ : translateFormula Ks (Rewriting.emb (totS F₅ : Sentence L6)) = TotT (Ks 5) := by
  simp [TotT, totS, F₅, translateFormula]
  and_intros <;> first
    | exact translate_noPh _ _ _ (by simp [Rewriting.emb, Rewriting.subst, noPh_rew, noPh_rewLift, NoPh])
    | rfl

theorem tr_refl₀₁ :
    translateFormula Ks (Rewriting.emb (reflS P₀ F₁ : Sentence L6)) = ReflT (Ks 0) (Ks 1) := by
  simp [ReflT, reflS, P₀, F₁, P₄, F₅, translateFormula]
  and_intros <;> first
    | exact translate_noPh _ _ _ (by simp [Rewriting.emb, Rewriting.subst, noPh_rew, noPh_rewLift, NoPh])
    | rfl

theorem tr_refl₂₃ :
    translateFormula Ks (Rewriting.emb (reflS P₂ F₃ : Sentence L6)) = ReflT (Ks 2) (Ks 3) := by
  simp [ReflT, reflS, P₂, F₃, P₄, F₅, translateFormula]
  and_intros <;> first
    | exact translate_noPh _ _ _ (by simp [Rewriting.emb, Rewriting.subst, noPh_rew, noPh_rewLift, NoPh])
    | rfl

theorem tr_refl₄₅ :
    translateFormula Ks (Rewriting.emb (reflS P₄ F₅ : Sentence L6)) = ReflT (Ks 4) (Ks 5) := by
  simp [ReflT, reflS, P₄, F₅, translateFormula]
  and_intros <;> first
    | exact translate_noPh _ _ _ (by simp [Rewriting.emb, Rewriting.subst, noPh_rew, noPh_rewLift, NoPh])
    | rfl

end Pairs

section Defs

variable (Ks : (i : Fin 6) → SF V (ar6 i))

theorem tr_andDefP :
    translateFormula Ks (Rewriting.emb andDefP) = ∀⁰ (Ks 4 🡘 Ks 0 ⋏ Ks 2) := by
  simp [andDefP, P₀, P₂, P₄, translateFormula, LogicalConnective.iff,
    Bootstrapping.Semiformula.imp_def]
  try exact (Bootstrapping.Semiformula.imp_def _ _).symm

end Defs

section Shapes

variable (Ks : (i : Fin 6) → SF V (ar6 i))

/-- The swap of the two bound variables, as translated. -/
abbrev swapV : Bootstrapping.SemitermVec V ℒₛₑₜ 2 2 :=
  fun j ↦ translateTerm (V := V) ((![#1, #0] : Fin 2 → SyntacticSemiterm L6 2) j)

theorem tr_F₁' {n : ℕ} (v : Fin 2 → SyntacticSemiterm L6 n) :
    translateFormula Ks (@Semiformula.rel L6 ℕ n 2 (placeholderRel (1 : Fin 6)) v) =
      (Ks 1).subst (fun j ↦ translateTerm (v j)) := rfl

theorem tr_F₃' {n : ℕ} (v : Fin 2 → SyntacticSemiterm L6 n) :
    translateFormula Ks (@Semiformula.rel L6 ℕ n 2 (placeholderRel (3 : Fin 6)) v) =
      (Ks 3).subst (fun j ↦ translateTerm (v j)) := rfl

theorem tr_F₅' {n : ℕ} (v : Fin 2 → SyntacticSemiterm L6 n) :
    translateFormula Ks (@Semiformula.rel L6 ℕ n 2 (placeholderRel (5 : Fin 6)) v) =
      (Ks 5).subst (fun j ↦ translateTerm (v j)) := rfl

/-- The identity substitution at two bound variables. -/
@[simp] theorem subst_ph₂ (φ : SF V 2) :
    φ.subst (fun j ↦ translateTerm (V := V)
      ((![#0, #1] : Fin 2 → SyntacticSemiterm L6 2) j)) = φ :=
  Bootstrapping.Semiformula.subst_eq_self _ _ fun i ↦ by
    match i with
    | 0 => rfl
    | 1 => rfl

/-- The translated maximum of two function codes. -/
def MaxT (F₁' F₃' : SF V 2) : SF V 2 :=
  translateFormula (K6 ⊤ F₁' ⊤ F₃' ⊤ ⊤) (Rewriting.emb maxRHS)

theorem tr_maxRHS : translateFormula Ks (Rewriting.emb maxRHS) = MaxT (Ks 1) (Ks 3) := by
  simp [MaxT, maxRHS, F₁, F₃, translateFormula]
  and_intros <;> first
    | exact translate_noPh _ _ _ (by simp [Rewriting.emb, Rewriting.subst, noPh_rew, noPh_rewLift, NoPh])
    | rfl

/-- The translated witness bound of a predicate code. -/
def WbT (P : SF V 1) : SF V 2 :=
  translateFormula (K6 P ⊤ ⊤ ⊤ ⊤ ⊤) (Rewriting.emb (wbS P₀))

theorem tr_wbS : translateFormula Ks (Rewriting.emb (wbS P₀)) = WbT (Ks 0) := by
  simp [WbT, wbS, witS, hasWitS, anyWitS, P₀, translateFormula]
  and_intros <;> first
    | exact translate_noPh _ _ _ (by simp [Rewriting.emb, Rewriting.subst, noPh_rew, noPh_rewLift, NoPh])
    | rfl

/-- The translated witness bound of the negation of a predicate code. -/
def WbNT (P : SF V 1) : SF V 2 :=
  translateFormula (K6 P ⊤ ⊤ ⊤ ⊤ ⊤) (Rewriting.emb (wbS (∼P₀)))

theorem tr_wbNS : translateFormula Ks (Rewriting.emb (wbS (∼P₀))) = WbNT (Ks 0) := by
  simp [WbNT, wbS, witS, hasWitS, anyWitS, P₀, translateFormula]
  and_intros <;> first
    | exact translate_noPh _ _ _ (by simp [Rewriting.emb, Rewriting.subst, noPh_rew, noPh_rewLift, NoPh])
    | rfl

/-- The translated existential body. -/
def ExT (P : SF V 1) : SF V 1 := translateFormula (K6 P ⊤ ⊤ ⊤ ⊤ ⊤) (Rewriting.emb exBody)

theorem tr_exBody : translateFormula Ks (Rewriting.emb exBody) = ExT (Ks 0) := by
  simp [ExT, exBody, P₀, translateFormula]
  try rfl

/-- The translated universal body. -/
def AllT (P : SF V 1) : SF V 1 := translateFormula (K6 P ⊤ ⊤ ⊤ ⊤ ⊤) (Rewriting.emb allBody)

theorem tr_allBody : translateFormula Ks (Rewriting.emb allBody) = AllT (Ks 0) := by
  simp [AllT, allBody, P₀, translateFormula]
  try rfl

/-- The translated atom bodies (`isEq` selects equality). -/
def AtomT (isEq : Bool) (N₀ N₂ : SF V 1) : SF V 1 :=
  translateFormula (K6 N₀ ⊤ N₂ ⊤ ⊤ ⊤)
    (Rewriting.emb (if isEq then eqAtomBody else memAtomBody))

theorem tr_memAtomBody :
    translateFormula Ks (Rewriting.emb memAtomBody) = AtomT false (Ks 0) (Ks 2) := by
  simp [AtomT, memAtomBody, P₀, P₂, translateFormula]
  and_intros <;> first
    | exact translate_noPh _ _ _ (by simp [Rewriting.emb, Rewriting.subst, noPh_rew, noPh_rewLift, NoPh])
    | rfl

theorem tr_eqAtomBody :
    translateFormula Ks (Rewriting.emb eqAtomBody) = AtomT true (Ks 0) (Ks 2) := by
  simp [AtomT, eqAtomBody, P₀, P₂, translateFormula]
  and_intros <;> first
    | exact translate_noPh _ _ _ (by simp [Rewriting.emb, Rewriting.subst, noPh_rew, noPh_rewLift, NoPh])
    | rfl

/-- "The predicate code defines exactly one natural number." -/
def NumOKT (N : SF V 1) : Bootstrapping.Formula V ℒₛₑₜ :=
  translateFormula (K6 N ⊤ ⊤ ⊤ ⊤ ⊤) (Rewriting.emb numOK₀)

theorem tr_numOK₀ : translateFormula Ks (Rewriting.emb numOK₀) = NumOKT (Ks 0) := by
  simp [NumOKT, numOK₀, P₀, translateFormula]
  and_intros <;> first
    | exact translate_noPh _ _ _ (by simp [Rewriting.emb, Rewriting.subst, noPh_rew, noPh_rewLift, NoPh])
    | rfl

theorem tr_numOK₂ : translateFormula Ks (Rewriting.emb numOK₂) = NumOKT (Ks 2) := by
  simp [NumOKT, numOK₀, numOK₂, P₀, P₂, translateFormula]
  and_intros <;> first
    | exact translate_noPh _ _ _ (by simp [Rewriting.emb, Rewriting.subst, noPh_rew, noPh_rewLift, NoPh])
    | rfl

end Shapes

section DefShapes

variable (Ks : (i : Fin 6) → SF V (ar6 i))

theorem tr_orDefP :
    translateFormula Ks (Rewriting.emb orDefP) = ∀⁰ (Ks 4 🡘 Ks 0 ⋎ Ks 2) := by
  simp [orDefP, P₀, P₂, P₄, translateFormula, LogicalConnective.iff,
    Bootstrapping.Semiformula.imp_def]
  try exact (Bootstrapping.Semiformula.imp_def _ _).symm

theorem tr_negDefP :
    translateFormula Ks (Rewriting.emb negDefP) = ∀⁰ (Ks 4 🡘 ∼Ks 0) := by
  simp [negDefP, P₀, P₄, translateFormula, LogicalConnective.iff,
    Bootstrapping.Semiformula.imp_def]
  try exact (Bootstrapping.Semiformula.imp_def _ _).symm

theorem tr_topDefP :
    translateFormula Ks (Rewriting.emb topDefP) = ∀⁰ (Ks 4 🡘 ⊤) := by
  simp [topDefP, P₄, translateFormula, LogicalConnective.iff,
    Bootstrapping.Semiformula.imp_def]
  try exact (Bootstrapping.Semiformula.imp_def _ _).symm

theorem tr_botDefP :
    translateFormula Ks (Rewriting.emb botDefP) = ∀⁰ (Ks 4 🡘 ⊥) := by
  simp [botDefP, P₄, translateFormula, LogicalConnective.iff,
    Bootstrapping.Semiformula.imp_def]
  try exact (Bootstrapping.Semiformula.imp_def _ _).symm

theorem tr_exDefP :
    translateFormula Ks (Rewriting.emb exDefP) = ∀⁰ (Ks 4 🡘 ExT (Ks 0)) := by
  rw [← tr_exBody Ks]
  simp [exDefP, P₄, translateFormula, LogicalConnective.iff, Bootstrapping.Semiformula.imp_def]
  try exact (Bootstrapping.Semiformula.imp_def _ _).symm

theorem tr_allDefP :
    translateFormula Ks (Rewriting.emb allDefP) = ∀⁰ (Ks 4 🡘 AllT (Ks 0)) := by
  rw [← tr_allBody Ks]
  simp [allDefP, P₄, translateFormula, LogicalConnective.iff, Bootstrapping.Semiformula.imp_def]
  try exact (Bootstrapping.Semiformula.imp_def _ _).symm

theorem tr_memAtomDefP :
    translateFormula Ks (Rewriting.emb memAtomDefP) = ∀⁰ (Ks 4 🡘 AtomT false (Ks 0) (Ks 2)) := by
  rw [← tr_memAtomBody Ks]
  simp [memAtomDefP, P₄, translateFormula, LogicalConnective.iff,
    Bootstrapping.Semiformula.imp_def]
  try exact (Bootstrapping.Semiformula.imp_def _ _).symm

theorem tr_eqAtomDefP :
    translateFormula Ks (Rewriting.emb eqAtomDefP) = ∀⁰ (Ks 4 🡘 AtomT true (Ks 0) (Ks 2)) := by
  rw [← tr_eqAtomBody Ks]
  simp [eqAtomDefP, P₄, translateFormula, LogicalConnective.iff,
    Bootstrapping.Semiformula.imp_def]
  try exact (Bootstrapping.Semiformula.imp_def _ _).symm

theorem tr_maxDefF :
    translateFormula Ks (Rewriting.emb maxDefF) =
      ∀⁰ ∀⁰ ((Ks 5).subst swapV 🡘 (MaxT (Ks 1) (Ks 3)).subst swapV) := by
  rw [← tr_maxRHS Ks]
  simp [maxDefF, F₅, translateFormula, tr_F₅', Rewriting.emb_subst_eq_subst_emb,
    LogicalConnective.iff, Bootstrapping.Semiformula.imp_def]
  try exact (Bootstrapping.Semiformula.imp_def _ _).symm

theorem tr_eqDefF :
    translateFormula Ks (Rewriting.emb eqDefF) =
      ∀⁰ ∀⁰ ((Ks 5).subst swapV 🡘 (Ks 1).subst swapV) := by
  simp [eqDefF, F₁, F₅, translateFormula, tr_F₁', tr_F₅', LogicalConnective.iff,
    Bootstrapping.Semiformula.imp_def]
  try exact (Bootstrapping.Semiformula.imp_def _ _).symm

theorem tr_succDefF :
    translateFormula Ks (Rewriting.emb succDefF) =
      ∀⁰ ∀⁰ ((Ks 5).subst swapV 🡘 (⌜succP⌝ : SF V 2).subst swapV) := by
  simp [succDefF, succL, F₅, translateFormula, tr_F₅', LogicalConnective.iff,
    Bootstrapping.Semiformula.imp_def]
  try exact (Bootstrapping.Semiformula.imp_def _ _).symm

theorem tr_wbDef₀ :
    translateFormula Ks (Rewriting.emb (wbDef P₀)) = ∀⁰ ∀⁰ (Ks 3 🡘 WbT (Ks 0)) := by
  rw [← tr_wbS Ks]
  simp [wbDef, F₃, translateFormula, tr_F₃', LogicalConnective.iff,
    Bootstrapping.Semiformula.imp_def]
  try exact (Bootstrapping.Semiformula.imp_def _ _).symm

theorem tr_wbDefN :
    translateFormula Ks (Rewriting.emb (wbDef (∼P₀))) = ∀⁰ ∀⁰ (Ks 3 🡘 WbNT (Ks 0)) := by
  rw [← tr_wbNS Ks]
  simp [wbDef, F₃, translateFormula, tr_F₃', LogicalConnective.iff,
    Bootstrapping.Semiformula.imp_def]
  try exact (Bootstrapping.Semiformula.imp_def _ _).symm

end DefShapes

section Taut

/-- `∀x (A ↔ A)` is an internal `𝗭𝗙` theorem. -/
theorem all_iff_self (A : SF V 1) : (𝗭𝗙 : SetTheory).internalize V ⊢ ∀⁰ (A 🡘 A) :=
  Bootstrapping.TProof.all! (by
    simp only [Bootstrapping.Semiformula.free, Bootstrapping.Semiformula.shift_iff,
      Bootstrapping.Semiformula.substs_imply]
    exact Entailment.E!_id)

/-- `∀x ∀y (A ↔ A)` is an internal `𝗭𝗙` theorem. -/
theorem all₂_iff_self (A : SF V 2) : (𝗭𝗙 : SetTheory).internalize V ⊢ ∀⁰ ∀⁰ (A 🡘 A) :=
  Bootstrapping.TProof.all₂! (by
    simp only [Bootstrapping.Semiformula.shift_iff, Bootstrapping.Semiformula.substs_imply]
    exact Entailment.E!_id)

end Taut

end LeanProofs.ZFCinPA.LDriverBase
