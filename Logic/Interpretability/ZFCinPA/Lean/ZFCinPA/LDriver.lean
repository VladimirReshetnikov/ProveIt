import ZFCinPA.LDriverSteps
import ZFCinPA.LTransVal

set_option autoImplicit false
noncomputable section

/-!
# The `hSchema` driver: the reflection invariant for every formula code

For every internal semiformula code `p` of level `n` there is a function code
`f` such that `𝗭𝗙` proves the reflection invariant of `envForm n p` with `f`:

`Θ n p :≡ ∃ f, IsSemiformula 2 f ∧ Provable 𝗭𝗙 (invVal (envForm n p) f)`

(`driver`). The proof is the `Σ₁` structural induction on semiformulas of the
ambient model (`IsSemiformula.sigma1_structural_induction`), whose binder
level is exactly `envForm`'s depth parameter. Each case is one compiled step
of `LDriverSteps`, after identifying `envForm`'s clause with the step's
translated body:

* atoms read through numeral chains (`atomT_val`, with `LNumOK.numOK`);
* negated atoms by `neg_step`; `⊤`, `⊥` by the bases;
* `⋏`, `⋎` literally (`envForm_and`, `envForm_or`);
* `∀`, `∃` by `allT_val`, `exT_val` (`envForm_all`, `envForm_exs`).
-/

namespace LeanProofs.ZFCinPA.LDriver

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LO.FirstOrder.SetTheory Entailment
open LeanProofs.ZFCinPA LeanProofs.ZFCinPA.SetPlaceholders LeanProofs.ZFCinPA.LTemplate
open LeanProofs.ZFCinPA.LInvariant LeanProofs.ZFCinPA.LStepAnd LeanProofs.ZFCinPA.LStepBasic
open LeanProofs.ZFCinPA.LStepAtom LeanProofs.ZFCinPA.LStepExT LeanProofs.ZFCinPA.LDriverBase
open LeanProofs.ZFCinPA.LDriverSteps LeanProofs.ZFCinPA.EnvTransform
open LeanProofs.ZFCinPA.NumeralOmega (numChainQ numChainQ_val)
open scoped LO.FirstOrder.Arithmetic

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]


/-! ## The invariant as a code function -/

/-- The totality half, on codes. -/
def totVal (f : V) : V :=
  LTransVal.transVal (![^⊤, f, ^⊤, f, ^⊤, f] : Fin 6 → V) (Rewriting.emb (totS F₅ : Sentence L6))

/-- The reflection half, on codes. -/
def reflVal (p f : V) : V :=
  LTransVal.transVal (![p, f, p, f, p, f] : Fin 6 → V) (Rewriting.emb (reflS P₄ F₅ : Sentence L6))

/-- The invariant, on codes. -/
def invVal (p f : V) : V := totVal f ^⋏ reflVal p f

theorem invT_val (P : SF V 1) (F : SF V 2) : (InvT P F).val = invVal P.val F.val := by
  simp only [InvT, TotT, ReflT, Bootstrapping.Semiformula.val_and, LTransVal.val_translateFormula,
    invVal, totVal, reflVal]
  congr 2
  · funext i
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨2, _⟩ => rfl
    | ⟨3, _⟩ => rfl
    | ⟨4, _⟩ => rfl
    | ⟨5, _⟩ => rfl
  · funext i
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨2, _⟩ => rfl
    | ⟨3, _⟩ => rfl
    | ⟨4, _⟩ => rfl
    | ⟨5, _⟩ => rfl

instance totVal_definable : 𝚺₁-Function₁ (totVal : V → V) := by
  have h := LTransVal.transVal_definable (V := V) (k := 6) (arities := ar6)
    (Rewriting.emb (totS F₅ : Sentence L6) : Semiproposition L6 0)
  refine (HierarchySymbol.DefinableFunction.substitution (F := fun vals : Fin 6 → V ↦
      LTransVal.transVal vals (Rewriting.emb (totS F₅ : Sentence L6) : Semiproposition L6 0))
    (f := fun i (x : Fin 1 → V) ↦ (![^⊤, x 0, ^⊤, x 0, ^⊤, x 0] : Fin 6 → V) i) h
    (fun i ↦ ?_)).of_eq _ (fun x ↦ rfl)
  match i with
  | ⟨0, _⟩ => exact HierarchySymbol.DefinableFunction.const _
  | ⟨1, _⟩ => exact HierarchySymbol.DefinableFunction.var 0
  | ⟨2, _⟩ => exact HierarchySymbol.DefinableFunction.const _
  | ⟨3, _⟩ => exact HierarchySymbol.DefinableFunction.var 0
  | ⟨4, _⟩ => exact HierarchySymbol.DefinableFunction.const _
  | ⟨5, _⟩ => exact HierarchySymbol.DefinableFunction.var 0

instance reflVal_definable : 𝚺₁-Function₂ (reflVal : V → V → V) := by
  have h := LTransVal.transVal_definable (V := V) (k := 6) (arities := ar6)
    (Rewriting.emb (reflS P₄ F₅ : Sentence L6) : Semiproposition L6 0)
  refine (HierarchySymbol.DefinableFunction.substitution (F := fun vals : Fin 6 → V ↦
      LTransVal.transVal vals (Rewriting.emb (reflS P₄ F₅ : Sentence L6) : Semiproposition L6 0))
    (f := fun i (x : Fin 2 → V) ↦ (![x 0, x 1, x 0, x 1, x 0, x 1] : Fin 6 → V) i) h
    (fun i ↦ ?_)).of_eq _ (fun x ↦ rfl)
  match i with
  | ⟨0, _⟩ => exact HierarchySymbol.DefinableFunction.var 0
  | ⟨1, _⟩ => exact HierarchySymbol.DefinableFunction.var 1
  | ⟨2, _⟩ => exact HierarchySymbol.DefinableFunction.var 0
  | ⟨3, _⟩ => exact HierarchySymbol.DefinableFunction.var 1
  | ⟨4, _⟩ => exact HierarchySymbol.DefinableFunction.var 0
  | ⟨5, _⟩ => exact HierarchySymbol.DefinableFunction.var 1

instance invVal_definable : 𝚺₁-Function₂ (invVal : V → V → V) :=
  HierarchySymbol.DefinableFunction.of_eq _ (fun _ ↦ rfl)
    (HierarchySymbol.DefinableFunction₂.comp (F := qqAnd)
      (HierarchySymbol.DefinableFunction₁.comp (F := totVal)
        (HierarchySymbol.DefinableFunction.var 1))
      (HierarchySymbol.DefinableFunction₂.comp (F := reflVal)
        (HierarchySymbol.DefinableFunction.var 0) (HierarchySymbol.DefinableFunction.var 1)))

/-- **The driver's induction predicate.** -/
def Θ (n p : V) : Prop :=
  ∃ f, IsSemiformula ℒₛₑₜ 2 f ∧ Provable (𝗭𝗙 : SetTheory) (invVal (envForm n p) f)

theorem Θ_definable : 𝚺₁-Relation (Θ : V → V → Prop) := by
  unfold Θ
  definability

/-! ## Typed views -/

/-- The typed view of `envForm n p`. -/
def envFormT (n : V) {m : V} {p : V} (hp : IsSemiformula ℒₛₑₜ m p) : SF V 1 :=
  ⟨envForm n p, by simpa using isSemiformula_envForm (d := n) hp⟩

theorem Θ_of_typed {n p : V} (P : SF V 1) (hP : P.val = envForm n p) (F : SF V 2)
    (h : (𝗭𝗙 : SetTheory).internalize V ⊢ InvT P F) : Θ n p :=
  ⟨F.val, F.isSemiformula, by
    have := Bootstrapping.tprovable_iff_provable.mp h
    rwa [invT_val, hP] at this⟩

theorem typed_of_Θ {n m p : V} (hp : IsSemiformula ℒₛₑₜ m p) (h : Θ n p) :
    ∃ F : SF V 2, (𝗭𝗙 : SetTheory).internalize V ⊢ InvT (envFormT n hp) F := by
  obtain ⟨f, hf, hprov⟩ := h
  refine ⟨⟨f, hf⟩, Bootstrapping.tprovable_iff_provable.mpr ?_⟩
  rw [invT_val]
  exact hprov

/-! ## Code identities -/

/-- Substituting `#0` for the only bound variable leaves a level-one code
alone, whatever the target level. -/
theorem subst_bvar0_val (P : SF V 1) {m : ℕ} (w : SemitermVec V ℒₛₑₜ 1 m)
    (hw : (w 0).val = ^#0) : (P.subst w).val = P.val := by
  have h1 := congrArg Bootstrapping.Semiformula.val (Bootstrapping.Semiformula.subst_eq_self₁ P)
  have hv : Bootstrapping.SemitermVec.val w =
      Bootstrapping.SemitermVec.val (![Bootstrapping.Semiterm.bvar 0] : SemitermVec V ℒₛₑₜ 1 1) := by
    simp [Bootstrapping.SemitermVec.val, Matrix.vecHead, Matrix.vecTail, hw]
  simp only [Bootstrapping.Semiformula.val_substs] at h1 ⊢
  rw [hv]
  exact h1

end LeanProofs.ZFCinPA.LDriver
