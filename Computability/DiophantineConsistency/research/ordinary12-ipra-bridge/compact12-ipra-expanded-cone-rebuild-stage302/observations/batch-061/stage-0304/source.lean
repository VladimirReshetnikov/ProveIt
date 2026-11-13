import ZFCinPA.SetRelativization
import ZFCinPA.LDriverSteps
import ZFCinPA.LTransVal
import ZFCinPA.SubstIdentity

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
  apply SubstIdentity.Semiformula.subst_bvarVec_val P w
  intro i
  rw [Fin.fin_one_eq_zero i]
  exact hw

theorem quote_neg_val {n : ℕ} (φ : SetTheorySemiproposition n) :
    (⌜∼φ⌝ : V) = neg ℒₛₑₜ (⌜φ⌝ : V) := by
  rw [Semiformula.quote_def, Semiformula.quote_def]
  exact congrArg Bootstrapping.Semiformula.val (Semiformula.typedQuote_neg (V := V) φ)

/-- A predicate placeholder read at `#0` under further binders keeps its code. -/
theorem tr_P₀sub_val (Ks : (i : Fin 6) → SF V (ar6 i)) {m : ℕ} :
    (translateFormula Ks (Rewriting.emb
      ((P₀ : Semisentence L6 1) ⇜ ![(#0 : Semiterm L6 Empty (m + 1))]))).val = (Ks 0).val := by
  rw [Rewriting.emb_subst_eq_subst_emb, translateFormula_subst, subst_bvar0_val _ _ rfl]
  simp [P₀]

theorem tr_P₂sub_val (Ks : (i : Fin 6) → SF V (ar6 i)) {m : ℕ} :
    (translateFormula Ks (Rewriting.emb
      ((P₂ : Semisentence L6 1) ⇜ ![(#0 : Semiterm L6 Empty (m + 1))]))).val = (Ks 2).val := by
  rw [Rewriting.emb_subst_eq_subst_emb, translateFormula_subst, subst_bvar0_val _ _ rfl]
  simp [P₂]

/-- The universal body is `envForm`'s universal clause. -/
theorem allT_val (P : SF V 1) :
    (AllT P).val = ^∀ ^∀ ((⌜∼econsP⌝ : V) ^⋎ ((⌜∼domYP⌝ : V) ^⋎ P.val)) := by
  simp [AllT, allBody, translateFormula, econsP, domYP]
  refine ⟨?_, ?_, tr_P₀sub_val _⟩
  · rw [quote_neg_val]; rfl
  · rw [quote_neg_val]; rfl

/-- The existential body is `envForm`'s existential clause. -/
theorem exT_val (P : SF V 1) :
    (ExT P).val = ^∃ ^∃ ((⌜econsP⌝ : V) ^⋏ ((⌜domYP⌝ : V) ^⋏ P.val)) := by
  simp [ExT, exBody, translateFormula, econsP, domYP]
  exact ⟨rfl, rfl, tr_P₀sub_val _⟩

/-- The membership-atom body is `envForm`'s atom at a nonzero relation code. -/
theorem atomT_val_mem (a b R : V) (hR : R ≠ 0) :
    (AtomT false (numChainQ a) (numChainQ b)).val = atomCode R a b := by
  simp [AtomT, memAtomBody, translateFormula, atomCode, hR]
  refine ⟨⟨tr_P₀sub_val _, ?_⟩, ⟨tr_P₂sub_val _, ?_⟩, ?_⟩
  · unfold appXCode; rw [coe_toNat_eq_quote]; rfl
  · unfold appYCode; rw [coe_toNat_eq_quote]; rfl
  · unfold memXYCode; rw [coe_toNat_eq_quote]; rfl

/-- The equality-atom body is `envForm`'s atom at relation code `0`. -/
theorem atomT_val_eq (a b : V) :
    (AtomT true (numChainQ a) (numChainQ b)).val = atomCode 0 a b := by
  simp [AtomT, eqAtomBody, translateFormula, atomCode]
  refine ⟨⟨tr_P₀sub_val _, ?_⟩, ⟨tr_P₂sub_val _, ?_⟩, ?_⟩
  · unfold appXCode; rw [coe_toNat_eq_quote]; rfl
  · unfold appYCode; rw [coe_toNat_eq_quote]; rfl
  · unfold eqXYCode; rw [coe_toNat_eq_quote]; rfl

/-! ## The induction -/

theorem isRel_set {k R : V} (hR : (ℒₛₑₜ).IsRel k R) : k = 2 ∧ (R = 0 ∨ R = 1) :=
  LeanProofs.ZFCinPA.SetRelativization.set_isRel hR

/-- **The driver**: for every internal semiformula code `p` of level `n`, some
function code `f` makes the reflection invariant of `envForm n p` an internal
`𝗭𝗙` theorem. -/
theorem driver {n p : V} (hp : IsSemiformula ℒₛₑₜ n p) : Θ n p := by
  refine IsSemiformula.sigma1_structural_induction (L := ℒₛₑₜ) (P := Θ) Θ_definable
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · intro n k R v hR hv
    obtain ⟨rfl, hR01⟩ := isRel_set hR
    have hrel := envForm_rel (d := n) hR hv.isUTerm
    rcases hR01 with rfl | rfl
    · exact Θ_of_typed (AtomT true (numChainQ (idx n v.[0])) (numChainQ (idx n v.[1])))
        (by rw [atomT_val_eq, hrel, atomOf]) _
        (atom_step true _ _ (LNumOK.numOK _) (LNumOK.numOK _))
    · exact Θ_of_typed (AtomT false (numChainQ (idx n v.[0])) (numChainQ (idx n v.[1])))
        (by rw [atomT_val_mem _ _ 1 _root_.one_ne_zero, hrel, atomOf]) _
        (atom_step false _ _ (LNumOK.numOK _) (LNumOK.numOK _))
  · intro n k R v hR hv
    obtain ⟨rfl, hR01⟩ := isRel_set hR
    have hrel := envForm_nrel (d := n) hR hv.isUTerm
    rcases hR01 with rfl | rfl
    · exact Θ_of_typed (∼AtomT true (numChainQ (idx n v.[0])) (numChainQ (idx n v.[1])))
        (by rw [Bootstrapping.Semiformula.val_neg, atomT_val_eq, hrel, atomOf]) _
        (neg_step _ _ (atom_step true _ _ (LNumOK.numOK _) (LNumOK.numOK _)))
    · exact Θ_of_typed (∼AtomT false (numChainQ (idx n v.[0])) (numChainQ (idx n v.[1])))
        (by rw [Bootstrapping.Semiformula.val_neg, atomT_val_mem _ _ 1 _root_.one_ne_zero, hrel, atomOf]) _
        (neg_step _ _ (atom_step false _ _ (LNumOK.numOK _) (LNumOK.numOK _)))
  · intro n
    exact Θ_of_typed ⊤ (by simp) _ top_base
  · intro n
    exact Θ_of_typed ⊥ (by simp) _ bot_base
  · intro n p q hp hq h₁ h₂
    obtain ⟨F₁', hF₁⟩ := typed_of_Θ hp h₁
    obtain ⟨F₃', hF₃⟩ := typed_of_Θ hq h₂
    exact Θ_of_typed _ (by simp [envFormT, envForm_and hp.isUFormula hq.isUFormula]) _
      (and_step _ _ _ _ hF₁ hF₃)
  · intro n p q hp hq h₁ h₂
    obtain ⟨F₁', hF₁⟩ := typed_of_Θ hp h₁
    obtain ⟨F₃', hF₃⟩ := typed_of_Θ hq h₂
    exact Θ_of_typed _ (by simp [envFormT, envForm_or hp.isUFormula hq.isUFormula]) _
      (or_step _ _ _ _ hF₁ hF₃)
  · intro n p hp ih
    obtain ⟨F₁', hF₁⟩ := typed_of_Θ hp ih
    exact Θ_of_typed _ (by rw [allT_val, envForm_all hp.isUFormula]; rfl) _ (all_step _ _ hF₁)
  · intro n p hp ih
    obtain ⟨F₁', hF₁⟩ := typed_of_Θ hp ih
    exact Θ_of_typed _ (by rw [exT_val, envForm_exs hp.isUFormula]; rfl) _ (ex_step _ _ hF₁)

/-- The driver, typed: the invariant of `envForm n p` at some function code. -/
theorem driverT {n p : V} (hp : IsSemiformula ℒₛₑₜ n p) :
    ∃ F : SF V 2, (𝗭𝗙 : SetTheory).internalize V ⊢ InvT (envFormT n hp) F :=
  typed_of_Θ hp (driver hp)

end LeanProofs.ZFCinPA.LDriver
