import ZFCinPA.ZFDelta1
import BoundedPAConsistency.ModelCodedPredicateTemplate

/-!
# Internalized Separation and ω-induction at a model-coded formula

A uniform proof compiler for `𝗭𝗙𝗖` eventually specializes fixed proof
templates at a formula whose Gödel code is an element of an arbitrary,
possibly nonstandard, model `V` of `𝗜𝚺₁`.  Such a formula cannot be decoded
into an ordinary Lean syntax tree.  Nevertheless `𝗭𝗙𝗖`'s represented
separation-schema recognizer accepts its separation body directly.

This is the set-theoretic analogue of the arithmetic project's
`BoundedPAConsistency.ModelCodedInductionAxiom`.  There PA's induction
recognizer accepted `indBody K`; here `𝗭𝗙𝗖`'s Δ₁ recognizer accepts
`sepBody K`, the typed Separation instance

```
∀ x, ∃ y, ∀ z, z ∈ y ↔ z ∈ x ∧ K(z)
```

of `ZFCinPA.SeparationDelta1`.  The only extra premise is
`shift ℒₛₑₜ K.val = K.val`: internal `shift` raises free-variable indices, so
this equation is the coded form of "`K` has no free variables".  The
recognizer then receives the particularly simple witnesses `m = 0` and
`b = sepBody K`: no universal-closure prefix is needed because the separation
body of a closed core is already a closed formula.

PA's induction axiom has no counterpart in `𝗭𝗙𝗖`; its replacement is this
internalized Separation instance together with a fixed finite source
derivation showing that ω-induction follows from it.  The second half of this
module compiles that derivation, once, through the generic typed template
proof compiler and packages the result as `zfcOmegaInductionOfShiftFixed`:

* Foundation's `Axiom.infinity` asserts only the existence of an *inductive*
  set (containing every empty set, closed under `isSucc`), not the existence
  of `ω` itself — `ℒₛₑₜ` has no constant for it.  ω-membership is therefore
  formulated as the standard class predicate `isVonNeumannNat`: membership in
  every inductive set.
* The base premise is necessarily relativized to `isEmpty` (`ℒₛₑₜ` has no
  term for `∅`): `∀ e, isEmpty e → K e`.
* Given also successor closure `∀ x x', K x → isSucc x' x → K x'`, the kernel
  concludes `∀ n, isVonNeumannNat n → K n`, with an honest internal `𝗭𝗙𝗖`
  proof code in `V`.
-/

set_option autoImplicit false

namespace LeanProofs.ZFCinPA.SeparationKernel

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA
open LeanProofs.BoundedPAConsistency.TypedTemplateProofCompiler
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateTemplate

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## The separation-schema disjunct of the `𝗭𝗙𝗖` recognizer

`𝗭𝗙𝗖`'s `Δ₁` characteristic decomposes, definitionally, into the five
recognizers assembled in `ZFCinPA.ZFDelta1`.  Membership in the internalized
theory therefore follows from acceptance by the separation recognizer alone. -/

/-- The `Δ₁` characteristic of `𝗭𝗙𝗖`, decomposed into its five recognizer
disjuncts.  This is definitional: `𝗭𝗙𝗖 = ((𝗘𝗤 ∪ zfFixed) ∪ sep) ∪ rep) ∪ 𝗔𝗖`
after `zf_eq`, and `Theory.Δ₁.add` takes the disjunction of characteristics. -/
lemma zfc_delta1ch_eq :
    (𝗭𝗙𝗖 : SetTheory).Δ₁ch
      = ((((𝗘𝗤 ℒₛₑₜ : SetTheory).Δ₁ch ⋎ zfFixed.Δ₁ch) ⋎ sepCh) ⋎ repCh)
          ⋎ (𝗔𝗖 : SetTheory).Δ₁ch := rfl

/-- A (possibly nonstandard) code accepted by the separation recognizer is a
member of `𝗭𝗙𝗖`'s internalized axiom class. -/
lemma mem_zfc_delta1Class_of_sepR {p : V} (hp : SepR p) :
    p ∈ (𝗭𝗙𝗖 : SetTheory).Δ₁Class := by
  change V ⊧/![p] ((𝗭𝗙𝗖 : SetTheory).Δ₁ch.val)
  rw [zfc_delta1ch_eq]
  simp only [HierarchySymbol.Semiformula.val_or,
    LogicalConnective.HomClass.map_or, LogicalConnective.Prop.or_eq]
  have h : V ⊧/![p] sepCh.val ↔ SepR p := by simp
  exact Or.inl (Or.inl (Or.inr (h.mpr hp)))

/-! ## Shift-fixedness of the separation body -/

/-- The typed separation body of a shift-fixed core is itself shift-fixed:
the skeleton atoms are quotations of standard formulas without free
variables, and the substitution vector `![#0]` consists of bound variables. -/
lemma sepBody_shift_fixed
    (K : Bootstrapping.Semiformula V ℒₛₑₜ 1)
    (hK : Bootstrapping.shift ℒₛₑₜ K.val = K.val) :
    (sepBody K).shift = sepBody K := by
  have hK' : K.shift = K := Bootstrapping.Semiformula.ext hK
  have hzy : (⌜sepAtomZY⌝ : Bootstrapping.Semiformula V ℒₛₑₜ 3).shift
      = ⌜sepAtomZY⌝ := by
    rw [← FirstOrder.Semiformula.typed_quote_shift]
    congr 1
    simp [sepAtomZY]
  have hzx : (⌜sepAtomZX⌝ : Bootstrapping.Semiformula V ℒₛₑₜ 3).shift
      = ⌜sepAtomZX⌝ := by
    rw [← FirstOrder.Semiformula.typed_quote_shift]
    congr 1
    simp [sepAtomZX]
  have hsub : (K.subst (![⌜(#0 : SyntacticSemiterm ℒₛₑₜ 3)⌝] :
        Bootstrapping.SemitermVec V ℒₛₑₜ 1 3)).shift
      = K.subst (![⌜(#0 : SyntacticSemiterm ℒₛₑₜ 3)⌝] :
        Bootstrapping.SemitermVec V ℒₛₑₜ 1 3) := by
    rw [Bootstrapping.Semiformula.shift_substs, hK']
    congr 1
    funext i
    simp [Matrix.cons_val_fin_one]
  simp only [sepBody, Bootstrapping.Semiformula.shift_all,
    Bootstrapping.Semiformula.shift_exs, Bootstrapping.Semiformula.shift_iff,
    Bootstrapping.Semiformula.shift_and, hzy, hzx, hsub]

/-! ## Δ₁-class membership of the model-coded separation instance -/

/-- The separation body of any closed model-coded unary formula is recognized
as a `𝗭𝗙𝗖` axiom.

For the schema recognizer we choose closure length `m = 0` and closure body
`b = sepBodyVal K.val`.  Shift invariance supplies the recognizer's
free-variable-freeness check; typed well-formedness supplies its `bv = 0`
check.  The recovered-core side condition is `sepBodyVal_eq` together with the
identity substitution `subst ℒₛₑₜ sepSubstConst K.val = K.val` (Foundation's
`subst_eq_self₁`), which converts `subst_le_sepBodyVal` into the required code
bound `K.val ≤ sepBodyVal K.val`. -/
lemma sepBody_mem_zfc_delta1Class_of_shift_fixed
    (K : Bootstrapping.Semiformula V ℒₛₑₜ 1)
    (hK : Bootstrapping.shift ℒₛₑₜ K.val = K.val) :
    (sepBody K).val ∈ (𝗭𝗙𝗖 : SetTheory).Δ₁Class := by
  apply mem_zfc_delta1Class_of_sepR
  rw [show (sepBody K).val = sepBodyVal K.val from (sepBodyVal_eq K).symm]
  have hsubstEmpty : Bootstrapping.subst ℒₛₑₜ (fvarVec 0) (sepBodyVal K.val)
      = sepBodyVal K.val := by
    have hbodySemi : IsSemiformula ℒₛₑₜ 0 (sepBodyVal K.val) := by
      rw [sepBodyVal_eq K]
      exact (sepBody K).isSemiformula_zero
    let body : Bootstrapping.Formula V ℒₛₑₜ := ⟨sepBodyVal K.val, hbodySemi⟩
    let emptyVec : Bootstrapping.SemitermVec V ℒₛₑₜ 0 0 := ![]
    have hempty : body.subst emptyVec = body := by simp
    rw [fvarVec_zero]
    change (body.subst emptyVec).val = body.val
    rw [hempty]
  have hidsub : Bootstrapping.subst ℒₛₑₜ ((sepSubstConst : ℕ) : V) K.val
      = K.val := by
    -- The raw code of `![#0]` does not depend on the ambient arity, so the
    -- level-3 substitution constant is also the code of the level-1 identity
    -- substitution, which fixes `K` by the typed `subst_eq_self₁`.
    have hvec :
        ((sepSubstConst : ℕ) : V)
          = Bootstrapping.SemitermVec.val
              (![Bootstrapping.Semiterm.bvar 0] :
                Bootstrapping.SemitermVec V ℒₛₑₜ 1 1) := by
      rw [val_sepSubstConst]
      simp [Bootstrapping.SemitermVec.val, Matrix.vecHead, Matrix.vecTail]
    rw [hvec,
      show Bootstrapping.subst ℒₛₑₜ
          (Bootstrapping.SemitermVec.val
            (![Bootstrapping.Semiterm.bvar 0] :
              Bootstrapping.SemitermVec V ℒₛₑₜ 1 1)) K.val
        = (K.subst (![Bootstrapping.Semiterm.bvar 0] :
            Bootstrapping.SemitermVec V ℒₛₑₜ 1 1)).val from rfl,
      Bootstrapping.Semiformula.subst_eq_self₁]
  refine ⟨0, by simp, sepBodyVal K.val, le_refl _, by simp, ?_, ?_, ?_,
    K.val, ?_, ?_, ?_⟩
  · rw [sepBodyVal_eq K]
    exact (sepBody K).isUFormula
  · rw [sepBodyVal_eq K]
    change (sepBody K).shift.val = (sepBody K).val
    exact congrArg Bootstrapping.Semiformula.val (sepBody_shift_fixed K hK)
  · have hsemi : IsSemiformula ℒₛₑₜ 0 (sepBodyVal K.val) := by
      rw [sepBodyVal_eq K]
      exact (sepBody K).isSemiformula_zero
    simpa [isSemiformula_iff] using hsemi.2
  · rw [hsubstEmpty]
    have h := subst_le_sepBodyVal (V := V) K.val
    rwa [hidsub] at h
  · simp
  · rw [hsubstEmpty]

/-! ## The internalized axiom -/

/-- A typed, model-internal `𝗭𝗙𝗖` proof of the Separation instance at `K`.

The proof code is a genuine element of `V`.  In particular, this constructor
also applies when `K.val` is nonstandard syntax produced by an internal
formula compiler. -/
noncomputable def zfcSeparationProofOfShiftFixed
    (K : Bootstrapping.Semiformula V ℒₛₑₜ 1)
    (hK : Bootstrapping.shift ℒₛₑₜ K.val = K.val) :
    (𝗭𝗙𝗖 : SetTheory).internalize V ⊢! sepBody K :=
  TProof.byAxm (sepBody_mem_zfc_delta1Class_of_shift_fixed K hK)

/-! ## The one-placeholder set-theoretic source language

The ω-induction derivation below is an ordinary finite proof over `ℒₛₑₜ`
enlarged by a single unary predicate placeholder.  The typed template proof
compiler then replaces the placeholder by the model-coded `K`.  This is the
`ℒₛₑₜ` counterpart of `ModelCodedPredicateTemplate`; since `ℒₛₑₜ` has no
function symbols, the term translation degenerates to variables and the
named-parameter mechanism of the arithmetic project is not needed. -/

/-- `ℒₛₑₜ` together with one distinguished unary relation. -/
@[reducible] def setTemplateLanguage : Language :=
  Language.add ℒₛₑₜ (placeholderLanguage 1)

instance : (setTemplateLanguage).DecidableEq where
  func := fun k ↦ by
    change DecidableEq ((ℒₛₑₜ).Func k ⊕ (placeholderLanguage 1).Func k)
    infer_instance
  rel := fun k ↦ by
    change DecidableEq ((ℒₛₑₜ).Rel k ⊕ (placeholderLanguage 1).Rel k)
    infer_instance

/-- The inclusion of `ℒₛₑₜ` into the placeholder-enlarged language. -/
noncomputable def setHom : ℒₛₑₜ →ᵥ setTemplateLanguage :=
  Language.Hom.add₁ ℒₛₑₜ (placeholderLanguage 1)

@[simp] theorem setHom_rel {k : ℕ} (r : (ℒₛₑₜ).Rel k) :
    setHom.rel r = Sum.inl r := rfl

/-! ## Specialization into typed `ℒₛₑₜ` syntax -/

section translation

variable {n m : ℕ}

/-- Interpret source terms as typed terms in the ambient model.  `ℒₛₑₜ` has no
function symbols, so a term is a variable; free-variable indices are embedded
as elements of the model. -/
noncomputable def translateTerm :
    SyntacticSemiterm setTemplateLanguage n → Bootstrapping.Semiterm V ℒₛₑₜ n
  | .bvar i => .bvar i
  | .fvar x => .fvar x
  | .func (Sum.inl f) _ => f.elim
  | .func (Sum.inr f) _ => f.elim

/-- Replace the placeholder atom by substitution into `K` and retain the
set-theoretic and logical constructors literally. -/
noncomputable def translateFormula
    (K : Bootstrapping.Semiformula V ℒₛₑₜ 1) :
    {n : ℕ} → Semiproposition setTemplateLanguage n →
      Bootstrapping.Semiformula V ℒₛₑₜ n
  | _, ⊤ => ⊤
  | _, ⊥ => ⊥
  | _, .rel (Sum.inl r) v => .rel r fun i ↦ translateTerm (v i)
  | _, .rel (Sum.inr .predicate) v => K.subst fun i ↦ translateTerm (v i)
  | _, .nrel (Sum.inl r) v => .nrel r fun i ↦ translateTerm (v i)
  | _, .nrel (Sum.inr .predicate) v => ∼(K.subst fun i ↦ translateTerm (v i))
  | _, p ⋏ q => translateFormula K p ⋏ translateFormula K q
  | _, p ⋎ q => translateFormula K p ⋎ translateFormula K q
  | _, ∀⁰ p => ∀⁰ translateFormula K p
  | _, ∃⁰ p => ∃⁰ translateFormula K p

/-! ### Compatibility with rewriting -/

@[simp] theorem translateTerm_shift
    (t : SyntacticSemiterm setTemplateLanguage n) :
    translateTerm (V := V) (Rew.shift t) =
      (translateTerm (V := V) t).shift := by
  induction t with
  | bvar i => simp [translateTerm]
  | fvar x => simp [translateTerm]
  | @func k f v ih => rcases f with f | f <;> exact f.elim

@[simp] theorem translateTerm_bShift
    (t : SyntacticSemiterm setTemplateLanguage n) :
    translateTerm (V := V) (Rew.bShift t) =
      (translateTerm (V := V) t).bShift := by
  induction t with
  | bvar i => simp [translateTerm]
  | fvar x => simp [translateTerm]
  | @func k f v ih => rcases f with f | f <;> exact f.elim

@[simp] theorem translateTerm_subst
    (w : Fin n → SyntacticSemiterm setTemplateLanguage m)
    (t : SyntacticSemiterm setTemplateLanguage n) :
    translateTerm (V := V) (Rew.subst w t) =
      (translateTerm (V := V) t).subst
        (fun i ↦ translateTerm (V := V) (w i)) := by
  induction t with
  | bvar i => simp [translateTerm]
  | fvar x => simp [translateTerm]
  | @func k f v ih => rcases f with f | f <;> exact f.elim

@[simp] theorem translateFormula_neg
    (K : Bootstrapping.Semiformula V ℒₛₑₜ 1)
    (p : Semiproposition setTemplateLanguage n) :
    translateFormula K (∼p) = ∼translateFormula K p := by
  induction p using FirstOrder.Semiformula.rec' with
  | hverum => simp [translateFormula]
  | hfalsum => simp [translateFormula]
  | hrel r v =>
      rcases r with r | r
      · simp [translateFormula]
      · cases r; simp [translateFormula]
  | hnrel r v =>
      rcases r with r | r
      · simp [translateFormula]
      · cases r; simp [translateFormula]
  | hand p q hp hq => simp [translateFormula, hp, hq]
  | hor p q hp hq => simp [translateFormula, hp, hq]
  | hall p hp => simp [translateFormula, hp]
  | hexs p hp => simp [translateFormula, hp]

@[simp] theorem translateFormula_shift
    (K : Bootstrapping.Semiformula V ℒₛₑₜ 1) (hK : K.shift = K)
    (p : Semiproposition setTemplateLanguage n) :
    translateFormula K (Rewriting.shift p) =
      (translateFormula K p).shift := by
  induction p using FirstOrder.Semiformula.rec' with
  | hverum => simp [translateFormula]
  | hfalsum => simp [translateFormula]
  | @hrel n k r v =>
      rcases r with r | r
      · simp [translateFormula, translateTerm_shift, Matrix.map,
          Function.comp_def]
      · cases r
        simp [translateFormula, Bootstrapping.Semiformula.shift_substs, hK,
          Matrix.map, Function.comp_def]
  | @hnrel n k r v =>
      rcases r with r | r
      · simp [translateFormula, translateTerm_shift, Matrix.map,
          Function.comp_def]
      · cases r
        simp [translateFormula, Bootstrapping.Semiformula.shift_substs, hK,
          Matrix.map, Function.comp_def]
  | hand p q hp hq => simp [translateFormula, hp, hq]
  | hor p q hp hq => simp [translateFormula, hp, hq]
  | hall p hp => simp [translateFormula, hp]
  | hexs p hp => simp [translateFormula, hp]

@[simp] theorem translateFormula_subst
    (K : Bootstrapping.Semiformula V ℒₛₑₜ 1)
    (w : Fin n → SyntacticSemiterm setTemplateLanguage m)
    (p : Semiproposition setTemplateLanguage n) :
    translateFormula K (Rew.subst w ▹ p) =
      (translateFormula K p).subst
        (fun i ↦ translateTerm (V := V) (w i)) := by
  induction p using FirstOrder.Semiformula.rec' generalizing m with
  | hverum => simp [translateFormula]
  | hfalsum => simp [translateFormula]
  | @hrel n k r v =>
      rcases r with r | r
      · simp [translateFormula, translateTerm_subst, Matrix.map,
          Function.comp_def]
      · cases r
        simp [translateFormula, Bootstrapping.Semiformula.substs_substs,
          translateTerm_subst, Matrix.map, Function.comp_def]
  | @hnrel n k r v =>
      rcases r with r | r
      · simp [translateFormula, translateTerm_subst, Matrix.map,
          Function.comp_def]
      · cases r
        simp [translateFormula, Bootstrapping.Semiformula.substs_substs,
          translateTerm_subst, Matrix.map, Function.comp_def]
  | hand p q hp hq => simp [translateFormula, hp, hq]
  | hor p q hp hq => simp [translateFormula, hp, hq]
  | hall p hp =>
      simp only [Rewriting.app_all, translateFormula,
        Bootstrapping.Semiformula.substs_all]
      rw [Rew.q_subst]
      rw [hp]
      congr 2
      funext i
      cases i using Fin.cases with
      | zero => rfl
      | succ i =>
          simp [Bootstrapping.SemitermVec.q, translateTerm_bShift, Matrix.map]
  | hexs p hp =>
      simp only [Rewriting.app_exs, translateFormula,
        Bootstrapping.Semiformula.substs_ex]
      rw [Rew.q_subst]
      rw [hp]
      congr 2
      funext i
      cases i using Fin.cases with
      | zero => rfl
      | succ i =>
          simp [Bootstrapping.SemitermVec.q, translateTerm_bShift, Matrix.map]

/-- The special `free` operation used by the universal proof rule also
commutes with placeholder specialization. -/
@[simp] theorem translateFormula_free
    (K : Bootstrapping.Semiformula V ℒₛₑₜ 1) (hK : K.shift = K)
    (p : Semiproposition setTemplateLanguage 1) :
    translateFormula K (Rewriting.free p) =
      (translateFormula K p).free := by
  rw [← LawfulSyntacticRewriting.app_subst_fbar_zero_comp_shift_eq_free]
  rw [translateFormula_subst, translateFormula_shift K hK]
  unfold Bootstrapping.Semiformula.free
  congr 1
  funext i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  rfl

/-! ### The compiler translation record -/

/-- The concrete syntax translation consumed by the generic typed template
proof compiler. -/
noncomputable def setTemplateTranslation
    (K : Bootstrapping.Semiformula V ℒₛₑₜ 1) (hK : K.shift = K) :
    TypedTemplateTranslation V setTemplateLanguage ℒₛₑₜ where
  term := translateTerm
  formula := translateFormula K
  formula_neg := translateFormula_neg K
  formula_and := fun _ _ ↦ rfl
  formula_or := fun _ _ ↦ rfl
  formula_verum := rfl
  formula_all := fun _ ↦ rfl
  formula_exs := fun _ ↦ rfl
  formula_shift := translateFormula_shift K hK
  formula_free := translateFormula_free K hK
  formula_subst₁ := fun p t ↦ by
    exact translateFormula_subst (V := V) K ![t] p

/-! ### Lifted `ℒₛₑₜ` material specializes to its quotation -/

/-- On the `ℒₛₑₜ` sublanguage, term specialization is ordinary typed
quotation. -/
@[simp] theorem translateTerm_lMap_set (t : SyntacticSemiterm ℒₛₑₜ n) :
    translateTerm (V := V) (t.lMap setHom) =
      (⌜t⌝ : Bootstrapping.Semiterm V ℒₛₑₜ n) := by
  induction t with
  | bvar i => rfl
  | fvar x => rfl
  | @func k f v ih => exact f.elim

/-- On formulas which do not mention the placeholder, specialization is
ordinary typed quotation. -/
@[simp] theorem translateFormula_lMap_set
    (K : Bootstrapping.Semiformula V ℒₛₑₜ 1)
    (p : SetTheorySemiproposition n) :
    translateFormula K (p.lMap setHom) =
      (⌜p⌝ : Bootstrapping.Semiformula V ℒₛₑₜ n) := by
  induction p using FirstOrder.Semiformula.rec' with
  | hverum => rfl
  | hfalsum => rfl
  | hrel r v =>
      simp only [FirstOrder.Semiformula.lMap_rel, setHom_rel, translateFormula]
      apply Bootstrapping.Semiformula.ext
      simp [translateTerm_lMap_set]
  | hnrel r v =>
      simp only [FirstOrder.Semiformula.lMap_nrel, setHom_rel, translateFormula]
      apply Bootstrapping.Semiformula.ext
      simp [translateTerm_lMap_set]
  | hand p q hp hq => simp [translateFormula, hp, hq]
  | hor p q hp hq => simp [translateFormula, hp, hq]
  | hall p hp => simp [translateFormula, hp]
  | hexs p hp => simp [translateFormula, hp]

/-- Sentence-level form of `translateFormula_lMap_set`: a lifted `ℒₛₑₜ`
sentence specializes to its typed quotation. -/
@[simp] theorem translateFormula_lMap_set_emb
    (K : Bootstrapping.Semiformula V ℒₛₑₜ 1) (σ : SetTheorySentence) :
    translateFormula K
        (Rewriting.emb (σ.lMap setHom) : Proposition setTemplateLanguage) =
      (⌜σ⌝ : Bootstrapping.Formula V ℒₛₑₜ) := by
  rw [← FirstOrder.Semiformula.lMap_emb, Sentence.typed_quote_def]
  exact translateFormula_lMap_set K (Rewriting.emb σ : SetTheoryProposition)

end translation

/-! ## The ω-induction source formulas

Foundation's `Axiom.infinity` asserts only the existence of an *inductive*
set — one containing every empty set and closed under `isSucc` — not the
existence of `ω` itself (`ℒₛₑₜ` has no constant for it).  The kernel therefore
formulates ω-membership as the standard class predicate "belongs to every
inductive set" (`isVonNeumannNat`), and ω-induction concludes
`∀ n, isVonNeumannNat n → K n`.  This is the strongest conclusion derivable
from one Separation instance at `K` plus Infinity: given an inductive set
`I₀` and the set `J = {z ∈ I₀ : K z}`, the base and successor premises make
`J` inductive, so every von Neumann natural lies in `J`. -/

/-- The membership atom of the source language. -/
def srcMem {n : ℕ} (t u : ClosedSemiterm setTemplateLanguage n) :
    Semisentence setTemplateLanguage n :=
  .rel (Sum.inl Language.Set.Rel.mem) ![t, u]

/-- The placeholder atom of the source language. -/
def srcP {n : ℕ} (t : ClosedSemiterm setTemplateLanguage n) :
    Semisentence setTemplateLanguage n :=
  .rel (Sum.inr PlaceholderRel.predicate) ![t]

/-- Lift a fixed `ℒₛₑₜ` formula into the source language. -/
noncomputable def liftSet {n : ℕ} (φ : SetTheorySemisentence n) :
    Semisentence setTemplateLanguage n :=
  φ.lMap setHom

/-- The source Separation instance at the placeholder:
`∀ x, ∃ y, ∀ z, z ∈ y ↔ z ∈ x ∧ P z`.  Its specialization is exactly
`sepBody K`. -/
noncomputable def srcSeparation : Sentence setTemplateLanguage :=
  ∀⁰ ∃⁰ ∀⁰ (srcMem #0 #1 🡘 (srcMem #0 #2 ⋏ srcP #0))

/-- An inductive set: one containing every empty set and closed under
successor.  Logically this is the matrix of Foundation's `Axiom.infinity`,
restated without formula splices so that it evaluates transparently in raw
structures of the template language. -/
def isInductive : SetTheorySemisentence 1 :=
  “I. (∀ e, (∀ z, z ∉ e) → e ∈ I) ∧
      (∀ x ∈ I, ∀ x', (∀ z, z ∈ x' ↔ (z = x ∨ z ∈ x)) → x' ∈ I)”

/-- The von Neumann natural numbers as a class predicate: membership in every
inductive set.  The inductive-set matrix is inlined (rather than spliced via
`!isInductive`) so that no substitution chains survive into evaluation. -/
def isVonNeumannNat : SetTheorySemisentence 1 :=
  “n. ∀ I, ((∀ e, (∀ z, z ∉ e) → e ∈ I) ∧
      (∀ x ∈ I, ∀ x', (∀ z, z ∈ x' ↔ (z = x ∨ z ∈ x)) → x' ∈ I)) → n ∈ I”

/-- Splice-free restatement of the axiom of infinity: some inductive set
exists.  `𝗭𝗙𝗖` proves it — it is `Axiom.infinity` up to unfolding of the
`isEmpty`/`isSucc` macros — and its lift is the only form of Infinity the
fixed source derivation consumes. -/
def inductiveSetExists : SetTheorySentence :=
  “∃ I, (∀ e, (∀ z, z ∉ e) → e ∈ I) ∧
      (∀ x ∈ I, ∀ x', (∀ z, z ∈ x' ↔ (z = x ∨ z ∈ x)) → x' ∈ I)”

/-- Source base premise: the placeholder holds of every empty set.  (`ℒₛₑₜ`
has no constant `∅`, so the base case is necessarily relativized to
`isEmpty`.) -/
noncomputable def srcOmegaZero : Sentence setTemplateLanguage :=
  ∀⁰ (liftSet isEmpty 🡒 srcP #0)

/-- Source successor premise: `∀ x ∀ x', P x → isSucc x' x → P x'`. -/
noncomputable def srcOmegaSucc : Sentence setTemplateLanguage :=
  ∀⁰ ∀⁰ (srcP #1 🡒 (liftSet isSucc 🡒 srcP #0))

/-- Source conclusion: the placeholder holds of every von Neumann natural. -/
noncomputable def srcOmegaConcl : Sentence setTemplateLanguage :=
  ∀⁰ (liftSet isVonNeumannNat 🡒 srcP #0)

/-- The complete source ω-induction sentence. -/
noncomputable def srcOmegaInduction : Sentence setTemplateLanguage :=
  srcOmegaZero 🡒 (srcOmegaSucc 🡒 srcOmegaConcl)

/-! ## Specialized shapes of the source formulas -/

section shapes

/-- `translateFormula_neg`, restated on the primitive negation so that it
also fires after `imp_eq`-style unfolding. -/
@[simp] theorem translateFormula_neg'
    (K : Bootstrapping.Semiformula V ℒₛₑₜ 1) {n : ℕ}
    (p : Semiproposition setTemplateLanguage n) :
    translateFormula K (FirstOrder.Semiformula.neg p) =
      ∼translateFormula K p :=
  translateFormula_neg K p

/-- Specialization commutes with implication (which is negation-normal-form
sugar on both sides). -/
@[simp] theorem translateFormula_imp
    (K : Bootstrapping.Semiformula V ℒₛₑₜ 1) {n : ℕ}
    (p q : Semiproposition setTemplateLanguage n) :
    translateFormula K (p 🡒 q) =
      translateFormula K p 🡒 translateFormula K q := by
  rw [FirstOrder.Semiformula.imp_eq, Bootstrapping.Semiformula.imp_def]
  simp [translateFormula]

/-- Specialization commutes with bi-implication. -/
@[simp] theorem translateFormula_iff
    (K : Bootstrapping.Semiformula V ℒₛₑₜ 1) {n : ℕ}
    (p q : Semiproposition setTemplateLanguage n) :
    translateFormula K (p 🡘 q) =
      translateFormula K p 🡘 translateFormula K q := by
  rw [show p 🡘 q = (p 🡒 q) ⋏ (q 🡒 p) from rfl,
    show translateFormula K p 🡘 translateFormula K q
      = (translateFormula K p 🡒 translateFormula K q)
        ⋏ (translateFormula K q 🡒 translateFormula K p) from rfl]
  simp [translateFormula, Bootstrapping.Semiformula.imp_def]

/-- Source bound variables specialize to typed bound variables. -/
@[simp] theorem translateTerm_bvar {n : ℕ} (i : Fin n) :
    translateTerm (V := V)
        (#i : SyntacticSemiterm setTemplateLanguage n) =
      .bvar i := rfl

/-- The lifted `ℒₛₑₜ` pieces of a source sentence specialize to their typed
quotations, at every arity. -/
@[simp] theorem translateFormula_emb_liftSet
    (K : Bootstrapping.Semiformula V ℒₛₑₜ 1) {n : ℕ}
    (φ : SetTheorySemisentence n) :
    translateFormula K
        (Rewriting.emb (liftSet φ) : Semiproposition setTemplateLanguage n) =
      (⌜φ⌝ : Bootstrapping.Semiformula V ℒₛₑₜ n) := by
  rw [liftSet, ← FirstOrder.Semiformula.lMap_emb, Sentence.typed_quote_def]
  exact translateFormula_lMap_set K
    (Rewriting.emb φ : SetTheorySemiproposition n)

/-- Typed quotation of `isEmpty`. -/
noncomputable def isEmptyQ : Bootstrapping.Semiformula V ℒₛₑₜ 1 := ⌜isEmpty⌝

/-- Typed quotation of `isSucc` (`#0` is the successor, `#1` the base). -/
noncomputable def isSuccQ : Bootstrapping.Semiformula V ℒₛₑₜ 2 := ⌜isSucc⌝

/-- Typed quotation of the von-Neumann-natural class predicate. -/
noncomputable def isVonNeumannNatQ : Bootstrapping.Semiformula V ℒₛₑₜ 1 :=
  ⌜isVonNeumannNat⌝

/-- Typed normal form of the quoted skeleton atom `z ∈ y`. -/
theorem sepAtomZY_typed_eq :
    (⌜sepAtomZY⌝ : Bootstrapping.Semiformula V ℒₛₑₜ 3) =
      Bootstrapping.Semiformula.rel Language.Set.Rel.mem
        ![.bvar 0, .bvar 1] := by
  rw [sepAtomZY, FirstOrder.Semiformula.typed_quote_rel]
  congr 1
  funext i
  match i with
  | 0 => simp
  | 1 => simp

/-- Typed normal form of the quoted skeleton atom `z ∈ x`. -/
theorem sepAtomZX_typed_eq :
    (⌜sepAtomZX⌝ : Bootstrapping.Semiformula V ℒₛₑₜ 3) =
      Bootstrapping.Semiformula.rel Language.Set.Rel.mem
        ![.bvar 0, .bvar 2] := by
  rw [sepAtomZX, FirstOrder.Semiformula.typed_quote_rel]
  congr 1
  funext i
  match i with
  | 0 => simp
  | 1 => simp

/-- Specialization of the embedded membership atom. -/
theorem translate_emb_srcMem {n : ℕ}
    (K : Bootstrapping.Semiformula V ℒₛₑₜ 1)
    (t u : ClosedSemiterm setTemplateLanguage n) :
    translateFormula K
        (Rewriting.emb (srcMem t u) : Semiproposition setTemplateLanguage n) =
      Bootstrapping.Semiformula.rel Language.Set.Rel.mem
        ![translateTerm (Rew.emb t), translateTerm (Rew.emb u)] := by
  rw [show (Rewriting.emb (srcMem t u) :
        Semiproposition setTemplateLanguage n)
      = FirstOrder.Semiformula.rel (Sum.inl Language.Set.Rel.mem)
          ![Rew.emb t, Rew.emb u] from by
    simp [srcMem]]
  rw [show translateFormula K
        (FirstOrder.Semiformula.rel (Sum.inl Language.Set.Rel.mem)
          ![Rew.emb t, Rew.emb u])
      = Bootstrapping.Semiformula.rel Language.Set.Rel.mem
          (fun i ↦ translateTerm ((![Rew.emb t, Rew.emb u]) i)) from rfl]
  congr 1
  funext i
  match i with
  | 0 => rfl
  | 1 => rfl

/-- Specialization of the embedded placeholder atom. -/
theorem translate_emb_srcP {n : ℕ}
    (K : Bootstrapping.Semiformula V ℒₛₑₜ 1)
    (t : ClosedSemiterm setTemplateLanguage n) :
    translateFormula K
        (Rewriting.emb (srcP t) : Semiproposition setTemplateLanguage n) =
      K.subst ![translateTerm (Rew.emb t)] := by
  rw [show (Rewriting.emb (srcP t) :
        Semiproposition setTemplateLanguage n)
      = FirstOrder.Semiformula.rel
          (Sum.inr PlaceholderRel.predicate) ![Rew.emb t] from by
    simp [srcP]]
  rw [show translateFormula K
        (FirstOrder.Semiformula.rel
          (Sum.inr PlaceholderRel.predicate) ![Rew.emb t])
      = K.subst (fun i ↦ translateTerm ((![Rew.emb t]) i)) from rfl]
  congr 1
  funext i
  match i with
  | 0 => rfl

/-- Literal specialization of the source Separation instance: it is the typed
separation body of `K`. -/
theorem translate_srcSeparation (K : Bootstrapping.Semiformula V ℒₛₑₜ 1) :
    translateFormula K
        (Rewriting.emb srcSeparation : Proposition setTemplateLanguage) =
      sepBody K := by
  simp only [srcSeparation, Rewriting.app_all, Rewriting.app_exs, Rew.q_emb,
    LogicalConnective.iff, FirstOrder.Semiformula.imp_eq,
    Bootstrapping.Semiformula.imp_def,
    LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_or,
    LogicalConnective.HomClass.map_neg,
    translateFormula, translateFormula_neg,
    translate_emb_srcMem, translate_emb_srcP, Rew.emb_bvar,
    translateTerm_bvar, sepBody, sepAtomZY_typed_eq, sepAtomZX_typed_eq,
    Semiterm.typed_quote_bvar]

/-- Literal specialization of the source base premise. -/
theorem translate_srcOmegaZero (K : Bootstrapping.Semiformula V ℒₛₑₜ 1) :
    translateFormula K
        (Rewriting.emb srcOmegaZero : Proposition setTemplateLanguage) =
      ∀⁰ (isEmptyQ 🡒 K) := by
  simp only [srcOmegaZero, Rewriting.app_all, Rew.q_emb,
    FirstOrder.Semiformula.imp_eq, Bootstrapping.Semiformula.imp_def,
    LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
    translateFormula, translateFormula_neg,
    translateFormula_emb_liftSet, translate_emb_srcP, Rew.emb_bvar,
    translateTerm_bvar, isEmptyQ]
  rw [Bootstrapping.Semiformula.subst_eq_self₁ K]

/-- Literal specialization of the source successor premise. -/
theorem translate_srcOmegaSucc (K : Bootstrapping.Semiformula V ℒₛₑₜ 1) :
    translateFormula K
        (Rewriting.emb srcOmegaSucc : Proposition setTemplateLanguage) =
      ∀⁰ ∀⁰ (K.subst ![.bvar 1] 🡒 (isSuccQ 🡒 K.subst ![.bvar 0])) := by
  simp only [srcOmegaSucc, Rewriting.app_all, Rew.q_emb,
    FirstOrder.Semiformula.imp_eq, Bootstrapping.Semiformula.imp_def,
    LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
    translateFormula, translateFormula_neg,
    translateFormula_emb_liftSet, translate_emb_srcP, Rew.emb_bvar,
    translateTerm_bvar, isSuccQ]

/-- Literal specialization of the source conclusion. -/
theorem translate_srcOmegaConcl (K : Bootstrapping.Semiformula V ℒₛₑₜ 1) :
    translateFormula K
        (Rewriting.emb srcOmegaConcl : Proposition setTemplateLanguage) =
      ∀⁰ (isVonNeumannNatQ 🡒 K) := by
  simp only [srcOmegaConcl, Rewriting.app_all, Rew.q_emb,
    FirstOrder.Semiformula.imp_eq, Bootstrapping.Semiformula.imp_def,
    LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
    translateFormula, translateFormula_neg,
    translateFormula_emb_liftSet, translate_emb_srcP, Rew.emb_bvar,
    translateTerm_bvar, isVonNeumannNatQ]
  rw [Bootstrapping.Semiformula.subst_eq_self₁ K]

/-- Literal specialization of the complete source ω-induction sentence. -/
theorem translate_srcOmegaInduction
    (K : Bootstrapping.Semiformula V ℒₛₑₜ 1) :
    translateFormula K
        (Rewriting.emb srcOmegaInduction : Proposition setTemplateLanguage) =
      ((∀⁰ (isEmptyQ 🡒 K)) 🡒
        ((∀⁰ ∀⁰ (K.subst ![.bvar 1] 🡒 (isSuccQ 🡒 K.subst ![.bvar 0]))) 🡒
          (∀⁰ (isVonNeumannNatQ 🡒 K)))) := by
  simp only [srcOmegaInduction, LogicalConnective.HomClass.map_imply,
    translateFormula_imp, translate_srcOmegaZero, translate_srcOmegaSucc,
    translate_srcOmegaConcl]

end shapes

/-! ## The source theory and its compilation -/

/-- The ω-induction source theory: all of `𝗭𝗙𝗖`, lifted into the placeholder
language, together with the Separation instance at the placeholder. -/
noncomputable def omegaSourceTheory : Theory setTemplateLanguage :=
  insert srcSeparation (Theory.lMap setHom 𝗭𝗙𝗖)

/-- Every axiom of the source theory specializes to a member of the
internalized `𝗭𝗙𝗖`: a lifted axiom to its own quotation, the placeholder
Separation instance to the recognized `sepBody K`. -/
noncomputable def omegaTheoryTranslation
    (K : Bootstrapping.Semiformula V ℒₛₑₜ 1)
    (hK : Bootstrapping.shift ℒₛₑₜ K.val = K.val) :
    TypedTheoryTemplateTranslation omegaSourceTheory
      ((𝗭𝗙𝗖 : SetTheory).internalize V) where
  toTypedTemplateTranslation :=
    setTemplateTranslation K (Bootstrapping.Semiformula.ext hK)
  axiom_mem := by
    intro σ hσ
    rcases Set.mem_insert_iff.mp hσ with rfl | ⟨τ, hτ, rfl⟩
    · change translateFormula K
        (Rewriting.emb srcSeparation : Proposition setTemplateLanguage) ∈' _
      rw [translate_srcSeparation]
      exact sepBody_mem_zfc_delta1Class_of_shift_fixed K hK
    · change translateFormula K
        (Rewriting.emb (τ.lMap setHom) : Proposition setTemplateLanguage) ∈' _
      rw [translateFormula_lMap_set_emb]
      exact (Bootstrapping.Δ₁Class.mem_iff''
        (T := (𝗭𝗙𝗖 : SetTheory))).mpr hτ

/-- Compile a fixed ordinary proof over the source theory into a represented
`𝗭𝗙𝗖` proof about the chosen model-coded predicate. -/
noncomputable def compileOmegaTemplate
    (K : Bootstrapping.Semiformula V ℒₛₑₜ 1)
    (hK : Bootstrapping.shift ℒₛₑₜ K.val = K.val)
    {σ : Sentence setTemplateLanguage}
    (d : omegaSourceTheory ⊢! σ) :
    (𝗭𝗙𝗖 : SetTheory).internalize V ⊢!
      translateFormula K (Rewriting.emb σ) :=
  (omegaTheoryTranslation K hK).compileProof d

/-! ## The fixed source derivation of ω-induction

The derivation is produced once, by completeness, from the standard semantic
argument: an inductive set `I₀` exists by (lifted, splice-free) Infinity; the
placeholder Separation instance yields `J = {z ∈ I₀ : P z}`; the base and
successor premises make `J` inductive; hence every set belonging to all
inductive sets belongs to `J` and satisfies `P`.  The placeholder and the
membership relation are interpreted arbitrarily, and no equality reasoning
occurs — the successor description is carried around opaquely — so raw
first-order structures suffice. -/

/-- One quantifier depth over a unary substitution keeps the next bound
variable in place, up to `bShift`. -/
private lemma subst_q_bvar_one {L : Language} {ξ : Type*} {n : ℕ}
    (t : Semiterm L ξ n) :
    (Rew.subst ![t]).q (#1 : Semiterm L ξ 2) = Rew.bShift t := by
  change (Rew.subst ![t]).q (#(Fin.succ (0 : Fin 1))) = _
  rw [Rew.q_bvar_succ, Rew.subst_bvar]
  simp

/-- Binary-substitution variant of `subst_q_bvar_one`, first slot. -/
private lemma subst2_q_bvar_one {L : Language} {ξ : Type*} {n : ℕ}
    (t u : Semiterm L ξ n) :
    (Rew.subst ![t, u]).q (#1 : Semiterm L ξ 3) = Rew.bShift t := by
  change (Rew.subst ![t, u]).q (#(Fin.succ (0 : Fin 2))) = _
  rw [Rew.q_bvar_succ, Rew.subst_bvar]
  simp

/-- Binary-substitution variant of `subst_q_bvar_one`, second slot. -/
private lemma subst2_q_bvar_two {L : Language} {ξ : Type*} {n : ℕ}
    (t u : Semiterm L ξ n) :
    (Rew.subst ![t, u]).q (#2 : Semiterm L ξ 3) = Rew.bShift u := by
  change (Rew.subst ![t, u]).q (#(Fin.succ (1 : Fin 2))) = _
  rw [Rew.q_bvar_succ, Rew.subst_bvar]
  simp

/-- `𝗭𝗙𝗖` proves the splice-free Infinity: semantically immediate from
`Axiom.infinity` in any set-structure model. -/
theorem zfc_proves_inductiveSetExists : 𝗭𝗙𝗖 ⊢ inductiveSetExists := by
  refine SetTheory.provable_of_models.{0} 𝗭𝗙𝗖 inductiveSetExists ?_
  intro M _ _ _
  have hax : M↓[ℒₛₑₜ] ⊧ Axiom.infinity :=
    Theory.models M 𝗭𝗙𝗖 (Set.mem_union_left _ ZermeloFraenkel.axiom_of_infinity)
  simp [models_iff, Axiom.infinity, isEmpty, isSucc,
    subst_q_bvar_one, subst2_q_bvar_one, subst2_q_bvar_two] at hax
  simpa [models_iff, inductiveSetExists] using hax

/-- Transport the splice-free Infinity into the source theory. -/
noncomputable def liftedInductiveSetExistsProof :
    omegaSourceTheory ⊢! (Semiformula.lMap setHom inductiveSetExists) :=
  (Theory.Proof.small_complete <|
    Semantics.weakening
      (lMap_models_lMap (Theory.Proof.sound zfc_proves_inductiveSetExists))
      (Set.subset_insert _ _)).get

/-- The fixed source derivation of ω-induction. -/
noncomputable def omegaSourceProof : omegaSourceTheory ⊢! srcOmegaInduction :=
  (Theory.Proof.small_complete <| consequence_iff.mpr fun M _ _ hmodels ↦ by
    haveI := hmodels
    have hsep : M↓[setTemplateLanguage] ⊧ srcSeparation :=
      models_of_mem (T := omegaSourceTheory) (Set.mem_insert _ _)
    have hinf : M↓[setTemplateLanguage] ⊧
        (Semiformula.lMap setHom inductiveSetExists) :=
      models_of_provable hmodels
        (show omegaSourceTheory ⊢ Semiformula.lMap setHom inductiveSetExists
          from ⟨liftedInductiveSetExistsProof⟩)
    have hmem : (Language.Mem.mem : (ℒₛₑₜ).Rel 2) = Language.Set.Rel.mem := rfl
    have heqr : (Language.Eq.eq : (ℒₛₑₜ).Rel 2) = Language.Set.Rel.eq := rfl
    simp [models_iff, srcSeparation, srcMem, srcP, inductiveSetExists,
      FirstOrder.Semiformula.ballMem, FirstOrder.Semiformula.ball_eq,
      FirstOrder.Semiformula.Operator.mem_def,
      FirstOrder.Semiformula.Operator.eq_def, LogicalConnective.iff,
      Function.comp_def, Matrix.comp_vecCons',
      hmem, heqr] at hsep hinf
    simp [models_iff, srcOmegaInduction, srcOmegaZero, srcOmegaSucc,
      srcOmegaConcl, srcP, liftSet, isVonNeumannNat, isEmpty, isSucc,
      FirstOrder.Semiformula.ballMem, FirstOrder.Semiformula.ball_eq,
      FirstOrder.Semiformula.Operator.mem_def,
      FirstOrder.Semiformula.Operator.eq_def, LogicalConnective.iff,
      Function.comp_def, Matrix.comp_vecCons',
      hmem, heqr]
    intro hzero hsucc n hn
    obtain ⟨I₀, hI₀e, hI₀s⟩ := hinf
    obtain ⟨J, hJ⟩ := hsep I₀
    refine ((hJ n).1 (hn J ?_ ?_)).2
    · intro e he
      exact (hJ e).2 (hI₀e e he) (hzero e he)
    · intro x hxJ x' hx'
      obtain ⟨hxI₀, hPx⟩ := (hJ x).1 hxJ
      exact (hJ x').2 (hI₀s x hxI₀ x' hx') (hsucc x x' hPx hx')).get

/-! ## The ω-induction kernel -/

/-- **ω-induction at a model-coded predicate.**  Given internal `𝗭𝗙𝗖` proofs
that `K` holds of every empty set and that `K` is closed under successor,
produce an internal `𝗭𝗙𝗖` proof that `K` holds of every von Neumann natural
(every member of every inductive set).

Both premises and the conclusion may mention a nonstandard formula code; the
result's `.val` is an internal `𝗭𝗙𝗖` proof code.  This is the set-theoretic
analogue of `paInductionOfShiftFixed`. -/
noncomputable def zfcOmegaInductionOfShiftFixed
    (K : Bootstrapping.Semiformula V ℒₛₑₜ 1)
    (hK : Bootstrapping.shift ℒₛₑₜ K.val = K.val)
    (hzero : (𝗭𝗙𝗖 : SetTheory).internalize V ⊢! ∀⁰ (isEmptyQ 🡒 K))
    (hsucc : (𝗭𝗙𝗖 : SetTheory).internalize V ⊢!
      ∀⁰ ∀⁰ (K.subst ![.bvar 1] 🡒 (isSuccQ 🡒 K.subst ![.bvar 0]))) :
    (𝗭𝗙𝗖 : SetTheory).internalize V ⊢! ∀⁰ (isVonNeumannNatQ 🡒 K) := by
  have h := compileOmegaTemplate K hK omegaSourceProof
  rw [translate_srcOmegaInduction] at h
  exact TProof.modusPonens (TProof.modusPonens h hzero) hsucc

end LeanProofs.ZFCinPA.SeparationKernel
