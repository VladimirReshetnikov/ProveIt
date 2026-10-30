import ZFCinPA.NativeZFContainers254
import ZFCinPA.InternalInterpretation
import Foundation.FirstOrder.Bootstrapping.DerivabilityCondition.D1
import ZFCinPA.ZFDelta1
import ZFCinPA.SetRelativization
import ZFCinPA.SubstIdentity
import BusyBeaver.ZFC.ConstructibleOrder

/-!
# The constructible interpretation of `𝗭𝗙𝗖` in `𝗭𝗙`, internalized

`SetRelativization.provable_falsum_of_relativize_set` turns an internal
`𝗭𝗙𝗖`-refutation into an internal `𝗭𝗙`-refutation in every model of `IΣ₁`, given a
domain formula `δ` and, for every internal axiom code `p` of `𝗭𝗙𝗖`, an internal
`𝗭𝗙`-derivation of `p^δ` (with side formulas `¬δ(&i)`). This module supplies
`δ = (x ∈ L)` and discharges every obligation except the separation and
replacement schemata at internal formula codes:

1. `inLSyn`: the repository's named formula for `x ∈ L`
   (`Constructible.inLF`) written without reference to a model, so that one
   syntactic object serves every model of `𝗭𝗙` (`inLSyn_eq` is `rfl`).
2. `domL`: its translation to a Foundation semisentence in one variable, with
   `eval_domL` stating that it defines `L` in every model of `𝗭𝗙`.
3. `relF`: external relativization of Foundation formulas, mirroring the
   internal `relativize` clause for clause; `eval_relF` evaluates it in the
   substructure carved out by `δ`, and `quote_relF` identifies its code with
   the internal relativization.
4. `L_models_fixed`: the constructible substructure of a model of `𝗭𝗙`
   satisfies the equality axioms, the seven fixed axioms of `𝗭𝗙` and `𝗔𝗖`
   (Gödel; the semantic work is `BusyBeaver.ZFC.ConstructibleZF` and
   `ConstructibleOrder`). By completeness `𝗭𝗙 ⊢ σ^L` for each of those
   sentences, and `𝗭𝗙 ⊢ ∃x (x ∈ L)`.
-/

namespace LeanProofs.ZFCinPA.ConstructibleInterpretation

/-! ## The constructibility formula, syntactically

`Constructible.inLF H hP x` is built from the operation bundle `defOp H hP`,
whose formula field is the model-independent `gdefF`. Unfolding the bundle
gives a formula that mentions no model. -/

section Syntactic

open SetTheory.BusyBeaver.ZFC.NamedZF SetTheory.BusyBeaver.ZFC.InternalOrd
  SetTheory.BusyBeaver.ZFC.InternalRank SetTheory.BusyBeaver.ZFC.ConstructibleDef

/-- `z ∈ Gdef t` (`TransRec.inGF` at `Gdef`'s graph). -/
def inGdefF (z t : Nat) : NForm :=
  .ex (z + t + 1) (.and (gdefF (z + t + 1) t) (.mem z (z + t + 1)))

/-- `f` approximates the constructible hierarchy on `d` (`TransRec.approxF`). -/
def approxLF (f d : Nat) : NForm :=
  let n := f + d + 1
  let c1 := NForm.all n (.imp (.mem n f) (.ex (n + 1) (.ex (n + 2)
    (.and (.mem (n + 1) d) (kpairF n (n + 1) (n + 2))))))
  let c2 := NForm.all n (.imp (.mem n d) (.ex (n + 1) (pmemF f n (n + 1))))
  let c3 := NForm.all n (.all (n + 1) (.all (n + 2)
    (.imp (.and (pmemF f n (n + 1)) (pmemF f n (n + 2))) (.eq (n + 1) (n + 2)))))
  let rhs := NForm.ex (n + 3) (.ex (n + 4) (.and (.mem (n + 3) n)
    (.and (pmemF f (n + 3) (n + 4)) (inGdefF (n + 2) (n + 4)))))
  let c4 := NForm.all n (.all (n + 1) (.imp (pmemF f n (n + 1))
    (.all (n + 2) ((NForm.mem (n + 2) (n + 1)).iff rhs))))
  .and c1 (.and c2 (.and c3 c4))

/-- `S = L_a` (`TransRec.isStageF`). -/
def isStageLF (a S : Nat) : NForm :=
  let n := a + S + 1
  .ex n (.and (.ex (n + 1) (.and (succF (n + 1) a) (approxLF n (n + 1)))) (pmemF n a S))

/-- `x ∈ L`, with free name `x`. -/
def inLSyn (x : Nat) : NForm :=
  .ex (x + 1) (.ex (x + 2) (.and (ordF (x + 1)) (.and (isStageLF (x + 1) (x + 2))
    (.mem x (x + 2)))))

/-- The model-indexed formula `inLF H hP` is the one syntactic formula `inLSyn`. -/
theorem inLSyn_eq {V : Type*} {mem : V → V → Prop} (H : _root_.SetTheory.ZFAxioms mem)
    (hP : ∀ a, ∃ p, ∀ x, mem x p ↔ _root_.SetTheory.Sub mem x a) (x : Nat) :
    inLSyn x = SetTheory.BusyBeaver.ZFC.Constructible.inLF H hP x := rfl

/-- `x ∈ L` as a De Bruijn formula with free index `0`. -/
def inLForm : _root_.SetTheory.Form := toForm id (inLSyn 0)

theorem sat_inLForm {V : Type*} {mem : V → V → Prop} (H : _root_.SetTheory.ZFAxioms mem)
    (hP : ∀ a, ∃ p, ∀ x, mem x p ↔ _root_.SetTheory.Sub mem x a) (e : ℕ → V) :
    _root_.SetTheory.Sat mem e inLForm ↔ SetTheory.BusyBeaver.ZFC.Constructible.InL H hP (e 0) := by
  rw [inLForm, sat_toForm, inLSyn_eq H hP]
  exact SetTheory.BusyBeaver.ZFC.Constructible.nsat_inLF H hP _ 0

end Syntactic

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open NativeZFContainers254 (memRel toSet eval_toSet)
open SetTheory.BusyBeaver.ZFC.Constructible (InL)

/-- A set-language term selects the same source variable under two maps. -/
theorem term_cases_between {S A B ξ : Type*} [Structure ℒₛₑₜ A] [Structure ℒₛₑₜ B]
    (g : S → A) (h : S → B) {n : ℕ} (t : Semiterm ℒₛₑₜ ξ n)
    (b : Fin n → S) (f : ξ → S) :
    ∃ u : S, t.val (g ∘ b) (g ∘ f) = g u ∧ t.val (h ∘ b) (h ∘ f) = h u := by
  cases t with
  | bvar i => exact ⟨b i, rfl, rfl⟩
  | fvar x => exact ⟨f x, rfl, rfl⟩
  | func g v => cases g

/-- Embedding commutes with substituting a vector of terms into a sentence. -/
lemma emb_comp_embSubsts_language {L : Language} {ξ ο : Type*} [IsEmpty ο] {n k : ℕ}
    (v : Fin k → Semiterm L ο n) :
    ((Rew.emb : Rew L ο n ξ n).comp (Rew.embSubsts v)) =
      Rew.embSubsts (fun i ↦ Rew.emb (v i)) := by
  ext x
  · simp [Rew.comp_app]
  · exact x.elim

lemma emb_comp_embSubsts {ξ ο : Type*} [IsEmpty ο] {n k : ℕ}
    (v : Fin k → Semiterm ℒₛₑₜ ο n) :
    ((Rew.emb : Rew ℒₛₑₜ ο n ξ n).comp (Rew.embSubsts v)) =
      Rew.embSubsts (fun i ↦ Rew.emb (v i)) :=
  emb_comp_embSubsts_language v

/-- A one-variable domain guard commutes with embedding. -/
lemma emb_guard {L : Language} {ξ ο : Type*} [IsEmpty ο] {n : ℕ}
    (δ : Semiformula L Empty 1) :
    (Rew.emb ▹ (Rew.embSubsts ![#0] ▹ δ : Semiformula L ο (n + 1)) :
      Semiformula L ξ (n + 1)) = Rew.embSubsts ![#0] ▹ δ := by
  have h : ((Rew.emb : Rew L ο (n + 1) ξ (n + 1)).comp (Rew.embSubsts ![#0])) =
      Rew.embSubsts ![#0] := by
    rw [emb_comp_embSubsts_language]
    congr 1
    funext i
    rw [Fin.fin_one_eq_zero i]
    simp
  rw [← TransitiveRewriting.comp_app, h]

/-- An atomic set interpretation parameterized by equality and membership formulas. -/
def paramAtom (E F : SetTheorySemisentence 2) {ξ : Type*} {n k : ℕ} :
    (ℒₛₑₜ).Rel k → (Fin k → Semiterm ℒₛₑₜ ξ n) → Semiformula ℒₛₑₜ ξ n
  | .eq, v => Rew.embSubsts v ▹ E
  | .mem, v => Rew.embSubsts v ▹ F

/-- Atomic evaluation from preservation of the two interpreted relations. -/
theorem eval_paramAtom {M S ξ : Type*} [SetStructure M] [SetStructure S] {P : M → Prop}
    (g : {x // P x} → S) (E F : SetTheorySemisentence 2) (rE rF : M → M → Prop)
    (hE : ∀ (w : Fin 2 → M) (ε : Empty → M), E.Eval w ε ↔ rE (w 0) (w 1))
    (hF : ∀ (w : Fin 2 → M) (ε : Empty → M), F.Eval w ε ↔ rF (w 0) (w 1))
    (hEq : ∀ u v : {x // P x}, rE u.1 v.1 ↔ g u = g v)
    (hMem : ∀ u v : {x // P x}, rF u.1 v.1 ↔ g u ∈ g v)
    {n k : ℕ} (R : (ℒₛₑₜ).Rel k) (v : Fin k → Semiterm ℒₛₑₜ ξ n)
    (b : Fin n → {x // P x}) (f : ξ → {x // P x}) :
    (paramAtom E F R v).Eval (Subtype.val ∘ b) (Subtype.val ∘ f) ↔
      (Semiformula.rel R v).Eval (g ∘ b) (g ∘ f) := by
  cases R with
  | eq =>
      obtain ⟨u0, h0, h0'⟩ := ConstructibleInterpretation.term_cases_between Subtype.val g (v 0) b f
      obtain ⟨u1, h1, h1'⟩ := ConstructibleInterpretation.term_cases_between Subtype.val g (v 1) b f
      simp only [paramAtom, Semiformula.eval_embSubsts, hE, Function.comp_apply]
      change rE _ _ ↔ (v 0).val (g ∘ b) (g ∘ f) = (v 1).val (g ∘ b) (g ∘ f)
      rw [h0, h1, h0', h1']
      exact hEq u0 u1
  | mem =>
      obtain ⟨u0, h0, h0'⟩ := ConstructibleInterpretation.term_cases_between Subtype.val g (v 0) b f
      obtain ⟨u1, h1, h1'⟩ := ConstructibleInterpretation.term_cases_between Subtype.val g (v 1) b f
      simp only [paramAtom, Semiformula.eval_embSubsts, hF, Function.comp_apply]
      change rF _ _ ↔ (v 0).val (g ∘ b) (g ∘ f) ∈ (v 1).val (g ∘ b) (g ∘ f)
      rw [h0, h1, h0', h1']
      exact hMem u0 u1

/-- Guarded universal quantification descends along a surjection. -/
theorem forall_guard {A B : Type*} {P : A → Prop} (g : {x // P x} → B)
    (hg : Function.Surjective g) (F : A → Prop) (G : B → Prop)
    (h : ∀ u, F u.1 ↔ G (g u)) :
    (∀ x, ¬P x ∨ F x) ↔ ∀ y, G y := by
  classical
  constructor
  · intro H y
    obtain ⟨⟨x, hx⟩, rfl⟩ := hg y
    exact (h ⟨x, hx⟩).mp ((H x).resolve_left (not_not.mpr hx))
  · intro H x
    by_cases hx : P x
    · exact Or.inr ((h ⟨x, hx⟩).mpr (H (g ⟨x, hx⟩)))
    · exact Or.inl hx

/-- Guarded existential quantification descends along a surjection. -/
theorem exists_guard {A B : Type*} {P : A → Prop} (g : {x // P x} → B)
    (hg : Function.Surjective g) (F : A → Prop) (G : B → Prop)
    (h : ∀ u, F u.1 ↔ G (g u)) :
    (∃ x, P x ∧ F x) ↔ ∃ y, G y := by
  constructor
  · rintro ⟨x, hx, hF⟩
    exact ⟨g ⟨x, hx⟩, (h ⟨x, hx⟩).mp hF⟩
  · rintro ⟨y, hG⟩
    obtain ⟨⟨x, hx⟩, rfl⟩ := hg y
    exact ⟨x, hx, (h ⟨x, hx⟩).mpr hG⟩

/-! ## The domain formula -/

/-- `x ∈ L` as a Foundation semisentence in one variable. -/
noncomputable def domL : SetTheorySemisentence 1 :=
  Rew.rewrite (fun _ => (#0 : Semiterm ℒₛₑₜ Empty 1)) ▹ toSet 1 inLForm

theorem eval_domL {V : Type*} [SetStructure V] (H : _root_.SetTheory.ZFAxioms (memRel V))
    (hP : ∀ a, ∃ p, ∀ x, memRel V x p ↔ _root_.SetTheory.Sub (memRel V) x a) (x : V)
    (ε : Empty → V) : domL.Eval ![x] ε ↔ InL H hP x := by
  rw [domL, Semiformula.eval_rewrite]
  have hf : (fun _ : ℕ => (#0 : Semiterm ℒₛₑₜ Empty 1).val ![x] ε) = fun _ => x := by
    funext; simp
  rw [hf]
  refine (eval_toSet inLForm 1 ![x] (fun _ => x) (fun _ => x) ?_ fun _ => rfl).trans
    (sat_inLForm H hP _)
  intro i
  rw [Fin.fin_one_eq_zero i]
  rfl

/-! ## External relativization -/

section Relativization

variable (δ : SetTheorySemisentence 1)

/-- The domain formula at binder depth `n + 1`, reading the innermost bound
variable. -/
noncomputable def domAt {ξ : Type*} (n : ℕ) : Semiformula ℒₛₑₜ ξ (n + 1) :=
  Rew.embSubsts ![#0] ▹ δ

/-- Relativization to `δ`, clause for clause the internal `relativize`. -/
noncomputable def relF {ξ : Type*} : {n : ℕ} → Semiformula ℒₛₑₜ ξ n → Semiformula ℒₛₑₜ ξ n
  | _, .rel R v => .rel R v
  | _, .nrel R v => .nrel R v
  | _, ⊤ => ⊤
  | _, ⊥ => ⊥
  | _, φ ⋏ ψ => relF φ ⋏ relF ψ
  | _, φ ⋎ ψ => relF φ ⋎ relF ψ
  | n, ∀⁰ φ => ∀⁰ (∼domAt δ n ⋎ relF φ)
  | n, ∃⁰ φ => ∃⁰ (domAt δ n ⋏ relF φ)

variable {ξ : Type*} {n : ℕ}

@[simp] lemma relF_rel {k} (R : (ℒₛₑₜ).Rel k) (v : Fin k → Semiterm ℒₛₑₜ ξ n) :
    relF δ (.rel R v) = .rel R v := rfl
@[simp] lemma relF_nrel {k} (R : (ℒₛₑₜ).Rel k) (v : Fin k → Semiterm ℒₛₑₜ ξ n) :
    relF δ (.nrel R v) = .nrel R v := rfl
@[simp] lemma relF_verum : relF δ (⊤ : Semiformula ℒₛₑₜ ξ n) = ⊤ := rfl
@[simp] lemma relF_falsum : relF δ (⊥ : Semiformula ℒₛₑₜ ξ n) = ⊥ := rfl
@[simp] lemma relF_and (φ ψ : Semiformula ℒₛₑₜ ξ n) : relF δ (φ ⋏ ψ) = relF δ φ ⋏ relF δ ψ := rfl
@[simp] lemma relF_or (φ ψ : Semiformula ℒₛₑₜ ξ n) : relF δ (φ ⋎ ψ) = relF δ φ ⋎ relF δ ψ := rfl
@[simp] lemma relF_all (φ : Semiformula ℒₛₑₜ ξ (n + 1)) :
    relF δ (∀⁰ φ) = ∀⁰ (∼domAt δ n ⋎ relF δ φ) := rfl
@[simp] lemma relF_exs (φ : Semiformula ℒₛₑₜ ξ (n + 1)) :
    relF δ (∃⁰ φ) = ∃⁰ (domAt δ n ⋏ relF δ φ) := rfl

/-- The domain formula commutes with embedding sentences into formulas. -/
lemma emb_domAt {ο : Type*} [IsEmpty ο] :
    (Rew.emb ▹ (domAt δ n : Semiformula ℒₛₑₜ ο (n + 1)) : Semiformula ℒₛₑₜ ξ (n + 1)) =
      domAt δ n :=
  emb_guard δ

/-- Relativization commutes with embedding sentences into formulas. -/
lemma emb_relF {ο : Type*} [IsEmpty ο] :
    ∀ {n : ℕ} (φ : Semiformula ℒₛₑₜ ο n),
      (Rew.emb ▹ relF δ φ : Semiformula ℒₛₑₜ ξ n) = relF δ (Rew.emb ▹ φ)
  | _, .rel R v => by simp
  | _, .nrel R v => by simp
  | _, ⊤ => by simp
  | _, ⊥ => by simp
  | _, φ ⋏ ψ => by simp [emb_relF φ, emb_relF ψ]
  | _, φ ⋎ ψ => by simp [emb_relF φ, emb_relF ψ]
  | _, ∀⁰ φ => by
      simp only [relF_all, Rewriting.app_all, Rew.q_emb, LogicalConnective.HomClass.map_or,
        LogicalConnective.HomClass.map_neg]
      rw [emb_domAt δ, emb_relF φ]
  | _, ∃⁰ φ => by
      simp only [relF_exs, Rewriting.app_exs, Rew.q_emb, LogicalConnective.HomClass.map_and]
      rw [emb_domAt δ, emb_relF φ]

end Relativization

/-! ## Evaluation in the substructure carved out by the domain -/

section Semantics

variable {V : Type*} [SetStructure V]

/-- A class of a set structure, as a set structure. -/
@[reducible] def subtypeSetStructure (P : V → Prop) : SetStructure {x // P x} :=
  ⟨fun s a => a.1 ∈ s.1⟩

attribute [local instance] subtypeSetStructure

variable (P : V → Prop)

lemma val_subtype {ξ : Type*} {n : ℕ} (t : Semiterm ℒₛₑₜ ξ n) (b : Fin n → {x // P x})
    (f : ξ → {x // P x}) :
    t.val (Subtype.val ∘ b) (Subtype.val ∘ f) = (t.val b f).1 := by
  obtain ⟨u, hu, hv⟩ := term_cases_between Subtype.val id t b f
  change t.val b f = u at hv
  exact hu.trans (congrArg Subtype.val hv.symm)

variable (δ : SetTheorySemisentence 1) (hδ : ∀ (x : V) (ε : Empty → V), δ.Eval ![x] ε ↔ P x)
include hδ

lemma eval_domAt {ξ : Type*} {n : ℕ} (x : V) (b : Fin n → V) (f : ξ → V) :
    (domAt δ n).Eval (x :> b) f ↔ P x := by
  have hv : (Semiterm.val (x :> b) f ∘ ![(#0 : Semiterm ℒₛₑₜ ξ (n + 1))]) = ![x] := by
    funext i
    rw [Fin.fin_one_eq_zero i]
    simp
  rw [domAt, Semiformula.eval_embSubsts, hv]
  exact hδ x Empty.elim

omit [SetStructure V] hδ in
lemma comp_vecCons_val {n : ℕ} (y : {x // P x}) (b : Fin n → {x // P x}) :
    (Subtype.val ∘ (y :> b)) = (y.1 :> Subtype.val ∘ b) :=
  funext fun i => Fin.cases rfl (fun _ => rfl) i

/-- **Relativization is evaluation in the substructure.** -/
theorem eval_relF {ξ : Type*} :
    ∀ {n : ℕ} (φ : Semiformula ℒₛₑₜ ξ n) (b : Fin n → {x // P x}) (f : ξ → {x // P x}),
      (relF δ φ).Eval (Subtype.val ∘ b) (Subtype.val ∘ f) ↔ φ.Eval b f
  | _, .rel R v, b, f => by
      cases R with
      | eq =>
          change ((v 0).val (Subtype.val ∘ b) (Subtype.val ∘ f) =
            (v 1).val (Subtype.val ∘ b) (Subtype.val ∘ f)) ↔ ((v 0).val b f = (v 1).val b f)
          rw [val_subtype, val_subtype]
          exact Subtype.ext_iff.symm
      | mem =>
          change ((v 0).val (Subtype.val ∘ b) (Subtype.val ∘ f) ∈
            (v 1).val (Subtype.val ∘ b) (Subtype.val ∘ f)) ↔ ((v 0).val b f ∈ (v 1).val b f)
          rw [val_subtype, val_subtype]
          exact Iff.rfl
  | _, .nrel R v, b, f => by
      cases R with
      | eq =>
          change ¬((v 0).val (Subtype.val ∘ b) (Subtype.val ∘ f) =
            (v 1).val (Subtype.val ∘ b) (Subtype.val ∘ f)) ↔ ¬((v 0).val b f = (v 1).val b f)
          rw [val_subtype, val_subtype]
          exact not_congr Subtype.ext_iff.symm
      | mem =>
          change ¬((v 0).val (Subtype.val ∘ b) (Subtype.val ∘ f) ∈
            (v 1).val (Subtype.val ∘ b) (Subtype.val ∘ f)) ↔ ¬((v 0).val b f ∈ (v 1).val b f)
          rw [val_subtype, val_subtype]
          exact Iff.rfl
  | _, ⊤, b, f => by simp
  | _, ⊥, b, f => by simp
  | _, φ ⋏ ψ, b, f => by
      simp only [relF_and, LogicalConnective.HomClass.map_and]
      exact and_congr (eval_relF φ b f) (eval_relF ψ b f)
  | _, φ ⋎ ψ, b, f => by
      simp only [relF_or, LogicalConnective.HomClass.map_or]
      exact or_congr (eval_relF φ b f) (eval_relF ψ b f)
  | _, ∀⁰ φ, b, f => by
      simp only [relF_all, Semiformula.eval_all, LogicalConnective.HomClass.map_or,
        LogicalConnective.HomClass.map_neg]
      constructor
      · intro h x
        have := (h x.1).resolve_left (by rw [eval_domAt P δ hδ]; exact not_not.mpr x.2)
        rw [← comp_vecCons_val] at this
        exact (eval_relF φ _ f).mp this
      · intro h x
        by_cases hx : P x
        · right
          have := (eval_relF φ (⟨x, hx⟩ :> b) f).mpr (h ⟨x, hx⟩)
          rwa [comp_vecCons_val] at this
        · left
          rw [eval_domAt P δ hδ]
          exact hx
  | _, ∃⁰ φ, b, f => by
      simp only [relF_exs, Semiformula.eval_ex, LogicalConnective.HomClass.map_and]
      constructor
      · rintro ⟨x, hx, h⟩
        rw [eval_domAt P δ hδ] at hx
        refine ⟨⟨x, hx⟩, (eval_relF φ _ f).mp ?_⟩
        rwa [comp_vecCons_val]
      · rintro ⟨x, h⟩
        refine ⟨x.1, (eval_domAt P δ hδ _ _ _).mpr x.2, ?_⟩
        have := (eval_relF φ (x :> b) f).mpr h
        rwa [comp_vecCons_val] at this

/-- A sentence holds relativized in `V` iff it holds in the substructure. -/
theorem models_relF_iff [Nonempty V] [Nonempty {x // P x}] (σ : SetTheorySentence) :
    V↓[ℒₛₑₜ] ⊧ relF δ σ ↔ {x // P x}↓[ℒₛₑₜ] ⊧ σ := by
  simp only [models_iff]
  have h := eval_relF P δ hδ σ ![] Empty.elim
  have hb : (Subtype.val ∘ (![] : Fin 0 → {x // P x})) = ![] := funext fun i => i.elim0
  have hf : (Subtype.val ∘ (Empty.elim : Empty → {x // P x})) = Empty.elim := funext fun i => i.elim
  rw [hb, hf] at h
  exact h

end Semantics

/-! ## Models of `𝗭𝗙` carry the repository's ZF bundle -/

section ZFModel

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- A model of `𝗭𝗙` is a model of `𝗭`. -/
theorem modelsZ_of_modelsZF : V↓[ℒₛₑₜ] ⊧* 𝗭 :=
  models_theory_iff.mpr fun _ hφ => models_of_mem (z_subset_zf hφ)

/-- The repository's Replacement clause, reusing the checked ordinary-ZF
extraction in NativeZFContainers254 (adapted there from Translation). -/
theorem repl_clauseZF (psi : _root_.SetTheory.Form) (e : ℕ → V)
    (hfun : _root_.SetTheory.Functional (_root_.SetTheory.relOf (memRel V) psi e)) (a : V) :
    ∃ r : V, ∀ y, y ∈ r ↔ ∃ x, x ∈ a ∧ _root_.SetTheory.relOf (memRel V) psi e y x :=
  NativeZFContainers254.repl_clause psi e hfun a

/-- **Bundle extraction for `𝗭𝗙`.** -/
theorem zfAxioms_of_modelsZF : _root_.SetTheory.ZFAxioms (memRel V) :=
  NativeZFContainers254.zfAxioms_of_models

theorem power_of_modelsZF :
    ∀ a : V, ∃ p, ∀ x, memRel V x p ↔ _root_.SetTheory.Sub (memRel V) x a :=
  NativeZFContainers254.pow_clause

theorem regular_of_modelsZF : SetTheory.BusyBeaver.ZFC.InternalOrd.Regular (memRel V) :=
  NativeZFContainers254.reg_clause

end ZFModel

/-- **The fixed axioms from a bundle**: equality axioms and the seven fixed
axioms of `𝗭𝗙` hold in any set structure with the six-field bundle, power
sets and regularity. -/
theorem fixed_models {S : Type*} [Nonempty S] [SetStructure S]
    (HL : _root_.SetTheory.ZFAxioms (memRel S))
    (hPow : ∀ x : S, ∃ p : S, ∀ z, z ∈ p ↔ ∀ u, u ∈ z → u ∈ x)
    (hReg : ∀ x : S, (∃ z, z ∈ x) → ∃ m, m ∈ x ∧ ¬∃ z, z ∈ m ∧ z ∈ x)
    (σ : SetTheorySentence) (hσ : σ ∈ 𝗘𝗤 ℒₛₑₜ ∪ zfFixed) : S↓[ℒₛₑₜ] ⊧ σ := by
  rcases hσ with hσ | hσ
  · exact models_of_mem (T := (𝗘𝗤 ℒₛₑₜ : SetTheory)) hσ
  · simp only [zfFixed, Set.mem_insert_iff, Set.mem_singleton_iff] at hσ
    rcases hσ with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · suffices ∃ x : S, ∀ y, y ∉ x by simpa [models_iff, Axiom.empty]
      obtain ⟨_, ⟨e0, -, he0⟩, -⟩ := HL.inf
      exact ⟨e0, he0⟩
    · suffices ∀ x y : S, x = y ↔ ∀ z, z ∈ x ↔ z ∈ y by
        simpa [models_iff, Axiom.extentionality]
      intro x y
      exact ⟨fun h => h ▸ fun _ => Iff.rfl, HL.ext x y⟩
    · suffices ∀ x y : S, ∃ z, ∀ v, v ∈ z ↔ v = x ∨ v = y by
        simpa [models_iff, Axiom.pairing]
      exact HL.pair
    · suffices ∀ x : S, ∃ y, ∀ z, z ∈ y ↔ ∃ v ∈ x, z ∈ v by
        simpa [models_iff, Axiom.union]
      intro x
      obtain ⟨w, hw⟩ := HL.union x
      refine ⟨w, fun z => (hw z).trans ?_⟩
      constructor <;> rintro ⟨v, h1, h2⟩ <;> exact ⟨v, h2, h1⟩
    · suffices ∀ x : S, ∃ y : S, ∀ z : S, z ∈ y ↔ ∀ u : S, u ∈ z → u ∈ x by
        simpa [models_iff, Axiom.power, isSubsetOf]
      exact hPow
    · suffices ∃ ω : S, (∀ e, (∀ z, z ∉ e) → e ∈ ω) ∧
          ∀ x ∈ ω, ∀ y, (∀ z, z ∈ y ↔ z = x ∨ z ∈ x) → y ∈ ω by
        simpa [models_iff, Axiom.infinity, isEmpty, isSucc, Rew.q_subst,
          Semiterm.val_substs, Function.comp_def]
      obtain ⟨I, ⟨e0, he0I, he0⟩, hsucc⟩ := HL.inf
      refine ⟨I, fun e he => ?_, fun x hx y hy => ?_⟩
      · have : e = e0 := HL.ext e e0 fun z =>
          ⟨fun h => absurd h (he z), fun h => absurd h (he0 z)⟩
        rw [this]
        exact he0I
      · obtain ⟨sx, hsxI, hsx⟩ := hsucc x hx
        have : y = sx := HL.ext y sx fun t => by
          rw [hsx t]
          exact (hy t).trans or_comm
        rw [this]
        exact hsxI
    · suffices ∀ x : S, (∃ z, z ∈ x) → ∃ y ∈ x, ∀ z ∈ x, z ∉ y by
        simpa [models_iff, Axiom.foundation, isNonempty]
      intro x hx
      obtain ⟨m, hm, hmin⟩ := hReg x hx
      exact ⟨m, hm, fun z hz hzm => hmin ⟨z, hzm, hz⟩⟩


/-! ## The constructible class of a model of `𝗭𝗙` -/

section LModel

open SetTheory.BusyBeaver.ZFC.InternalOrd SetTheory.BusyBeaver.ZFC.ConstructibleZF

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- `x ∈ L` in a model of `𝗭𝗙`. -/
abbrev InLV (x : V) : Prop := InL (zfAxioms_of_modelsZF (V := V)) power_of_modelsZF x

attribute [local instance] subtypeSetStructure

theorem inLV_nonempty : ∃ x : V, InLV x :=
  ⟨_, inL_ord _ regular_of_modelsZF _ (ord_of_mem (ord_omega _)
    (_root_.SetTheory.vempty_in_omega (zfAxioms_of_modelsZF (V := V))))⟩

instance : Nonempty {x : V // InLV x} := ⟨⟨_, inLV_nonempty.choose_spec⟩⟩

/-- **Gödel**: the constructible class satisfies the equality axioms, the
seven fixed axioms of `𝗭𝗙`, and the axiom of choice. -/
theorem L_models (σ : SetTheorySentence) (hσ : σ ∈ 𝗘𝗤 ℒₛₑₜ ∪ zfFixed ∪ 𝗔𝗖) :
    {x : V // InLV x}↓[ℒₛₑₜ] ⊧ σ := by
  have H := zfAxioms_of_modelsZF (V := V)
  have hR := regular_of_modelsZF (V := V)
  have hP := power_of_modelsZF (V := V)
  have HL := L_zfAxioms H hR hP
  rcases hσ with hσ | hσ
  · apply fixed_models HL ?_ (L_regular H hR hP) σ hσ
    intro x
    obtain ⟨p, hp⟩ := L_power H hR hP x
    exact ⟨p, fun z => (hp z).trans Iff.rfl⟩
  · rcases hσ
    suffices ∀ 𝓧 : {x : V // InLV x},
        (∀ X ∈ 𝓧, ∃ z, z ∈ X) →
        (∀ X ∈ 𝓧, ∀ Y ∈ 𝓧, (∃ x ∈ X, x ∈ Y) → X = Y) →
        ∃ C, ∀ X ∈ 𝓧, ∃! x, x ∈ C ∧ x ∈ X by
      simpa [models_iff, Axiom.choice, isNonempty, -Subtype.exists]
    intro 𝓧 hne hdisj
    have hch := SetTheory.BusyBeaver.ZFC.ConstructibleOrder.choice_of_VL HL (L_regular H hR hP)
      (L_power H hR hP) (SetTheory.BusyBeaver.ZFC.ConstructibleAbs.vEqL H hR hP)
    obtain ⟨C, hC⟩ := hch 𝓧 hne
      (fun X Y hX hY hXY ⟨z, hzX, hzY⟩ => hXY (hdisj X hX Y hY ⟨z, hzX, hzY⟩))
    refine ⟨C, fun X hX => ?_⟩
    obtain ⟨z, hzX, hzC, hz⟩ := hC X hX
    exact ⟨z, ⟨hzC, hzX⟩, fun w ⟨hwC, hwX⟩ => hz w hwX hwC⟩

end LModel

/-! ## The external theorems -/

/-- `𝗭𝗙 ⊢ σ^L` for every equality axiom, fixed axiom of `𝗭𝗙`, and `𝗔𝗖`. -/
theorem zf_proves_relL (σ : SetTheorySentence) (hσ : σ ∈ 𝗘𝗤 ℒₛₑₜ ∪ zfFixed ∪ 𝗔𝗖) :
    𝗭𝗙 ⊢ relF domL σ := by
  refine SetTheory.provable_of_models.{0} 𝗭𝗙 _ fun V _ _ _ => ?_
  exact (models_relF_iff (InLV (V := V)) domL
    (fun x ε => eval_domL zfAxioms_of_modelsZF power_of_modelsZF x ε) σ).mpr (L_models σ hσ)

/-- `𝗭𝗙 ⊢ ∃x (x ∈ L)`. -/
theorem zf_proves_exists_L : 𝗭𝗙 ⊢ (∃⁰ domL : SetTheorySentence) := by
  refine SetTheory.provable_of_models.{0} 𝗭𝗙 _ fun V _ _ _ => ?_
  obtain ⟨x, hx⟩ := inLV_nonempty (V := V)
  have h : ∃ y : V, domL.Eval ![y] Empty.elim :=
    ⟨x, (eval_domL zfAxioms_of_modelsZF power_of_modelsZF x _).mpr hx⟩
  simpa [models_iff] using h


/-! ## Internalization

Everything below lives in an arbitrary model `W` of `IΣ₁`: the codes are
internal, and the axiom classes are the arithmetized `Δ₁` classes, which
contain nonstandard codes in nonstandard models. The finite parts of `𝗭𝗙𝗖`
(equality axioms, the seven fixed axioms, `𝗔𝗖`) are disjunctions of standard
numerals, so their obligations are external theorems quoted by **D1**. -/

section Internal

open LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
  LeanProofs.BoundedPAConsistency.InternalRelativization

variable {W : Type*} [ORingStructure W] [W↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma quote_neg_set {n : ℕ} (ψ : SetTheorySemiproposition n) :
    (⌜∼ψ⌝ : W) = neg ℒₛₑₜ (⌜ψ⌝ : W) := by
  simp [LO.FirstOrder.Semiformula.quote_def]

lemma isUFormula_quote {n : ℕ} (ψ : SetTheorySemiproposition n) :
    IsUFormula ℒₛₑₜ (⌜ψ⌝ : W) :=
  (LO.FirstOrder.Semiformula.quote_isSemiformula ψ).isUFormula

lemma shift_quote_sen {k : ℕ} (σ : Semisentence ℒₛₑₜ k) : shift ℒₛₑₜ (⌜σ⌝ : W) = ⌜σ⌝ := by
  rw [LO.FirstOrder.Sentence.quote_def, ← LO.FirstOrder.Semiformula.quote_shift]
  congr 1
  rw [Rewriting.shift, ← TransitiveRewriting.comp_app, Rew.shift_comp_emb]

lemma isSemiformula_quote_sen {k : ℕ} (σ : Semisentence ℒₛₑₜ k) :
    IsSemiformula ℒₛₑₜ (k : W) (⌜σ⌝ : W) := by
  rw [LO.FirstOrder.Sentence.quote_def]
  simpa using LO.FirstOrder.Semiformula.quote_isSemiformula (V := W)
    (Rewriting.emb σ : SetTheorySemiproposition k)

/-- A quoted domain and two quoted relations form a good interpretation parameter. -/
lemma good_quoted_parameter {U : Type} [ORingStructure U] [U↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (D : Semisentence ℒₛₑₜ 1) (E F : Semisentence ℒₛₑₜ 2) :
    InternalInterpretation.Good (⟪(⌜D⌝ : U), ⟪(⌜E⌝ : U), (⌜F⌝ : U)⟫⟫ : U) := by
  have hd : InternalInterpretation.dom (⟪(⌜D⌝ : U), ⟪(⌜E⌝ : U), (⌜F⌝ : U)⟫⟫ : U) = ⌜D⌝ := by
    simp [InternalInterpretation.dom]
  have ha (R : U) : InternalInterpretation.atomOf (⟪(⌜D⌝ : U), ⟪(⌜E⌝ : U), (⌜F⌝ : U)⟫⟫ : U) R =
      if R = 0 then ⌜E⌝ else ⌜F⌝ := by simp [InternalInterpretation.atomOf]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hd]; simpa only [Nat.cast_one] using isSemiformula_quote_sen (W := U) D
  · rw [hd]; exact shift_quote_sen (W := U) D
  · intro R
    rw [ha]
    split_ifs
    · simpa using isSemiformula_quote_sen (W := U) E
    · simpa using isSemiformula_quote_sen (W := U) F
  · intro R
    rw [ha]
    split_ifs <;> exact shift_quote_sen _

lemma embSubsts_eq_comp_general {ξ : Type*} {n k : ℕ} (v : Fin k → Semiterm ℒₛₑₜ ξ n) :
    (Rew.embSubsts v : Rew ℒₛₑₜ Empty k ξ n) = (Rew.subst v).comp Rew.emb := by
  ext x
  · simp [Rew.comp_app]
  · exact x.elim

lemma quote_embSubsts {k n : ℕ} (σ : Semisentence ℒₛₑₜ k) (v : Fin k → SyntacticSemiterm ℒₛₑₜ n) :
    (⌜(Rew.embSubsts v ▹ σ : SetTheorySemiproposition n)⌝ : W) =
      subst ℒₛₑₜ (SemitermVec.val fun i ↦ (⌜v i⌝ : Bootstrapping.Semiterm W ℒₛₑₜ n)) ⌜σ⌝ := by
  rw [embSubsts_eq_comp_general, TransitiveRewriting.comp_app, LO.FirstOrder.Semiformula.quote_def,
    LO.FirstOrder.Semiformula.typed_quote_substs, Bootstrapping.Semiformula.val_substs,
    LO.FirstOrder.Sentence.quote_def, LO.FirstOrder.Semiformula.quote_def]

lemma embSubsts_eq_comp {ξ : Type*} {n : ℕ} :
    (Rew.embSubsts ![(#0 : Semiterm ℒₛₑₜ ξ (n + 1))] : Rew ℒₛₑₜ Empty 1 ξ (n + 1)) =
      (Rew.subst ![#0]).comp Rew.emb := embSubsts_eq_comp_general _

lemma subst_unary_bvar0 {p : W} {n : ℕ} (w : SemitermVec W ℒₛₑₜ 1 n)
    (hp : IsSemiformula ℒₛₑₜ 1 p) (hw0 : (w 0).val = ^#0) :
    subst ℒₛₑₜ (SemitermVec.val w) p = p := by
  have h := SubstIdentity.Semiformula.subst_bvarVec_val
    (⟨p, by simpa using hp⟩ : Bootstrapping.Semiformula W ℒₛₑₜ 1) w (by
      intro i
      rw [Fin.fin_one_eq_zero i]
      exact hw0)
  simpa only [Bootstrapping.Semiformula.val_substs] using h

/-- The domain formula has the same code at every binder depth. -/
lemma quote_domAt (n : ℕ) :
    (⌜(domAt domL n : SetTheorySemiproposition (n + 1))⌝ : W) = ⌜domL⌝ := by
  rw [domAt, quote_embSubsts]
  exact subst_unary_bvar0 _ (by simp) (by simp)

/-- **The code of the external relativization is the internal relativization
of the code.** -/
theorem quote_relF : ∀ {n : ℕ} (φ : SetTheorySemiproposition n),
    (⌜relF domL φ⌝ : W) = relativize ℒₛₑₜ (⌜domL⌝ : W) ⌜φ⌝
  | _, .rel R v => by
      have h := isUFormula_quote (W := W) (.rel R v : SetTheorySemiproposition _)
      rw [LO.FirstOrder.Semiformula.quote_rel] at h
      rw [relF_rel, LO.FirstOrder.Semiformula.quote_rel,
        relativize_rel (IsUFormula.rel.mp h).1 (IsUFormula.rel.mp h).2]
  | _, .nrel R v => by
      have h := isUFormula_quote (W := W) (.nrel R v : SetTheorySemiproposition _)
      rw [LO.FirstOrder.Semiformula.quote_nrel] at h
      rw [relF_nrel, LO.FirstOrder.Semiformula.quote_nrel,
        relativize_nrel (IsUFormula.nrel.mp h).1 (IsUFormula.nrel.mp h).2]
  | _, ⊤ => by simp
  | _, ⊥ => by simp
  | _, φ ⋏ ψ => by
      rw [relF_and, LO.FirstOrder.Semiformula.quote_and, LO.FirstOrder.Semiformula.quote_and,
        quote_relF φ, quote_relF ψ, relativize_and (isUFormula_quote φ) (isUFormula_quote ψ)]
  | _, φ ⋎ ψ => by
      rw [relF_or, LO.FirstOrder.Semiformula.quote_or, LO.FirstOrder.Semiformula.quote_or,
        quote_relF φ, quote_relF ψ, relativize_or (isUFormula_quote φ) (isUFormula_quote ψ)]
  | n, ∀⁰ φ => by
      rw [relF_all, LO.FirstOrder.Semiformula.quote_all, LO.FirstOrder.Semiformula.quote_or,
        quote_neg_set, quote_domAt, quote_relF φ, LO.FirstOrder.Semiformula.quote_all,
        relativize_all (isUFormula_quote φ)]
  | n, ∃⁰ φ => by
      rw [relF_exs, LO.FirstOrder.Semiformula.quote_ex, LO.FirstOrder.Semiformula.quote_and,
        quote_domAt, quote_relF φ, LO.FirstOrder.Semiformula.quote_ex,
        relativize_exs (isUFormula_quote φ)]

theorem quote_relF_sentence (σ : SetTheorySentence) :
    (⌜relF domL σ⌝ : W) = relativize ℒₛₑₜ (⌜domL⌝ : W) ⌜σ⌝ := by
  rw [LO.FirstOrder.Sentence.quote_def (relF domL σ), LO.FirstOrder.Sentence.quote_def σ]
  have h : (Rewriting.emb (relF domL σ) : SetTheoryProposition) = relF domL (Rewriting.emb σ) :=
    emb_relF domL σ
  rw [h]
  exact quote_relF _

lemma isSemiformula_quote_domL : IsSemiformula ℒₛₑₜ 1 (⌜domL⌝ : W) := by simp

lemma shift_quote_domL : shift ℒₛₑₜ (⌜domL⌝ : W) = ⌜domL⌝ := shift_quote_sen domL

/-- `Prov_ZF(∃x (x ∈ L))`. -/
theorem provable_exists_L : Provable 𝗭𝗙 (^∃ (⌜domL⌝ : W)) := by
  have h := internalize_provability (V := W) zf_proves_exists_L
  simpa [LO.FirstOrder.Sentence.quote_def] using h

/-! ### The internal axiom class of `𝗭𝗙𝗖` -/

lemma mem_class_union {T U : SetTheory} [T.Δ₁] [U.Δ₁] {p : W} :
    p ∈ (T ∪ U).Δ₁Class ↔ p ∈ T.Δ₁Class ∨ p ∈ U.Δ₁Class := FiniteTheoryRecognizer.union_class_iff T U p

/-- The internal `𝗭𝗙𝗖` axiom class splits into five parts. -/
lemma mem_ZFC_class {p : W} (h : p ∈ (𝗭𝗙𝗖 : SetTheory).Δ₁Class) :
    p ∈ (𝗘𝗤 ℒₛₑₜ : SetTheory).Δ₁Class ∨ p ∈ zfFixed.Δ₁Class ∨ p ∈ (𝗔𝗖 : SetTheory).Δ₁Class ∨
      p ∈ separationTheory.Δ₁Class ∨ p ∈ replacementTheory.Δ₁Class := by
  rcases mem_class_union.mp h with h | h
  · have h' : p ∈ (𝗘𝗤 ℒₛₑₜ ∪ zfFixed ∪ separationTheory ∪ replacementTheory : SetTheory).Δ₁Class :=
      h
    rcases mem_class_union.mp h' with h' | h'
    · rcases mem_class_union.mp h' with h' | h'
      · rcases mem_class_union.mp h' with h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr (Or.inr (Or.inl h')))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h')))
  · exact Or.inr (Or.inr (Or.inl h))

/-- A code in the class of a finite list theory is one of the listed codes. -/
lemma mem_ch_ofList {p : W} (l : List SetTheorySentence)
    (h : W ⊧/![p] (Theory.Δ₁.ofList l).ch.val) : ∃ σ ∈ l, p=⌜σ⌝ :=
  LeanProofs.ZFCinPA.SetRelativization.finite_mem_ch_ofList l h

lemma mem_ch_ofFinite (T : SetTheory) (hT : Set.Finite T) {p : W}
    (h : W ⊧/![p] (Theory.Δ₁.ofFinite T hT).ch.val) : ∃ σ ∈ T, p=⌜σ⌝ :=
  LeanProofs.ZFCinPA.SetRelativization.finite_mem_ch_ofFinite T hT h

lemma standard_of_mem_class {p : W}
    (hp : p ∈ (𝗘𝗤 ℒₛₑₜ : SetTheory).Δ₁Class ∨ p ∈ zfFixed.Δ₁Class ∨
      p ∈ (𝗔𝗖 : SetTheory).Δ₁Class) :
    ∃ σ ∈ 𝗘𝗤 ℒₛₑₜ ∪ zfFixed ∪ 𝗔𝗖, p = ⌜σ⌝ := by
  rcases hp with h | h | h
  · obtain ⟨σ, hσ, rfl⟩ := mem_ch_ofFinite (𝗘𝗤 ℒₛₑₜ) Theory.EqAxiom.finite h
    exact ⟨σ, Or.inl (Or.inl hσ), rfl⟩
  · obtain ⟨σ, hσ, rfl⟩ := mem_ch_ofList
      [Axiom.empty, Axiom.extentionality, Axiom.pairing, Axiom.union,
        Axiom.power, Axiom.infinity, Axiom.foundation] h
    exact ⟨σ, Or.inl (Or.inr (by simpa [zfFixed] using hσ)), rfl⟩
  · change W ⊧/![p] (Theory.Δ₁.singleton Axiom.choice).ch.val at h
    have h' : p = ORingStructure.numeral (Encodable.encode Axiom.choice) := by simpa using h
    exact ⟨Axiom.choice, Or.inr rfl, by
      rw [h', numeral_eq_natCast_app, LO.FirstOrder.Sentence.quote_eq_encode]⟩

/-- **The standard obligations.** Every internal code of an equality axiom, a
fixed axiom of `𝗭𝗙`, or `𝗔𝗖` has an internal `𝗭𝗙`-proof of its relativization
to `L` (with no side formulas). -/
theorem standard_obligation {p : W}
    (hp : p ∈ (𝗘𝗤 ℒₛₑₜ : SetTheory).Δ₁Class ∨ p ∈ zfFixed.Δ₁Class ∨
      p ∈ (𝗔𝗖 : SetTheory).Δ₁Class) :
    ∃ m, Derivable 𝗭𝗙 (insert (relativize ℒₛₑₜ (⌜domL⌝ : W) p) (domSet ℒₛₑₜ (⌜domL⌝ : W) m)) := by
  obtain ⟨σ, hσ, rfl⟩ := standard_of_mem_class hp
  refine ⟨0, ?_⟩
  have hempty : domSet ℒₛₑₜ (⌜domL⌝ : W) 0 = ∅ := mem_ext fun y => by simp [mem_domSet_iff]
  rw [hempty, ← quote_relF_sentence]
  exact (internalize_provability (zf_proves_relL σ hσ)).toDerivable

/-- **Choice transport in `IΣ₁`, up to the schemata.** In every model of
`IΣ₁`: if every internal separation and replacement axiom code has an internal
`𝗭𝗙`-proof of its relativization to `L` (with side formulas), then an internal
`𝗭𝗙𝗖`-refutation yields an internal `𝗭𝗙`-refutation. -/
theorem provable_falsum_ZF_of_ZFC
    (hSchema : ∀ p : W, IsFormula ℒₛₑₜ p →
      p ∈ separationTheory.Δ₁Class ∨ p ∈ replacementTheory.Δ₁Class →
      ∃ m, Derivable 𝗭𝗙 (insert (relativize ℒₛₑₜ (⌜domL⌝ : W) p) (domSet ℒₛₑₜ (⌜domL⌝ : W) m)))
    (h : Provable 𝗭𝗙𝗖 (^⊥ : W)) : Provable 𝗭𝗙 (^⊥ : W) :=
  SetRelativization.provable_falsum_of_relativize_set isSemiformula_quote_domL shift_quote_domL
    (fun p hp hmem => by
      rcases mem_ZFC_class hmem with h | h | h | h | h
      · exact standard_obligation (Or.inl h)
      · exact standard_obligation (Or.inr (Or.inl h))
      · exact standard_obligation (Or.inr (Or.inr h))
      · exact hSchema p hp (Or.inl h)
      · exact hSchema p hp (Or.inr h))
    provable_exists_L h

end Internal

end LeanProofs.ZFCinPA.ConstructibleInterpretation
