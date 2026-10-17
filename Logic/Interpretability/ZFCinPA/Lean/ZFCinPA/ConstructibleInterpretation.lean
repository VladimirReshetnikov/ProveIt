import ZFCinPA.Translation
import ZFCinPA.ZFDelta1
import ZFCinPA.SetRelativization
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
open SetTheory.BusyBeaver.ZFC.Constructible (InL)

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
      domAt δ n := by
  have h : ((Rew.emb : Rew ℒₛₑₜ ο (n + 1) ξ (n + 1)).comp (Rew.embSubsts ![#0])) =
      Rew.embSubsts ![#0] := by
    ext x
    · rw [Fin.fin_one_eq_zero x]
      simp [Rew.comp_app]
    · exact x.elim
  unfold domAt
  rw [← TransitiveRewriting.comp_app, h]

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
  cases t with
  | bvar x => rfl
  | fvar x => rfl
  | func g v => exact g.elim

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

private theorem env2_eq_aux {W : Type*} (x y : W) (e : ℕ → W) :
    ∀ i : Fin 2, ![x, y] i = _root_.SetTheory.scons x (_root_.SetTheory.scons y e) i.val := fun i =>
  Fin.cases rfl (fun j => Fin.cases rfl (fun j0 => j0.elim0) j) i

private theorem env2_shift_aux {W : Type*} (x y : W) (e : ℕ → W) (j : ℕ) :
    e j = _root_.SetTheory.scons x (_root_.SetTheory.scons y e) (2 + j) := by
  rw [Nat.add_comm]
  rfl

/-- The repository's Replacement clause in a model of `𝗭𝗙` (the proof of
`Translation.repl_clause`, which is stated for `𝗭𝗙𝗖` but uses only
Replacement and Separation). -/
theorem repl_clauseZF (psi : _root_.SetTheory.Form) (e : ℕ → V)
    (hfun : _root_.SetTheory.Functional (_root_.SetTheory.relOf (memRel V) psi e)) (a : V) :
    ∃ r : V, ∀ y, y ∈ r ↔ ∃ x, x ∈ a ∧ _root_.SetTheory.relOf (memRel V) psi e y x := by
  haveI : V↓[ℒₛₑₜ] ⊧* 𝗭 := modelsZ_of_modelsZF (V := V)
  have hTG : ∀ xv yv : V,
      ((toSet 2 (totalGraphF psi)).Eval ![xv, yv] e ↔
        (_root_.SetTheory.relOf (memRel V) psi e yv xv ∨
          ((¬ ∃ z, _root_.SetTheory.relOf (memRel V) psi e z xv) ∧ yv = xv))) := fun xv yv =>
    (eval_toSet (totalGraphF psi) 2 ![xv, yv] e
        (_root_.SetTheory.scons xv (_root_.SetTheory.scons yv e))
        (env2_eq_aux xv yv e) (fun j => env2_shift_aux xv yv e j)).trans
      (sat_totalGraphF psi e xv yv)
  have htot : ∀ x : V, ∃! y, (toSet 2 (totalGraphF psi)).Eval ![x, y] e := by
    intro x
    by_cases hx : ∃ z, _root_.SetTheory.relOf (memRel V) psi e z x
    · obtain ⟨z, hz⟩ := hx
      exact ⟨z, (hTG x z).mpr (Or.inl hz), fun y hy =>
        ((hTG x y).mp hy).elim (fun h => hfun x y z h hz)
          (fun h => absurd ⟨z, hz⟩ h.1)⟩
    · exact ⟨x, (hTG x x).mpr (Or.inr ⟨hx, rfl⟩), fun y hy =>
        ((hTG x y).mp hy).elim (fun h => absurd ⟨y, h⟩ hx) (fun h => h.2)⟩
  have hrepl :
      ∀ f : ℕ → V,
        (∀ x : V, ∃! y : V, (toSet 2 (totalGraphF psi)).Eval ![x, y] f) →
        ∀ X : V, ∃ Y : V, ∀ y : V,
          y ∈ Y ↔ ∃ x ∈ X, (toSet 2 (totalGraphF psi)).Eval ![x, y] f := by
    simpa [models_iff, Axiom.replacementSchema, Matrix.constant_eq_singleton,
      Matrix.comp_vecCons'] using
      models_of_mem (M := V) (T := 𝗭𝗙)
        (ZermeloFraenkel.axiom_of_replacement (toSet 2 (totalGraphF psi)))
  obtain ⟨Y, hY⟩ := hrepl e htot a
  obtain ⟨r, hr⟩ := sep_clause (carveF psi) (_root_.SetTheory.scons a e) Y
  refine ⟨r, fun y => ?_⟩
  rw [hr y, sat_carveF psi e a y]
  constructor
  · rintro ⟨-, hx⟩
    exact hx
  · rintro ⟨x, hxa, hRyx⟩
    exact ⟨(hY y).mpr ⟨x, hxa, (hTG x y).mpr (Or.inl hRyx)⟩, x, hxa, hRyx⟩

/-- **Bundle extraction for `𝗭𝗙`.** -/
theorem zfAxioms_of_modelsZF : _root_.SetTheory.ZFAxioms (memRel V) :=
  haveI : V↓[ℒₛₑₜ] ⊧* 𝗭 := modelsZ_of_modelsZF (V := V)
  { ext := fun _ _ h => mem_ext h
    sep := sep_clause
    pair := pairing_exists
    union := union_clause
    inf := inf_clause
    repl := repl_clauseZF }

theorem power_of_modelsZF :
    ∀ a : V, ∃ p, ∀ x, memRel V x p ↔ _root_.SetTheory.Sub (memRel V) x a :=
  haveI : V↓[ℒₛₑₜ] ⊧* 𝗭 := modelsZ_of_modelsZF (V := V)
  pow_clause

theorem regular_of_modelsZF : SetTheory.BusyBeaver.ZFC.InternalOrd.Regular (memRel V) :=
  haveI : V↓[ℒₛₑₜ] ⊧* 𝗭 := modelsZ_of_modelsZF (V := V)
  reg_clause

end ZFModel

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
  rcases hσ with (hσ | hσ) | hσ
  · exact models_of_mem (T := (𝗘𝗤 ℒₛₑₜ : SetTheory)) hσ
  · simp only [zfFixed, Set.mem_insert_iff, Set.mem_singleton_iff] at hσ
    rcases hσ with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · suffices ∃ x : {x : V // InLV x}, ∀ y, y ∉ x by simpa [models_iff, Axiom.empty]
      obtain ⟨_, ⟨e0, -, he0⟩, -⟩ := HL.inf
      exact ⟨e0, he0⟩
    · suffices ∀ x y : {x : V // InLV x}, x = y ↔ ∀ z, z ∈ x ↔ z ∈ y by
        simpa [models_iff, Axiom.extentionality]
      intro x y
      exact ⟨fun h => h ▸ fun _ => Iff.rfl, HL.ext x y⟩
    · suffices ∀ x y : {x : V // InLV x}, ∃ z, ∀ v, v ∈ z ↔ v = x ∨ v = y by
        simpa [models_iff, Axiom.pairing, -Subtype.exists]
      exact HL.pair
    · suffices ∀ x : {x : V // InLV x}, ∃ y, ∀ z, z ∈ y ↔ ∃ v ∈ x, z ∈ v by
        simpa [models_iff, Axiom.union, -Subtype.exists]
      intro x
      obtain ⟨w, hw⟩ := HL.union x
      refine ⟨w, fun z => (hw z).trans ?_⟩
      constructor <;> rintro ⟨v, h1, h2⟩ <;> exact ⟨v, h2, h1⟩
    · suffices ∀ x : {x : V // InLV x}, ∃ y, ∀ z, z ∈ y ↔ z ⊆ x by
        simpa [models_iff, Axiom.power, -Subtype.exists]
      intro x
      obtain ⟨p, hp⟩ := L_power H hR hP x
      exact ⟨p, fun z => (hp z).trans Iff.rfl⟩
    · suffices ∃ ω : {x : V // InLV x}, (∀ e, LO.FirstOrder.SetTheory.IsEmpty e → e ∈ ω) ∧
          ∀ x ∈ ω, ∀ y, (∀ z, z ∈ y ↔ z = x ∨ z ∈ x) → y ∈ ω by
        simpa [models_iff, Axiom.infinity, val_isSucc_iff]
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
    · suffices ∀ x : {x : V // InLV x}, LO.FirstOrder.SetTheory.IsNonempty x →
          ∃ y ∈ x, ∀ z ∈ x, z ∉ y by
        simpa [models_iff, Axiom.foundation]
      intro x hx
      obtain ⟨m, hm, hmin⟩ := L_regular H hR hP x (isNonempty_def.mp hx)
      exact ⟨m, hm, fun z hz hzm => hmin ⟨z, hzm, hz⟩⟩
  · rcases hσ
    suffices ∀ 𝓧 : {x : V // InLV x},
        (∀ X ∈ 𝓧, LO.FirstOrder.SetTheory.IsNonempty X) →
        (∀ X ∈ 𝓧, ∀ Y ∈ 𝓧, (∃ x ∈ X, x ∈ Y) → X = Y) →
        ∃ C, ∀ X ∈ 𝓧, ∃! x, x ∈ C ∧ x ∈ X by
      simpa [models_iff, Axiom.choice, -Subtype.exists]
    intro 𝓧 hne hdisj
    have hch := SetTheory.BusyBeaver.ZFC.ConstructibleOrder.choice_of_VL HL (L_regular H hR hP)
      (L_power H hR hP) (SetTheory.BusyBeaver.ZFC.ConstructibleAbs.vEqL H hR hP)
    obtain ⟨C, hC⟩ := hch 𝓧 (fun X hX => isNonempty_def.mp (hne X hX))
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

lemma embSubsts_eq_comp {ξ : Type*} {n : ℕ} :
    (Rew.embSubsts ![(#0 : Semiterm ℒₛₑₜ ξ (n + 1))] : Rew ℒₛₑₜ Empty 1 ξ (n + 1)) =
      (Rew.subst ![#0]).comp Rew.emb := by
  ext x
  · rw [Fin.fin_one_eq_zero x]
    simp [Rew.comp_app]
  · exact x.elim

/-- The domain formula has the same code at every binder depth. -/
lemma quote_domAt (n : ℕ) :
    (⌜(domAt domL n : SetTheorySemiproposition (n + 1))⌝ : W) = ⌜domL⌝ := by
  have h : (domAt domL n : SetTheorySemiproposition (n + 1)) =
      (Rewriting.emb domL : SetTheorySemiproposition 1) ⇜ ![#0] := by
    rw [domAt, embSubsts_eq_comp, TransitiveRewriting.comp_app]
  rw [h, LO.FirstOrder.Semiformula.quote_def, LO.FirstOrder.Semiformula.typed_quote_substs,
    Bootstrapping.Semiformula.val_substs, LO.FirstOrder.Sentence.quote_def,
    LO.FirstOrder.Semiformula.quote_def]
  refine subst_eq_self_of_prefix (k := 1) (by simp) (SemitermVec.isSemitermVec _) (by simp) ?_
  intro i hi
  have : i = 0 := by simpa using hi
  subst this
  simp

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

lemma shift_quote_domL : shift ℒₛₑₜ (⌜domL⌝ : W) = ⌜domL⌝ := by
  rw [LO.FirstOrder.Sentence.quote_def, ← LO.FirstOrder.Semiformula.quote_shift]
  congr 1
  rw [Rewriting.shift, ← TransitiveRewriting.comp_app, Rew.shift_comp_emb]

/-- `Prov_ZF(∃x (x ∈ L))`. -/
theorem provable_exists_L : Provable 𝗭𝗙 (^∃ (⌜domL⌝ : W)) := by
  have h := internalize_provability (V := W) zf_proves_exists_L
  simpa [LO.FirstOrder.Sentence.quote_def] using h

/-! ### The internal axiom class of `𝗭𝗙𝗖` -/

lemma mem_class_union {T U : SetTheory} [T.Δ₁] [U.Δ₁] {p : W} :
    p ∈ (T ∪ U).Δ₁Class ↔ p ∈ T.Δ₁Class ∨ p ∈ U.Δ₁Class := by
  change W ⊧/![p] (T.Δ₁ch ⋎ U.Δ₁ch).val ↔ W ⊧/![p] T.Δ₁ch.val ∨ W ⊧/![p] U.Δ₁ch.val
  simp

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
lemma mem_ch_ofList {p : W} : ∀ (l : List SetTheorySentence),
    W ⊧/![p] (Theory.Δ₁.ofList l).ch.val → ∃ σ ∈ l, p = ⌜σ⌝
  | [], h => by
      change W ⊧/![p] (⊥ : 𝚫₁.Semisentence 1).val at h
      simp at h
  | φ :: l, h => by
      change W ⊧/![p] ((Theory.Δ₁.singleton φ).ch ⋎ (Theory.Δ₁.ofList l).ch).val at h
      simp only [HierarchySymbol.Semiformula.val_or, LogicalConnective.HomClass.map_or,
        LogicalConnective.Prop.or_eq] at h
      rcases h with h | h
      · refine ⟨φ, by simp, ?_⟩
        have h' : p = ORingStructure.numeral (Encodable.encode φ) := by simpa using h
        rw [h', numeral_eq_natCast_app, LO.FirstOrder.Sentence.quote_eq_encode]
      · obtain ⟨σ, hσ, rfl⟩ := mem_ch_ofList l h
        exact ⟨σ, by simp [hσ], rfl⟩

lemma mem_ch_ofFinite (T : SetTheory) (hT : Set.Finite T) {p : W}
    (h : W ⊧/![p] (Theory.Δ₁.ofFinite T hT).ch.val) : ∃ σ ∈ T, p = ⌜σ⌝ := by
  obtain ⟨σ, hσ, rfl⟩ := mem_ch_ofList hT.toFinset.toList h
  exact ⟨σ, by simpa using hσ, rfl⟩

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
