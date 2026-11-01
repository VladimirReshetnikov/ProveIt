import DiophantineConsistency.PRAWitnessCalculus
import DiophantineConsistency.PRAISigmaOneOpenComparison
import DiophantineConsistency.PRABoundedWitness
import DiophantineConsistency.PRAModelIOpenPairing
/-! # Transferring witness bounds from `𝗜𝚺₁` to candidate PRA

The genuinely unbounded witnesses of Foundation's definitions (fixpoint stages,
computation histories, syntax-function values) have small replacements in
`𝗜𝚺₁`, where Foundation's semantic API applies. This module moves such a
replacement statement into every candidate-PRA model.

Fix a `Σ₁` formula `ψ` in context `x :> e` and a bound: an `ℒₒᵣ` graph `Tg`
(context `t :> e`) together with a candidate-PRA term `Tt` above every value of
`Tg`. If every `𝗜𝚺₁` model satisfies

  `ψ(x, e) → ∃ t, Tg(t, e) ∧ ∃ x' ≤ t, ψ(x', e)`,

then every candidate-PRA model `M` satisfies

  `bnd ψ(x, e, w) → ∃ x' ≤ Tt(e), ψ(x', e)` (`transfer`).

Phrased with `bnd ψ` the statement is `∀ e x w ∃ z θ` with a bounded matrix,
so `PRAISigmaOneOpenComparison.comparison` (Parsons' theorem in the form
proved there) applies once the matrix is made open by characteristic codes:
`z` packs the replacement `x'` with a bound `w'` for its own witnesses, and
the bounded formula `cdef ψ` unpacks it. In a candidate-PRA model the
hypothesis `bnd ψ(x, e, w)` is supplied by the witness calculus (`WB`), so
`transfer` is exactly the side condition `wb_exs` needs. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAWitnessTransfer
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open StrictSigmaOneInduction

variable {n : ℕ}

/-- `bnd ψ`, reordered to the context `x :> w :> e`. -/
noncomputable def front (ψ : ArithmeticSemisentence (n + 1)) : ArithmeticSemisentence (n + 2) :=
  Rew.subst (Fin.snoc ((#0 : ArithmeticSemiterm Empty (n + 2)) :> fun i : Fin n => #(i.succ.succ)) #1) ▹
    bnd ψ

theorem eval_front {V : Type*} [ORingStructure V] (ψ : ArithmeticSemisentence (n + 1))
    (x w : V) (e : Fin n → V) :
    (front ψ).Eval (x :> w :> e) Empty.elim ↔ (bnd ψ).Eval (Fin.snoc (x :> e) w) Empty.elim := by
  have hf : (Semiterm.val (x :> w :> e) Empty.elim ∘
      ⇑(Rew.subst (Fin.snoc ((#0 : ArithmeticSemiterm Empty (n + 2)) :> fun i : Fin n => #(i.succ.succ)) #1)) ∘
        Semiterm.fvar) = (Empty.elim : Empty → V) := funext fun z => Empty.elim z
  have hv : (Semiterm.val (x :> w :> e) Empty.elim ∘
      ⇑(Rew.subst (Fin.snoc ((#0 : ArithmeticSemiterm Empty (n + 2)) :> fun i : Fin n => #(i.succ.succ)) #1)) ∘
        Semiterm.bvar) = Fin.snoc (x :> e) w := by
    funext i
    refine Fin.lastCases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i <;> simp
  rw [front, Semiformula.eval_rew, hf, hv]

/-- `z` codes `⟪x', w'⟫` with `x' ≤ t` and `bnd ψ(x', e, w')`. Context `z :> t :> e`. -/
noncomputable def cdef (ψ : ArithmeticSemisentence (n + 1)) : ArithmeticSemisentence (n + 2) :=
  “z t. ∃ x' <⁺ z, ∃ w' <⁺ z, !pairDef z x' w' ∧ x' ≤ t ∧ !(front ψ) x' w' ⋯”

theorem cdef_bounded (ψ : ArithmeticSemisentence (n + 1)) (hψ : Hierarchy 𝚺 1 ψ) :
    Hierarchy 𝚺 0 (cdef ψ) := by
  have h := hierarchy_bnd hψ le_rfl (fun _ => rfl)
  simp [cdef, front, Semiformula.bexsLTSucc, Semiformula.bexsLT, h, pairDef.sigma_prop]

/-- The `𝗜𝚺₁` statement: bounded instances have replacements below `Tg`. Context `x :> w :> e`. -/
noncomputable def sigmaBody (ψ φ : ArithmeticSemisentence (n + 1)) (Tg : ArithmeticSemisentence (n + 1)) :
    ArithmeticSemisentence (n + 2) :=
  “x w. !(front ψ) x w ⋯ → ∃ t, !Tg t ⋯ ∧ ∃ z, !(cdef φ) z t ⋯”

/-! ## The `𝗜𝚺₁` side -/

theorem strictSigma_sigma1 {φ : ArithmeticSemiformula ℕ 1} (h : StrictSigma φ) : Hierarchy 𝚺 1 φ := by
  obtain ⟨k, D, hD, rfl⟩ := h
  simpa using hD.mono (show 0 ≤ 1 by decide)

/-- `𝗜𝚺₁` models satisfy strict-`Σ₁` induction. -/
theorem models_prefix {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :
    V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ ∪ InductionScheme ℒₒᵣ StrictSigma := by
  have h : (𝗣𝗔⁻ ∪ InductionScheme ℒₒᵣ StrictSigma) ⊆ 𝗜𝚺₁ := by
    rintro σ (hσ | ⟨φ, hφ, rfl⟩)
    · exact Or.inl hσ
    · exact Or.inr ⟨φ, strictSigma_sigma1 hφ, rfl⟩
  exact Semantics.ModelsSet.of_subset inferInstance h

theorem eval_cdef {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] (ψ : ArithmeticSemisentence (n + 1))
    (z t : V) (e : Fin n → V) :
    (cdef ψ).Eval (z :> t :> e) Empty.elim ↔ ∃ x' ≤ z, ∃ w' ≤ z, z = ⟪x', w'⟫ ∧ x' ≤ t ∧
      (bnd ψ).Eval (Fin.snoc (x' :> e) w') Empty.elim := by
  simp [cdef, Semiformula.bexsLTSucc, Semiformula.bexsLT, FirstOrder.bexs, Semiformula.Operator.val,
    Semiformula.Operator.LT.sentence_eq, Semiformula.Operator.LE.sentence_eq,
    Semiformula.Operator.Eq.sentence_eq, lt_succ_iff_le]
  have hv (a b : V) : (Semiterm.val (b :> a :> z :> t :> e) Empty.elim ∘
      ((#1 :> #0 :> fun x => #x.succ.succ.succ.succ) : Fin (n + 2) → ArithmeticSemiterm Empty (n + 4))) =
      (a :> b :> e) := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i <;> simp
  simp only [hv, eval_front]
  simp [le_iff_eq_or_lt]

theorem eval_sigmaBody {V : Type*} [ORingStructure V] (ψ φ Tg : ArithmeticSemisentence (n + 1))
    (x w : V) (e : Fin n → V) :
    (sigmaBody ψ φ Tg).Eval (x :> w :> e) Empty.elim ↔
      ((front ψ).Eval (x :> w :> e) Empty.elim →
        ∃ t, Tg.Eval (t :> e) Empty.elim ∧ ∃ z, (cdef φ).Eval (z :> t :> e) Empty.elim) := by
  have h1 : (Semiterm.val (x :> w :> e) Empty.elim ∘
      ((#0 :> #1 :> fun x => #x.succ.succ) : Fin (n + 2) → ArithmeticSemiterm Empty (n + 2))) =
      x :> w :> e := by
    funext i; refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i <;> simp
  have h2 (t : V) : (Semiterm.val (t :> x :> w :> e) Empty.elim ∘
      ((#0 :> fun x => #x.succ.succ.succ) : Fin (n + 1) → ArithmeticSemiterm Empty (n + 3))) =
      t :> e := by
    funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
  have h3 (z t : V) : (Semiterm.val (z :> t :> x :> w :> e) Empty.elim ∘
      ((#0 :> #1 :> fun x => #x.succ.succ.succ.succ) : Fin (n + 2) → ArithmeticSemiterm Empty (n + 4))) =
      z :> t :> e := by
    funext i; refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i <;> simp
  simp [sigmaBody]
  simp only [h1, h2, h3]

theorem cons_cons_tail {V : Type*} (v : Fin (n + 2) → V) :
    v = v 0 :> v 1 :> fun i : Fin n => v i.succ.succ := by
  funext i; refine Fin.cases rfl (fun j => Fin.cases rfl (fun k => rfl) j) i

/-- **The `𝗜𝚺₁` statement** follows from its semantic content in `𝗜𝚺₁` models. -/
theorem isigma1_sigma (ψ φ Tg : ArithmeticSemisentence (n + 1)) (hφ : Hierarchy 𝚺 1 φ)
    (hI : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (e : Fin n → V) (x : V),
      ψ.Eval (x :> e) Empty.elim →
        ∃ t, Tg.Eval (t :> e) Empty.elim ∧ ∃ x' ≤ t, φ.Eval (x' :> e) Empty.elim) :
    𝗜𝚺₁ ⊢ ∀⁰* sigmaBody ψ φ Tg := by
  refine complete.{0} _ _ fun V _ hV => ?_
  haveI : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ ∪ InductionScheme ℒₒᵣ StrictSigma := models_prefix
  letI : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₁) inferInstance
  letI : V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (U := 𝗜𝚺₁) inferInstance
  simp only [models_iff, Semiformula.eval_allClosure]
  intro v
  rw [cons_cons_tail v, eval_sigmaBody]
  intro hf
  have hψx : ψ.Eval (v 0 :> fun i : Fin n => v i.succ.succ) Empty.elim :=
    eval_bnd_imp ψ _ _ Empty.elim ((eval_front ψ _ _ _).mp hf)
  obtain ⟨t, ht, x', hx't, hψ'⟩ := hI V _ _ hψx
  obtain ⟨w', hw'⟩ := eval_bnd_of hφ le_rfl (fun _ => rfl) (x' :> fun i : Fin n => v i.succ.succ)
    Empty.elim hψ'
  exact ⟨t, ht, ⟪x', w'⟫, (eval_cdef φ _ t _).mpr
    ⟨x', le_pair_left x' w', w', le_pair_right x' w', rfl, hx't, hw'⟩⟩

/-! ## The candidate-PRA side -/

open PRALanguage PRATheory PRAFiniteFunctionCodes PRABoundedCharacteristic PRABoundedFormula
  PRABoundedWitness

theorem front_bounded (ψ : ArithmeticSemisentence (n + 1)) (hψ : Hierarchy 𝚺 1 ψ) :
    Hierarchy 𝚺 0 (front ψ) :=
  Hierarchy.rew _ (hierarchy_bnd hψ le_rfl (fun _ => rfl))

/-- The bound term dominates its graph: `Tg(t, e) → t ≤ Tt(e)`. -/
noncomputable def dominates (Tg : ArithmeticSemisentence (n + 1)) (Tt : TermN n) : Sentence language :=
  ∀⁰* (Semiformula.lMap embedding Tg 🡒
    (Rew.subst ![#0, Rew.bShift Tt] ▹
      Semiformula.lMap embedding (“x y. x ≤ y” : ArithmeticSemisentence 2)))

/-- Reduce a domination sentence to its value in a candidate-PRA model. -/
theorem dominates_of_val (Tg : ArithmeticSemisentence (n + 1)) (Tt : TermN n)
    (h : ∀ (M : Type) [Nonempty M] [Structure language M] [Structure.Eq language M]
      [M↓[language] ⊧* PRA] (t : M) (e : Fin n → M),
      (Semiformula.lMap embedding Tg).Eval (t :> e) Empty.elim →
        (Semiformula.lMap embedding (“x y. x ≤ y” : ArithmeticSemisentence 2)).Eval
          ![t, Tt.val e Empty.elim] Empty.elim) :
    PRA ⊢ dominates Tg Tt := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ hM
  letI : M↓[language] ⊧* PRA := hM
  simp only [models_iff, dominates, Semiformula.eval_allClosure, LogicalConnective.HomClass.map_imply]
  intro v hv
  rw [Semiformula.eval_rew]
  have hvec : (Semiterm.val v Empty.elim ∘
      ⇑(Rew.subst ![(#0 : Semiterm language Empty (n + 1)), Rew.bShift Tt]) ∘ Semiterm.bvar) =
      ![v 0, Tt.val (fun i => v i.succ) Empty.elim] := by
    funext i; refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.elim0 k) j) i <;>
      simp [Semiterm.val_bShift']
  have hf : (Semiterm.val v Empty.elim ∘
      ⇑(Rew.subst ![(#0 : Semiterm language Empty (n + 1)), Rew.bShift Tt]) ∘
        Semiterm.fvar) = (Empty.elim : Empty → M) := Subsingleton.elim _ _
  rw [hvec, hf]
  have hv' : v = v 0 :> fun i => v i.succ := (Fin.cons_self_tail v).symm
  rw [hv'] at hv
  exact h M (v 0) (fun i => v i.succ) hv


/-- The open matrix: free variables `x = &0`, `w = &1`, `e = &2, …`; bound `z`. -/
noncomputable def theta (cA cC : Code (n + 2)) (Tt : TermN n) : Semiproposition language 1 :=
  ∼(Rew.embSubsts (fun i : Fin (n + 2) => (&(i : ℕ) : Semiterm language ℕ 1)) ▹ characteristicMatrix cA) ⋎
    (Rew.embSubsts ((#0 : Semiterm language ℕ 1) :>
      (Rew.embSubsts (fun i : Fin n => (&((i : ℕ) + 2) : Semiterm language ℕ 1)) Tt) :>
      fun i : Fin n => &((i : ℕ) + 2)) ▹ characteristicMatrix cC)

theorem theta_open (cA cC : Code (n + 2)) (Tt : TermN n) : (theta cA cC Tt).Open := by
  simp [theta, characteristicMatrix]

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

omit [M↓[language] ⊧* PRA] in
theorem eval_lMap_std {k : ℕ} (φ : ArithmeticSemisentence k) (v : Fin k → M) :
    (Semiformula.lMap embedding φ).Eval v Empty.elim ↔ φ.Eval v Empty.elim := by
  rw [Semiformula.eval_lMap, PRAModelIOpenPairing.reduct_eq_standard]

omit [M↓[language] ⊧* PRA] in
/-- What the open matrix says. -/
theorem eval_theta (ψ φ : ArithmeticSemisentence (n + 1)) (cA cC : Code (n + 2)) (Tt : TermN n)
    (hA : M↓[language] ⊧ oneCorrectSentence cA (Semiformula.lMap embedding (front ψ)))
    (hC : M↓[language] ⊧ oneCorrectSentence cC (Semiformula.lMap embedding (cdef φ)))
    (z : M) (f : ℕ → M) :
    (theta cA cC Tt).Eval ![z] f ↔
      ¬(front ψ).Eval (f 0 :> f 1 :> fun i : Fin n => f ((i : ℕ) + 2)) Empty.elim ∨
        (cdef φ).Eval (z :> Tt.val (fun i : Fin n => f ((i : ℕ) + 2)) Empty.elim :>
          fun i : Fin n => f ((i : ℕ) + 2)) Empty.elim := by
  have hA' := modelCharacteristicMatrix cA _ hA
  have hC' := modelCharacteristicMatrix cC _ hC
  simp only [theta, LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
    Semiformula.eval_rew]
  have v1 : (Semiterm.val ![z] f ∘
      ⇑(Rew.embSubsts fun i : Fin (n + 2) => (&(i : ℕ) : Semiterm language ℕ 1)) ∘ Semiterm.bvar) =
      (f 0 :> f 1 :> fun i : Fin n => f ((i : ℕ) + 2)) := by
    funext i; refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i <;> simp
  have ht : ((Rew.embSubsts (fun i : Fin n => (&((i : ℕ) + 2) : Semiterm language ℕ 1))) Tt).val ![z] f =
      Tt.val (fun i : Fin n => f ((i : ℕ) + 2)) Empty.elim := by
    rw [Semiterm.val_rew]
    congr 1
    funext x
    exact x.elim
  have v2 : (Semiterm.val ![z] f ∘
      ⇑(Rew.embSubsts ((#0 : Semiterm language ℕ 1) :>
        (Rew.embSubsts (fun i : Fin n => (&((i : ℕ) + 2) : Semiterm language ℕ 1)) Tt) :>
          fun i : Fin n => &((i : ℕ) + 2))) ∘ Semiterm.bvar) =
      (z :> Tt.val (fun i : Fin n => f ((i : ℕ) + 2)) Empty.elim :>
        fun i : Fin n => f ((i : ℕ) + 2)) := by
    funext i; refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i <;>
      simp [Function.comp_def, ht]
  have f1 : (Semiterm.val ![z] f ∘
      ⇑(Rew.embSubsts fun i : Fin (n + 2) => (&(i : ℕ) : Semiterm language ℕ 1)) ∘ Semiterm.fvar) =
      (Empty.elim : Empty → M) := Subsingleton.elim _ _
  have f2 : (Semiterm.val ![z] f ∘
      ⇑(Rew.embSubsts ((#0 : Semiterm language ℕ 1) :>
        (Rew.embSubsts (fun i : Fin n => (&((i : ℕ) + 2) : Semiterm language ℕ 1)) Tt) :>
          fun i : Fin n => &((i : ℕ) + 2))) ∘ Semiterm.fvar) = (Empty.elim : Empty → M) :=
    Subsingleton.elim _ _
  rw [v1, v2, f1, f2, hA', hC', eval_lMap_std, eval_lMap_std]
  exact Iff.rfl

theorem eval_dominates (Tg : ArithmeticSemisentence (n + 1)) (Tt : TermN n)
    (h : M↓[language] ⊧ dominates Tg Tt) (t : M) (e : Fin n → M) :
    letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen
    Tg.Eval (t :> e) Empty.elim → t ≤ Tt.val e Empty.elim := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen
  simp only [models_iff, dominates, Semiformula.eval_allClosure] at h
  intro ht
  have h' := h (t :> e)
  simp only [LogicalConnective.HomClass.map_imply, Semiformula.eval_rew, eval_lMap_std] at h'
  have hv : (Semiterm.val (t :> e) Empty.elim ∘
      ⇑(Rew.subst ![(#0 : Semiterm language Empty (n + 1)), Rew.bShift Tt]) ∘
        Semiterm.bvar) = ![t, Tt.val e Empty.elim] := by
    funext i; refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.elim0 k) j) i <;>
      simp [Function.comp_def]
  have hf : (Semiterm.val (t :> e) Empty.elim ∘
      ⇑(Rew.subst ![(#0 : Semiterm language Empty (n + 1)), Rew.bShift Tt]) ∘
        Semiterm.fvar) = (Empty.elim : Empty → M) := Subsingleton.elim _ _
  rw [hv, hf, eval_lMap_std] at h'
  have hd : t = Tt.val e Empty.elim ∨ t < Tt.val e Empty.elim := by
    simpa [Semiformula.Operator.val, Semiformula.Operator.LE.sentence_eq,
      Semiformula.Operator.Eq.sentence_eq, Semiformula.Operator.LT.sentence_eq] using h' ht
  exact le_iff_eq_or_lt.mpr hd

end models

theorem PRA_goal (ψ φ Tg : ArithmeticSemisentence (n + 1)) (Tt : TermN n)
    (hdom : PRA ⊢ dominates Tg Tt) (cA cC : Code (n + 2))
    (hA : PRA ⊢ oneCorrectSentence cA (Semiformula.lMap embedding (front ψ)))
    (hC : PRA ⊢ oneCorrectSentence cC (Semiformula.lMap embedding (cdef φ))) :
    PRA ⊢ (Semiformula.lMap embedding (∀⁰* sigmaBody ψ φ Tg) 🡒 (∃⁰ theta cA cC Tt).univCl) := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ hM
  letI : M↓[language] ⊧* PRA := hM
  letI : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
  letI : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
  letI : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
  letI : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
  letI : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen
  have hAm := models_of_provable hM hA
  have hCm := models_of_provable hM hC
  have hdm := models_of_provable hM hdom
  simp only [Semantics.Imp.models_imply]
  intro hσ
  have hσ' : ∀ v : Fin (n + 2) → M, (sigmaBody ψ φ Tg).Eval v Empty.elim := by
    intro v
    have h := models_iff.mp hσ
    rw [Semiformula.eval_lMap, PRAModelIOpenPairing.reduct_eq_standard] at h
    exact (Semiformula.eval_allClosure.mp h) v
  simp only [models_iff, Semiformula.eval_univCl, Semiformula.eval_ex]
  intro f
  let e : Fin n → M := fun i => f ((i : ℕ) + 2)
  by_cases hf : (front ψ).Eval (f 0 :> f 1 :> e) Empty.elim
  · obtain ⟨t, ht, z, hz⟩ := (eval_sigmaBody ψ φ Tg (f 0) (f 1) e).mp (hσ' _) hf
    have hte := eval_dominates Tg Tt hdm t e ht
    obtain ⟨x', hx', w', hw', rfl, hxt, hb⟩ := (eval_cdef φ z t e).mp hz
    refine ⟨⟪x', w'⟫, (eval_theta ψ φ cA cC Tt hAm hCm _ f).mpr (Or.inr ?_)⟩
    exact (eval_cdef φ _ _ e).mpr ⟨x', hx', w', hw', rfl, le_trans hxt hte, hb⟩
  · exact ⟨0, (eval_theta ψ φ cA cC Tt hAm hCm 0 f).mpr (Or.inl hf)⟩

section transfer
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

/-- **Witness-replacement transfer.** A replacement bound valid in every `𝗜𝚺₁`
model, dominated by a candidate-PRA code, holds in every candidate-PRA model for
every instance whose own witnesses are bounded. -/
theorem transfer (ψ φ Tg : ArithmeticSemisentence (n + 1)) (Tt : TermN n) (hψ : Hierarchy 𝚺 1 ψ)
    (hφ : Hierarchy 𝚺 1 φ)
    (hI : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (e : Fin n → V) (x : V),
      ψ.Eval (x :> e) Empty.elim →
        ∃ t, Tg.Eval (t :> e) Empty.elim ∧ ∃ x' ≤ t, φ.Eval (x' :> e) Empty.elim)
    (hdom : PRA ⊢ dominates Tg Tt) (e : Fin n → M) (x w : M)
    (hb : (bnd ψ).Eval (Fin.snoc (x :> e) w) Empty.elim) :
    ∃ x' ≤ Tt.val e Empty.elim, φ.Eval (x' :> e) Empty.elim := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen
  obtain ⟨cA, -, -, hA⟩ := PRA_proves_boundedBooleanCharacteristic
    (Semiformula.lMap embedding (front ψ)) (ParsonsHierarchyMap.hierarchy (front_bounded ψ hψ))
  obtain ⟨cC, -, -, hC⟩ := PRA_proves_boundedBooleanCharacteristic
    (Semiformula.lMap embedding (cdef φ)) (ParsonsHierarchyMap.hierarchy (cdef_bounded φ hφ))
  have hG := PRAISigmaOneOpenComparison.comparison (∀⁰* sigmaBody ψ φ Tg) (isigma1_sigma ψ φ Tg hφ hI)
    (theta cA cC Tt) (theta_open cA cC Tt) (PRA_goal ψ φ Tg Tt hdom cA cC hA hC)
  have hGm := models_of_provable (inferInstance : M↓[language] ⊧* PRA) hG
  have hAm := models_of_provable (inferInstance : M↓[language] ⊧* PRA) hA
  have hCm := models_of_provable (inferInstance : M↓[language] ⊧* PRA) hC
  simp only [models_iff, Semiformula.eval_univCl, Semiformula.eval_ex] at hGm
  let f : ℕ → M := fun k => match k with
    | 0 => x
    | 1 => w
    | k + 2 => if h : k < n then e ⟨k, h⟩ else x
  have hfe : (fun i : Fin n => f ((i : ℕ) + 2)) = e := by funext i; simp [f, i.isLt]
  obtain ⟨z, hz⟩ := hGm f
  rw [eval_theta ψ φ cA cC Tt hAm hCm z f, hfe] at hz
  have hfr : (front ψ).Eval (f 0 :> f 1 :> e) Empty.elim := (eval_front ψ x w e).mpr hb
  obtain ⟨x', -, w', -, -, hxT, hb'⟩ := (eval_cdef φ z _ e).mp (hz.resolve_left (not_not_intro hfr))
  exact ⟨x', hxT, eval_bnd_imp φ (x' :> e) w' Empty.elim hb'⟩

/-! ## Polynomial bounds -/

/-- The graph `t = P(e)` of an `ℒₒᵣ` term. -/
noncomputable def polyGraph (P : ArithmeticSemiterm Empty n) : ArithmeticSemisentence (n + 1) :=
  Semiformula.Operator.Eq.eq.operator ![#0, Rew.bShift P]

omit [Nonempty M] [M↓[language] ⊧* PRA] in
theorem val_lMap_std (P : ArithmeticSemiterm Empty n) (e : Fin n → M) :
    (Semiterm.lMap embedding P).val e Empty.elim = P.val e Empty.elim := by
  rw [Semiterm.val_lMap, PRAModelIOpenPairing.reduct_eq_standard]

theorem dominates_poly (P : ArithmeticSemiterm Empty n) :
    PRA ⊢ dominates (polyGraph P) (Semiterm.lMap embedding P) := by
  refine dominates_of_val _ _ fun M _ _ _ hM x e hx => ?_
  letI : M↓[language] ⊧* PRA := hM
  letI : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
  letI : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
  letI : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
  letI : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
  letI : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
  rw [eval_lMap_std] at hx ⊢
  have hx0 : x = P.val e Empty.elim := by
    simpa [polyGraph, Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq,
      Semiterm.val_bShift'] using hx
  rw [val_lMap_std, hx0]
  simp [Semiformula.Operator.val, Semiformula.Operator.LE.sentence_eq,
    Semiformula.Operator.Eq.sentence_eq, Semiformula.Operator.LT.sentence_eq]

end transfer

section poly
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
open PRAWitnessCalculus

/-- **An existential whose `𝗜𝚺₁` replacement lies below an `ℒₒᵣ` polynomial has
bounded witnesses in every candidate-PRA model.** -/
theorem wb_exs_poly (ψ : ArithmeticSemisentence (n + 1)) (hψ : Hierarchy 𝚺 1 ψ)
    (P : ArithmeticSemiterm Empty n)
    (hI : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (e : Fin n → V) (x : V),
      ψ.Eval (x :> e) Empty.elim → ∃ x' ≤ P.val e Empty.elim, ψ.Eval (x' :> e) Empty.elim)
    (hWB : WB M ψ) : WB M (∃⁰ ψ) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  obtain ⟨B, hB, hb⟩ := hWB
  refine wb_exs (fun e => P.val e Empty.elim) (term_mono P) (fun e ⟨x, hx⟩ => ?_) ⟨B, hB, hb⟩
  have hI' : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (e : Fin n → V) (x : V),
      ψ.Eval (x :> e) Empty.elim → ∃ t, (polyGraph P).Eval (t :> e) Empty.elim ∧
        ∃ x' ≤ t, ψ.Eval (x' :> e) Empty.elim := by
    intro V _ _ e x h
    obtain ⟨x', hx', h'⟩ := hI V e x h
    exact ⟨P.val e Empty.elim, by simp [polyGraph, Semiformula.Operator.val,
      Semiformula.Operator.Eq.sentence_eq], x', hx', h'⟩
  obtain ⟨x', hx', h'⟩ := transfer ψ ψ (polyGraph P) (Semiterm.lMap embedding P) hψ hψ hI'
    (dominates_poly P) e x (B (x :> e)) (hb _ hx)
  exact ⟨x', by rwa [val_lMap_std] at hx', h'⟩

/-- **An existential whose `𝗜𝚺₁` replacement lies below the graph of a
candidate-PRA term**, monotone in candidate PRA. -/
theorem wb_exs_bound (ψ : ArithmeticSemisentence (n + 1)) (hψ : Hierarchy 𝚺 1 ψ)
    (Tg : ArithmeticSemisentence (n + 1)) (Tt : TermN n) (hdom : PRA ⊢ dominates Tg Tt)
    (hmono : Mono M (fun e => Tt.val e Empty.elim))
    (hI : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (e : Fin n → V) (x : V),
      ψ.Eval (x :> e) Empty.elim →
        ∃ t, Tg.Eval (t :> e) Empty.elim ∧ ∃ x' ≤ t, ψ.Eval (x' :> e) Empty.elim)
    (hWB : WB M ψ) : WB M (∃⁰ ψ) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  obtain ⟨B, hB, hb⟩ := hWB
  refine wb_exs (fun e => Tt.val e Empty.elim) hmono (fun e ⟨x, hx⟩ => ?_) ⟨B, hB, hb⟩
  exact transfer ψ ψ Tg Tt hψ hψ hI hdom e x (B (x :> e)) (hb _ hx)

end poly


end DiophantineConsistency.PRAWitnessTransfer
