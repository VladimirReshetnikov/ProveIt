import DiophantineConsistency.PRAWitnessTransfer
import DiophantineConsistency.PRAHistoryTruncation
/-! # Exponential witness bounds

Some witnesses are only exponentially bounded: computation histories of
primitive recursions, and values such as `repeatVec x k` (iterated pairing).
`PRAWitnessTransfer.wb_exs_bound` accepts any candidate-PRA term as a bound,
given its `ℒₒᵣ` graph, the domination sentence and monotonicity. This module
supplies the two shapes needed:

* `expBound P`, the term `2^P` for an `ℒₒᵣ` polynomial `P`, with graph
  `Exponential (P e) t`;
* `expBound2 P Q`, the term `2^(P · 2^Q)`, with graph
  `∃ a, Exponential (Q e) a ∧ Exponential (P e · a) t`.

Both are dominated in candidate PRA by `PRAHistoryExpCode.graph_iff` and the
uniqueness of `Exponential`, and monotone by `PRAHistoryTruncation.expF_mono`. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAWitnessExpBounds
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAWitnessCalculus PRAWitnessTransfer

variable {n : ℕ}

/-- `2^P`. -/
noncomputable def expBound (P : ArithmeticSemiterm Empty n) : TermN n :=
  .func PRAHistoryExpCode.expCode ![Semiterm.lMap embedding P]

/-- The graph `Exponential (P e) t`, context `t :> e`. -/
noncomputable def expGraph (P : ArithmeticSemiterm Empty n) : ArithmeticSemisentence (n + 1) :=
  Rewriting.subst exponentialDef.val ![Rew.bShift P, #0]

/-- `2^(P · 2^Q)`. -/
noncomputable def expBound2 (P Q : ArithmeticSemiterm Empty n) : TermN n :=
  .func PRAHistoryExpCode.expCode
    ![.func mulCode ![Semiterm.lMap embedding P, .func PRAHistoryExpCode.expCode ![Semiterm.lMap embedding Q]]]

/-- The graph `∃ a, Exponential (Q e) a ∧ Exponential (P e · a) t`, context `t :> e`. -/
noncomputable def expGraph2 (P Q : ArithmeticSemiterm Empty n) : ArithmeticSemisentence (n + 1) :=
  ∃⁰ (Rewriting.subst exponentialDef.val ![Rew.bShift (Rew.bShift Q), #0] ⋏
    Rewriting.subst exponentialDef.val
      ![Semiterm.func Language.ORing.Func.mul ![Rew.bShift (Rew.bShift P), #0], #1])

theorem eval_expGraph {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀]
    (P : ArithmeticSemiterm Empty n) (t : V) (e : Fin n → V) :
    (expGraph P).Eval (t :> e) Empty.elim ↔ Exponential (P.val e Empty.elim) t := by
  simp [expGraph, Semiterm.val_bShift', Function.comp_def]

theorem eval_expGraph2 {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀]
    (P Q : ArithmeticSemiterm Empty n) (t : V) (e : Fin n → V) :
    (expGraph2 P Q).Eval (t :> e) Empty.elim ↔
      ∃ a, Exponential (Q.val e Empty.elim) a ∧ Exponential (P.val e Empty.elim * a) t := by
  have key : ∀ x : V, (Structure.func (L := ℒₒᵣ) Language.ORing.Func.mul fun i =>
      Semiterm.val (x :> t :> e) Empty.elim (![Rew.bShift (Rew.bShift P), #0] i)) =
        P.val e Empty.elim * x := by
    intro x
    have hv : (fun i => Semiterm.val (x :> t :> e) Empty.elim (![Rew.bShift (Rew.bShift P), #0] i)) =
        ![P.val e Empty.elim, x] := by
      funext i
      refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.elim0 k) j) i <;>
        simp [Semiterm.val_bShift']
    rw [hv]
    rfl
  simp [expGraph2, Semiterm.val_bShift', Function.comp_def, Semiterm.val_func, key]

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

omit [Nonempty M] [Structure.Eq language M] [M↓[language] ⊧* PRA] in
theorem expF_eq (x : M) :
    Structure.func (L := language) PRAHistoryExpCode.expCode ![x] = PRAHistoryTruncation.expF x := by
  unfold PRAHistoryTruncation.expF
  congr 1
  funext i
  exact Fin.cases rfl (fun j => Fin.elim0 j) i

omit [Nonempty M] [M↓[language] ⊧* PRA] in
theorem val_expBound (P : ArithmeticSemiterm Empty n) (e : Fin n → M) :
    (expBound P).val e Empty.elim = PRAHistoryTruncation.expF (P.val e Empty.elim) := by
  simp [expBound, Semiterm.val_func, val_lMap_std, expF_eq]

omit [Nonempty M] [M↓[language] ⊧* PRA] in
theorem val_expBound2 (P Q : ArithmeticSemiterm Empty n) (e : Fin n → M) :
    (expBound2 P Q).val e Empty.elim =
      PRAHistoryTruncation.expF (P.val e Empty.elim * PRAHistoryTruncation.expF (Q.val e Empty.elim)) := by
  simp [expBound2, Semiterm.val_func, val_lMap_std, expF_eq]
  rfl

theorem mono_expBound (P : ArithmeticSemiterm Empty n) :
    Mono M (fun e => (expBound P).val e Empty.elim) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  intro e e' h
  simp only [val_expBound]
  exact PRAHistoryTruncation.expF_mono (term_mono P e e' h)

theorem mono_expBound2 (P Q : ArithmeticSemiterm Empty n) :
    Mono M (fun e => (expBound2 P Q).val e Empty.elim) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  intro e e' h
  simp only [val_expBound2]
  exact PRAHistoryTruncation.expF_mono
    (mul_le_mul' (term_mono P e e' h) (PRAHistoryTruncation.expF_mono (term_mono Q e e' h)))

end models

/-- Reduce a domination sentence to its value in a candidate-PRA model. -/
theorem dominates_of_val (Tg : ArithmeticSemisentence (n + 1)) (Tt : TermN n)
    (h : ∀ (M : Type) [Nonempty M] [Structure language M] [Structure.Eq language M]
      [M↓[language] ⊧* PRA] (t : M) (e : Fin n → M),
      (Semiformula.lMap embedding Tg).Eval (t :> e) Empty.elim →
        (Semiformula.lMap embedding (“x y. x ≤ y” : ArithmeticSemisentence 2)).Eval
          ![t, Tt.val e Empty.elim] Empty.elim) :
    PRA ⊢ dominates Tg Tt :=
  PRAWitnessTransfer.dominates_of_val Tg Tt h

section dom
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

omit [M↓[language] ⊧* PRA] in
theorem eval_le_lMap [M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] (a b : M) :
    (Semiformula.lMap embedding (“x y. x ≤ y” : ArithmeticSemisentence 2)).Eval ![a, b] Empty.elim ↔
      a ≤ b := by
  rw [eval_lMap_std]
  simp [Semiformula.Operator.val, Semiformula.Operator.LE.sentence_eq,
    Semiformula.Operator.Eq.sentence_eq, Semiformula.Operator.LT.sentence_eq, le_iff_eq_or_lt]

end dom

theorem dominates_expBound (P : ArithmeticSemiterm Empty n) :
    PRA ⊢ dominates (expGraph P) (expBound P) := by
  refine dominates_of_val _ _ fun M _ _ _ hM t e ht => ?_
  letI : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
  letI : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
  letI : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
  letI : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
  letI : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  rw [eval_lMap_std, eval_expGraph] at ht
  rw [eval_le_lMap, val_expBound, ht.uniq (PRAHistoryTruncation.exponential_expF _)]

theorem dominates_expBound2 (P Q : ArithmeticSemiterm Empty n) :
    PRA ⊢ dominates (expGraph2 P Q) (expBound2 P Q) := by
  refine dominates_of_val _ _ fun M _ _ _ hM t e ht => ?_
  letI : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
  letI : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
  letI : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
  letI : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
  letI : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  rw [eval_lMap_std, eval_expGraph2] at ht
  obtain ⟨a, ha, hta⟩ := ht
  rw [eval_le_lMap, val_expBound2, ← ha.uniq (PRAHistoryTruncation.exponential_expF _),
    hta.uniq (PRAHistoryTruncation.exponential_expF _)]

end DiophantineConsistency.PRAWitnessExpBounds
