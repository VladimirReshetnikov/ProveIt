module
public import PATheory
public import ProofBridge
public import Foundation.FirstOrder.Arithmetic.Schemata
@[expose] public section
namespace PalomarPA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

def BaseAxiom.foundation : BaseAxiom → ArithmeticSentence
  | .eqRefl => Theory.Eq.refl ℒₒᵣ
  | .eqSymm => Theory.Eq.symm ℒₒᵣ
  | .eqTrans => Theory.Eq.trans ℒₒᵣ
  | .zeroExt => Theory.Eq.funcExt .zero
  | .oneExt => Theory.Eq.funcExt .one
  | .addExt => Theory.Eq.funcExt .add
  | .mulExt => Theory.Eq.funcExt .mul
  | .eqExt => Theory.Eq.relExt .eq
  | .ltExt => Theory.Eq.relExt .lt
  | .addZero => PeanoMinus.Axiom.addZero
  | .addAssoc => PeanoMinus.Axiom.addAssoc
  | .addComm => PeanoMinus.Axiom.addComm
  | .addEqOfLt => PeanoMinus.Axiom.addEqOfLt
  | .zeroLe => PeanoMinus.Axiom.zeroLe
  | .zeroLtOne => PeanoMinus.Axiom.zeroLtOne
  | .oneLeOfZeroLt => PeanoMinus.Axiom.oneLeOfZeroLt
  | .addLtAdd => PeanoMinus.Axiom.addLtAdd
  | .mulZero => PeanoMinus.Axiom.mulZero
  | .mulOne => PeanoMinus.Axiom.mulOne
  | .mulAssoc => PeanoMinus.Axiom.mulAssoc
  | .mulComm => PeanoMinus.Axiom.mulComm
  | .mulLtMul => PeanoMinus.Axiom.mulLtMul
  | .distr => PeanoMinus.Axiom.distr
  | .ltIrrefl => PeanoMinus.Axiom.ltIrrefl
  | .ltTrans => PeanoMinus.Axiom.ltTrans
  | .ltTri => PeanoMinus.Axiom.ltTri

@[simp] theorem BaseAxiom.to_formula (a : BaseAxiom) :
    a.formula.toFoundation = a.foundation := by
  rw [← Formula.to_from a.foundation]
  congr 1
  cases a <;> rfl

theorem BaseAxiom.mem_peanoMinus (a : BaseAxiom) : a.formula.toFoundation ∈ PeanoMinus := by
  rw [to_formula]
  cases a
  all_goals first
    | exact PeanoMinus.equal _ (Theory.eqAxiom.refl)
    | exact PeanoMinus.equal _ (Theory.eqAxiom.symm)
    | exact PeanoMinus.equal _ (Theory.eqAxiom.trans)
    | exact PeanoMinus.equal _ (Theory.eqAxiom.funcExt _)
    | exact PeanoMinus.equal _ (Theory.eqAxiom.relExt _)
    | exact PeanoMinus.addZero
    | exact PeanoMinus.addAssoc
    | exact PeanoMinus.addComm
    | exact PeanoMinus.addEqOfLt
    | exact PeanoMinus.zeroLe
    | exact PeanoMinus.zeroLtOne
    | exact PeanoMinus.oneLeOfZeroLt
    | exact PeanoMinus.addLtAdd
    | exact PeanoMinus.mulZero
    | exact PeanoMinus.mulOne
    | exact PeanoMinus.mulAssoc
    | exact PeanoMinus.mulComm
    | exact PeanoMinus.mulLtMul
    | exact PeanoMinus.distr
    | exact PeanoMinus.ltIrrefl
    | exact PeanoMinus.ltTrans
    | exact PeanoMinus.ltTri


theorem exists_base_of_peanoMinus {p : ArithmeticSentence} (h : p ∈ PeanoMinus) :
    ∃ a : BaseAxiom, a.foundation = p := by
  cases h with
  | equal p hp =>
    cases hp with
    | refl => exact ⟨.eqRefl,rfl⟩
    | symm => exact ⟨.eqSymm,rfl⟩
    | trans => exact ⟨.eqTrans,rfl⟩
    | funcExt f =>
      cases f
      all_goals first
        | exact ⟨.zeroExt,rfl⟩
        | exact ⟨.oneExt,rfl⟩
        | exact ⟨.addExt,rfl⟩
        | exact ⟨.mulExt,rfl⟩
    | relExt r =>
      cases r
      all_goals first
        | exact ⟨.eqExt,rfl⟩
        | exact ⟨.ltExt,rfl⟩
  | addZero => exact ⟨.addZero,rfl⟩
  | addAssoc => exact ⟨.addAssoc,rfl⟩
  | addComm => exact ⟨.addComm,rfl⟩
  | addEqOfLt => exact ⟨.addEqOfLt,rfl⟩
  | zeroLe => exact ⟨.zeroLe,rfl⟩
  | zeroLtOne => exact ⟨.zeroLtOne,rfl⟩
  | oneLeOfZeroLt => exact ⟨.oneLeOfZeroLt,rfl⟩
  | addLtAdd => exact ⟨.addLtAdd,rfl⟩
  | mulZero => exact ⟨.mulZero,rfl⟩
  | mulOne => exact ⟨.mulOne,rfl⟩
  | mulAssoc => exact ⟨.mulAssoc,rfl⟩
  | mulComm => exact ⟨.mulComm,rfl⟩
  | mulLtMul => exact ⟨.mulLtMul,rfl⟩
  | distr => exact ⟨.distr,rfl⟩
  | ltIrrefl => exact ⟨.ltIrrefl,rfl⟩
  | ltTrans => exact ⟨.ltTrans,rfl⟩
  | ltTri => exact ⟨.ltTri,rfl⟩

theorem base_iff_peanoMinus (p : Sentence) :
    (∃ a : BaseAxiom, p = a.formula) ↔ p.toFoundation ∈ PeanoMinus := by
  constructor
  · rintro ⟨a,rfl⟩; exact a.mem_peanoMinus
  · intro h
    obtain ⟨a,ha⟩ := exists_base_of_peanoMinus h
    refine ⟨a,?_⟩
    have ht : a.formula.toFoundation = p.toFoundation := a.to_formula.trans ha
    have := congrArg Formula.fromFoundation ht
    simpa only [Formula.from_to] using this.symm

@[simp] theorem Term.to_zero : (Term.zero : Term ξ n).toFoundation = (‘0’ : Semiterm ℒₒᵣ ξ n) := by
  change Semiterm.func _ _ = Semiterm.func _ _
  congr 1; funext i; exact Fin.elim0 i
@[simp] theorem Term.to_one : (Term.one : Term ξ n).toFoundation = (‘1’ : Semiterm ℒₒᵣ ξ n) := by
  change Semiterm.func _ _ = Semiterm.func _ _
  congr 1; funext i; exact Fin.elim0 i

@[simp] theorem Formula.to_succInd (p : Formula Nat 1) :
    p.succInd.toFoundation = Arithmetic.succInd p.toFoundation := by
  have hi : p.toFoundation/[Semiterm.bvar (0 : Fin 1)] = p.toFoundation := by
    have hv : ![Semiterm.bvar (0 : Fin 1)] = (Semiterm.bvar : Fin 1 → Semiterm ℒₒᵣ Nat 1) := by
      funext i; fin_cases i; rfl
    simp [Rewriting.subst,hv]
  have hs : (p.rewrite (fun _ => .add (.bvar (0 : Fin 1)) .one) Term.fvar).toFoundation =
      p.toFoundation/[‘(#0 + 1)’] := by
    rw [Formula.to_rewrite]
    change Semiformula.rewAux _ _ = Semiformula.rewAux _ _
    congr 1
    apply Rew.ext
    · intro i; fin_cases i
      change (Term.add (.bvar 0) .one).toFoundation = _
      simp [Term.toFoundation, Term.to_one]
      congr 1; funext j; fin_cases j <;> simp [Rew.bindAux]
      exact Term.to_one
    · intro x; rfl
  simp only [Formula.succInd, Formula.imp, Formula.toFoundation, Formula.to_neg,
    Formula.to_instantiate, Arithmetic.succInd, Semiformula.imp_eq, Semiformula.neg_eq,
    Term.to_zero, boundIndex_zero, hi, hs]
  rfl


@[simp] theorem Term.to_freeVariables (t : Term Nat n) :
    t.toFoundation.freeVariables = t.freeVariables := by
  have hu : (Finset.univ : Finset (Fin 2)) = {0,1} := by decide
  induction t <;> simp_all [Term.toFoundation, Term.freeVariables, Semiterm.freeVariables, hu]

@[simp] theorem Formula.to_freeVariables (p : Formula Nat n) :
    p.toFoundation.freeVariables = p.freeVariables := by
  have hu : (Finset.univ : Finset (Fin 2)) = {0,1} := by decide
  induction p <;> simp_all [Formula.toFoundation, Formula.freeVariables, Semiformula.freeVariables, hu]

@[simp] theorem Formula.to_fvSup (p : Formula Nat n) :
    p.toFoundation.fvSup = p.fvSup := by
  simp [Semiformula.fvSup,Formula.fvSup]

@[simp] theorem Formula.to_allClosure (p : Formula ξ n) :
    p.allClosure.toFoundation = (∀¹* p.toFoundation) := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih (.all p)


@[simp] theorem Formula.to_univCl (p : Formula Nat 0) :
    p.univCl.toFoundation = p.toFoundation.univCl := by
  unfold Formula.univCl
  rw [← Formula.to_fvSup]
  apply (Semiformula.coe_inj _ _).mp
  rw [Semiformula.coe_univCl_eq_univCl']
  simp only [Formula.to_allClosure, Rewriting.emb_allClosure, Semiformula.univCl']
  congr 1
  rw [Formula.to_rewrite]
  change (Rew.emb : Rew ℒₒᵣ Empty (0+p.toFoundation.fvSup) Nat (0+p.toFoundation.fvSup)) ▹
    (Rew.bind _ _ ▹ p.toFoundation) = Rew.fixitr 0 p.toFoundation.fvSup ▹ p.toFoundation
  rw [← TransitiveRewriting.comp_app]
  apply Semiformula.rew_eq_of_funEqOn
  · intro i; exact Fin.elim0 i
  · intro x hx
    have hx' : x < p.toFoundation.fvSup := Semiformula.lt_fvSup_of_fvar? hx
    have hx'' : x < p.fvSup := by simpa using hx'
    simp [Function.comp_def, Rew.comp_app, Rew.fixitr_fvar, hx', hx'', Term.toFoundation]

/-- Exact axiom-set correspondence, including canonical parameter closure. -/
theorem PATheory_iff (p : Sentence) :
    PATheory p ↔ p.toFoundation ∈ Peano := by
  constructor
  · intro h
    cases h with
    | base a => exact Or.inl a.mem_peanoMinus
    | induction q =>
      apply Or.inr
      refine ⟨q.toFoundation, trivial, ?_⟩
      simp
  · intro h
    rcases h with h | ⟨q, _, hq⟩
    · obtain ⟨a,ha⟩ := (base_iff_peanoMinus p).mpr h
      rw [ha]; exact PATheory.base a
    · have he : p = (Formula.fromFoundation q).succInd.univCl := by
        have ht : p.toFoundation = ((Formula.fromFoundation q).succInd.univCl).toFoundation := by
          simpa using hq
        have := congrArg Formula.fromFoundation ht
        simpa only [Formula.from_to] using this
      rw [he]
      exact PATheory.induction _

/-- Explicit finitary PA proofs are exactly ordinary Foundation PA proofs. -/
theorem pa_provable_iff (p : Sentence) :
    Provable PATheory p ↔ Peano ⊢ p.toFoundation :=
  provable_iff PATheory_iff p

#print axioms pa_provable_iff

#print axioms Formula.to_succInd
#print axioms Formula.to_univCl
#print axioms PATheory_iff

#print axioms BaseAxiom.to_formula
#print axioms BaseAxiom.mem_peanoMinus
end PalomarPA
