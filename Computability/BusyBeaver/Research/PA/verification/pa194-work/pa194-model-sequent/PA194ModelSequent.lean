import PA194ModelContext
import ConPASequent

/-!
# Sequents of nonstandard length in the numerical calculus

`ConPASequent` instantiated with the separate-diagonal numerical calculus of a candidate-PRA
model `M` whose arithmetic reduct satisfies `𝗜𝚺₁`: implication `impValue`, universal
quantifier `allValue`, provability `TargetProvable`.

`Derives Γ a` says that the implication chain `seqValue Γ a` of the internal list `Γ` (a
Foundation vector in `M`, possibly of nonstandard length) and the code `a` is provable.

* `Derives.closed`, `Derives.assumption`, `Derives.mp`: the rules of a context calculus;
* `derives_adjoin_iff`: the deduction theorem;
* `Derives.cut`, `Derives.mono`: cut and the structural rules;
* `Derives.generalize`: generalization under hypotheses closed under the quantifier;
* `Ctx.derives`: a proof tree of standard size from a standard list of hypotheses
  (`PA194ModelContext`) is valid under an internal list that derives those hypotheses. This
  moves every fixed-shape rule of `PA194ModelContext` under hypothesis lists of nonstandard
  length.

Nothing here concerns the translation of source formulas or an internal derivation.
-/
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194ModelLogic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor

/-- The defining formula of the triangular pairing. -/
abbrev cantorGraph : 𝚺₀.Semisentence 3 := SetTheory.BusyBeaver.ZFC.ArithmeticCantor.pairDef

/-- `z = impValue a b`. -/
def impGraph : 𝚺₁.Semisentence 3 := .mkSigma “z a b. ∃ p, !cantorGraph p a b ∧ z = 4 * p”

/-- `z = allValue x a`. -/
def allGraph : 𝚺₁.Semisentence 3 := .mkSigma “z x a. ∃ p, !cantorGraph p a x ∧ z = 4 * p + 2”

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem impValue_defined : 𝚺₁-Function₂ (impValue : M → M → M) via impGraph := .mk fun v => by
  simp [impGraph, impValue]

theorem allValue_defined : 𝚺₁-Function₂ (allValue : M → M → M) via allGraph := .mk fun v => by
  simp [allGraph, allValue, impValue]

/-- The numerical calculus as a calculus with a quantifier. -/
noncomputable def quantM : ConPA.Sequent.Quant M where
  imp := impValue
  impDef := impGraph
  imp_defined := impValue_defined
  Pr := TargetProvable
  pr_definable := targetProvable_definable
  mp := fun ha hab => tp_mp ha hab
  k := imp_k
  s := imp_s
  comp := imp_comp
  exchange := imp_exchange
  all := allValue
  allDef := allGraph
  all_defined := allValue_defined
  gen := fun x _ ha => tp_gen x ha
  dist := r2

/-- The implication chain `γ₀ → (γ₁ → (… → a))` of the internal list `Γ`. -/
noncomputable def seqValue (Γ a : M) : M := ConPA.Sequent.seq (quantM (M := M)).toCalc Γ a

@[simp] theorem seqValue_nil (a : M) : seqValue 0 a = a := by simp [seqValue]

@[simp] theorem seqValue_adjoin (γ Γ a : M) :
    seqValue (γ ∷ Γ) a = impValue γ (seqValue Γ a) := by
  simp [seqValue, quantM]

/-- `Γ ⊢ a` for an internal list `Γ`. -/
def Derives (Γ a : M) : Prop := TargetProvable (seqValue Γ a)

theorem derives_nil (a : M) : Derives 0 a ↔ TargetProvable a := by simp [Derives]

theorem Derives.closed {a : M} (h : TargetProvable a) (Γ : M) : Derives Γ a :=
  ConPA.Sequent.seq_weaken (quantM (M := M)).toCalc h Γ

theorem Derives.assumption (Γ : M) {i : M} (hi : i < len Γ) : Derives Γ Γ.[i] :=
  ConPA.Sequent.seq_proj (quantM (M := M)).toCalc Γ i hi

theorem Derives.mp {Γ a b : M} (ha : Derives Γ a) (hab : Derives Γ (impValue a b)) :
    Derives Γ b :=
  ConPA.Sequent.seq_mp (quantM (M := M)).toCalc ha hab

/-- The deduction theorem. -/
theorem derives_adjoin_iff (γ Γ a : M) : Derives (γ ∷ Γ) a ↔ Derives Γ (impValue γ a) :=
  ConPA.Sequent.seq_adjoin_iff (quantM (M := M)).toCalc γ Γ a

theorem Derives.up {Γ a : M} (h : Derives Γ a) (γ : M) : Derives (γ ∷ Γ) a :=
  ConPA.Sequent.seq_up (quantM (M := M)).toCalc h γ

/-- Cut: `Δ` derives whatever a list of its consequences derives. -/
theorem Derives.cut {Γ Δ a : M} (h : Derives Γ a) (hΓ : ∀ i < len Γ, Derives Δ Γ.[i]) :
    Derives Δ a :=
  ConPA.Sequent.seq_cut_rule (quantM (M := M)).toCalc h hΓ

/-- Weakening, exchange and contraction. -/
theorem Derives.mono {Γ Δ a : M} (h : Derives Γ a)
    (hΓ : ∀ i < len Γ, ∃ j < len Δ, Γ.[i] = Δ.[j]) : Derives Δ a :=
  ConPA.Sequent.seq_mono_rule (quantM (M := M)).toCalc h hΓ

/-- Generalization under hypotheses that are closed under the quantifier. -/
theorem Derives.generalize {Γ a : M} (x : M) (h : Derives Γ a)
    (hv : ∀ i < len Γ, TargetProvable (impValue Γ.[i] (allValue x Γ.[i]))) :
    Derives Γ (allValue x a) :=
  ConPA.Sequent.seq_gen (quantM (M := M)) x h hv

/-- A proof tree of standard size from the standard list `Γ` is valid under every internal
list that derives the entries of `Γ`. -/
theorem Ctx.derives {Γ : List M} {a : M} (d : Ctx Γ a) (Δ : M)
    (h : ∀ b, b ∈ Γ → Derives Δ b) : Derives Δ a := by
  induction d with
  | assumption hb => exact h _ hb
  | closed p => exact Derives.closed p Δ
  | mp _ _ ihp ihq => exact Derives.mp ihp ihq

/-- Proof by cases under an internal list. -/
theorem Derives.cases {Γ : M} (a : M) {c : M} (hp : Derives (a ∷ Γ) c)
    (hn : Derives (negValue a ∷ Γ) c) : Derives Γ c := by
  have hp' := (derives_adjoin_iff a Γ c).mp hp
  have hn' := (derives_adjoin_iff (negValue a) Γ c).mp hn
  let a1 : Ctx [a, impValue a c, impValue (negValue a) c] a := .assumption (by simp)
  let f1 : Ctx [a, impValue a c, impValue (negValue a) c] (impValue a c) :=
    .assumption (by simp)
  let p1 : Ctx [a, impValue a c, impValue (negValue a) c] c := .mp a1 f1
  let a2 : Ctx [negValue a, impValue a c, impValue (negValue a) c] (negValue a) :=
    .assumption (by simp)
  let f2 : Ctx [negValue a, impValue a c, impValue (negValue a) c]
      (impValue (negValue a) c) := .assumption (by simp)
  let p2 : Ctx [negValue a, impValue a c, impValue (negValue a) c] c := .mp a2 f2
  have d : Ctx [impValue a c, impValue (negValue a) c] c := Ctx.casesOnFormula a p1 p2
  exact d.derives Γ (fun b hb => by
    rcases List.mem_cons.mp hb with (rfl | hb)
    · exact hp'
    · rcases List.mem_cons.mp hb with (rfl | hb)
      · exact hn'
      · exact False.elim (List.not_mem_nil hb))

#print axioms Derives.assumption
#print axioms Derives.mp
#print axioms derives_adjoin_iff
#print axioms Derives.cut
#print axioms Derives.mono
#print axioms Derives.generalize
#print axioms Ctx.derives
#print axioms Derives.cases
end models
end PA194ModelLogic
