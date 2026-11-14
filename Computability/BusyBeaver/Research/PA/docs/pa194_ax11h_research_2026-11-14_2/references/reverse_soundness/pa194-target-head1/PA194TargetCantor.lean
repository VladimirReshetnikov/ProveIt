import PA194AllInversion
import PA194DerivationCompiler
import PA194ChildCodes
/-! Exact machine-Cantor constructors and a one-leaf target certificate.
The full target checker and the Nat h1 code/derivation identity are open. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false
namespace PA194TargetCantor
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PRAHerbrandSelection PRABoundedWitness PA194PathIterator PA194NumeralCode
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor

def cantorMatrix : Semisentence language 3 := Semiformula.lMap embedding SetTheory.BusyBeaver.ZFC.ArithmeticCantor.pairDef.val

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

theorem modelCantorTotal : M↓[language] ⊧ (∀⁰* ∃⁰ cantorMatrix) := by
  simp only [models_iff, Semiformula.eval_allClosure, Semiformula.eval_ex]
  intro e
  refine ⟨cantor (e 0) (e 1), ?_⟩
  rw [cantorMatrix, Semiformula.eval_lMap, PRAModelIOpenPairing.reduct_eq_standard]
  have hv : (cantor (e 0) (e 1) :> e) = ![cantor (e 0) (e 1),e 0,e 1] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    refine Fin.cases rfl (fun k => ?_) j
    exact Fin.cases rfl (fun l => Fin.elim0 l) k
  rw [hv]
  exact (cantor_defined (V := M)).defined ![cantor (e 0) (e 1),e 0,e 1] |>.mpr rfl

theorem modelCantorSelected (f : Code 2)
    (h : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt cantorMatrix f)
    (a b : M) : F f ![a,b] = cantor a b := by
  have hm := models_of_provable (inferInstance : M↓[language] ⊧* PRA) h
  simp only [models_iff, Semiformula.eval_allClosure] at hm
  have hm := hm ![a,b]
  rw [PRAHerbrandSelection.openMatrixAt, Semiformula.eval_substs] at hm
  have hv : (Semiterm.val (L := language) ![a,b] Empty.elim ∘
      Fin.cases (PRATheory.applyCode f (PRATheory.vars 2)) (PRATheory.vars 2)) = ![F f ![a,b],a,b] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change F f (Semiterm.val (L := language) ![a,b] Empty.elim ∘ PRATheory.vars 2) = _
      congr 1
    · refine Fin.cases rfl (fun k => ?_) j
      exact Fin.cases rfl (fun l => Fin.elim0 l) k
  rw [hv,cantorMatrix, Semiformula.eval_lMap, PRAModelIOpenPairing.reduct_eq_standard] at hm
  exact ((cantor_defined (V := M)).defined ![F f ![a,b],a,b]).mp hm
end models

theorem PRA_has_cantorCode : ∃ f : Code 2, Primrec (eval f) ∧
    PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt cantorMatrix f := by
  apply PRA_boundedWitness
  · exact ParsonsHierarchyMap.hierarchy SetTheory.BusyBeaver.ZFC.ArithmeticCantor.pairDef.sigma_prop
  · apply Theory.Proof.complete_on_eq_models.{0,0}
    intro M _ _ _ _
    exact modelCantorTotal

noncomputable def fixedCantor : Code 2 := Classical.choose PRA_has_cantorCode
theorem fixedCantor_certified : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt cantorMatrix fixedCantor :=
  (Classical.choose_spec PRA_has_cantorCode).2

noncomputable def machineImp {n : Nat} (a b : Code n) : Code n :=
  bin mulCode (numeralCode n 4) (bin fixedCantor a b)
noncomputable def machineAll {n : Nat} (a b : Code n) : Code n :=
  bin addCode (machineImp b a) (numeralCode n 2)
noncomputable def machineNeg {n : Nat} (a : Code n) : Code n :=
  machineImp a (numeralCode n 1)
noncomputable def machineEx {n : Nat} (a b : Code n) : Code n :=
  machineNeg (machineAll a (machineNeg b))
noncomputable def machineHead1 : Code 2 :=
  machineImp (machineEx (.proj 0) (machineAll (.proj 0) (.proj 1))) (.proj 1)
noncomputable def leafCertificate : Code 2 :=
  bin pairCode (numeralCode 2 2) (bin pairCode (.proj 0) (.proj 1))


section targetModels
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance candidateZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance candidateOne : One M := ⟨F oneCode Fin.elim0⟩
local instance candidateAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance candidateMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance candidateLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

noncomputable def impValue (a b : M) : M := 4 * cantor a b
noncomputable def allValue (a b : M) : M := impValue b a + 2
noncomputable def negValue (a : M) : M := impValue a 1
noncomputable def exValue (a b : M) : M := negValue (allValue a (negValue b))
noncomputable def head1Value (a b : M) : M := impValue (exValue a (allValue a b)) b

theorem machineImp_model {n : Nat} (a b : Code n) (e : Fin n → M) :
    F (machineImp a b) e = impValue (F a e) (F b e) := by
  rw [machineImp,modelBin,modelNumeralCode,modelBin,modelCantorSelected fixedCantor fixedCantor_certified]
  rfl

theorem machineAll_model {n : Nat} (a b : Code n) (e : Fin n → M) :
    F (machineAll a b) e = allValue (F a e) (F b e) := by
  rw [machineAll,modelBin,machineImp_model,modelNumeralCode]
  rfl

theorem machineNeg_model {n : Nat} (a : Code n) (e : Fin n → M) :
    F (machineNeg a) e = negValue (F a e) := by
  rw [machineNeg,machineImp_model,modelNumeralCode]
  simp [negValue]

theorem machineEx_model {n : Nat} (a b : Code n) (e : Fin n → M) :
    F (machineEx a b) e = exValue (F a e) (F b e) := by
  rw [machineEx,machineNeg_model,machineAll_model,machineNeg_model]
  rfl

theorem machineHead1_model (a b : M) : F machineHead1 ![a,b] = head1Value a b := by
  rw [machineHead1,machineImp_model,machineEx_model,machineAll_model,modelProjection,modelProjection]
  rfl
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem leafCertificate_model (a b : M) :
    F leafCertificate ![a,b] = pair 2 (pair a b) := by
  rw [leafCertificate,modelBin,modelNumeralCode,modelBin,modelProjection,modelProjection,
    modelPairCode,modelPairCode]
  rfl


/-- A target proof relation for the single head-1 axiom schema. The certificate
is a tagged Foundation pair; the theorem number uses the machine's Cantor code. -/
def Head1Certificate (c y : M) : Prop :=
  ∃ a b, c = pair 2 (pair a b) ∧ y = F machineHead1 ![a,b]

theorem leaf_predicate_def (f : M → M → M) (hf : 𝚺₁-Function₂ f) :
    𝚺₁-Relation (fun c y : M => ∃ a b, c = pair 2 (pair a b) ∧ y = f a b) := by
  haveI := hf
  definability

theorem head1Certificate_definable : 𝚺₁-Relation (Head1Certificate (M := M)) := by
  haveI : 𝚺₁-Function₂ (fun a b : M => F machineHead1 ![a,b]) := by
    have h : 𝚺₁.DefinableFunction (fun e : Fin 2 → M => F machineHead1 e) :=
      HierarchySymbol.Defined.to_definable _ (PA194CodeGraph.modelGraph (M := M) machineHead1)
    convert h using 1
    funext e
    exact congrArg (fun v : Fin 2 → M => F machineHead1 v) (Matrix.fun_eq_vec_two e).symm
  exact leaf_predicate_def (fun a b => F machineHead1 ![a,b]) inferInstance

theorem head1Leaf_model (a b : M) :
    Head1Certificate (F leafCertificate ![a,b]) (F machineHead1 ![a,b]) := by
  exact ⟨a,b,leafCertificate_model a b,rfl⟩

#print axioms head1Certificate_definable
#print axioms head1Leaf_model

#print axioms machineHead1_model
end targetModels

section standard

theorem cantor_eq_machine (a b : Nat) :
    cantor a b = M6.Source.Cantor.pair a b := by
  have h (n : Nat) : triangle n = M6.Source.Cantor.triangle n := by
    induction n with
    | zero => simp [triangle, M6.Source.Cantor.triangle]
    | succ n ih =>
      change triangle (n+1) = M6.Source.Cantor.triangle n + n + 1
      rw [triangle_succ, ih]
  rw [cantor, M6.Source.Cantor.pair, h]

noncomputable def natImp (a b : Nat) : Nat := 4 * cantor a b
noncomputable def natAll (a b : Nat) : Nat := natImp b a + 2
noncomputable def natNeg (a : Nat) : Nat := natImp a 1
noncomputable def natEx (a b : Nat) : Nat := natNeg (natAll a (natNeg b))
noncomputable def natHead1 (a b : Nat) : Nat := natImp (natEx a (natAll a b)) b

noncomputable def head1_exact_standard (a b : Nat) :
    PA194DerivationCompiler.Derivation (natHead1 a b) := by
  have h := PA194DerivationCompiler.Derivation.h1 a b
  simpa only [natHead1,natEx,natNeg,natAll,natImp,cantor_eq_machine,
    PA196.Commands.Code.head1, PA196.Commands.Code.ex, PA196.Commands.Code.N,
    PA196.Commands.Code.U, PA196.Commands.Code.I] using h

local instance : Structure language Nat := natStructure
local instance : Structure.Eq language Nat := ⟨fun _ _ => iff_of_eq rfl⟩
local instance : Nat↓[language] ⊧* PRA := nat_models_PRA

theorem eval_fixedCantor (a b : Nat) :
    eval fixedCantor (a ::ᵥ b ::ᵥ List.Vector.nil) = M6.Source.Cantor.pair a b := by
  have hm := models_of_provable (inferInstance : Nat↓[language] ⊧* PRA) fixedCantor_certified
  simp only [models_iff, Semiformula.eval_allClosure] at hm
  have hm := hm ![a,b]
  rw [PRAHerbrandSelection.openMatrixAt, Semiformula.eval_substs] at hm
  have hv : (Semiterm.val (L := language) ![a,b] Empty.elim ∘
      Fin.cases (PRATheory.applyCode fixedCantor (PRATheory.vars 2)) (PRATheory.vars 2)) =
      ![eval fixedCantor (a ::ᵥ b ::ᵥ List.Vector.nil),a,b] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change eval fixedCantor (List.Vector.ofFn (Semiterm.val (L := language) ![a,b] Empty.elim ∘ PRATheory.vars 2)) = _
      rw [ofFn_two]
      rfl
    · refine Fin.cases rfl (fun k => ?_) j
      exact Fin.cases rfl (fun l => Fin.elim0 l) k
  rw [hv,cantorMatrix, Semiformula.eval_lMap, nat_reduct] at hm
  have h := ((cantor_defined (V := Nat)).defined ![eval fixedCantor (a ::ᵥ b ::ᵥ List.Vector.nil),a,b]).mp hm
  exact h.trans (cantor_eq_machine a b)


#print axioms head1_exact_standard
end standard

#print axioms modelCantorTotal
#print axioms PRA_has_cantorCode
#print axioms modelCantorSelected
end PA194TargetCantor
