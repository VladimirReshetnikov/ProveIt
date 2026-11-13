module
public import M6PA.Theory
public import M6PA.Calibration.RelationalAdditionResultSupplier
public import M6PA.Calibration.RelationalParameterClosure
public import M6PA.Calibration.RelationalOrdinalSuccessor
public import M6PA.Calibration.RelationalOrdinalEmpty
@[expose] public section

/-! Closed addition totality, with every allocator and Separation obligation
retained. This closes a supplied theorem, never an open ND hypothesis. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def addClosedResult : Form := closeParameter (addTotalStatement 0)

def addClosedResultSupplier (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i, f i < lo) (hz : lo+7 < z)
    (hsep : lo+4+depth (∼prefixProperty 0) ≤ z)
    (hadj : lo+3+lkBudget adjunctionDerivation ≤ z)
    (hbudget : lo+1+lkBudget (addTotalDerivation 0) ≤ z) :
    NativeCalculus.ActualBasis.Proof (code addClosedResult f lo z) := by
  apply closeParameterSupplier
  apply addTotalSupplier 0 (shiftedLabels f lo) (lo+1) z (by omega)
  · intro i
    cases i with
    | zero => simp [shiftedLabels]
    | succ i => simpa [shiftedLabels] using Nat.lt_trans (hf i) (Nat.lt_succ_self lo)
  · omega
  · omega
  · omega
  · omega

#print axioms addClosedResultSupplier
end M6.PA.RelationalSource.PairGraph

namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND

def successorClosed : Form := closeParameter (Ordinal.domainSuccessorStatement (.fvar 0))

def successorClosedSupplier (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i, f i < lo) (hz : lo+7 < z)
    (hadj : lo+3+lkBudget adjunctionDerivation ≤ z)
    (hbudget : lo+1+lkBudget (Ordinal.domainSuccessorDerivation (.fvar 0)) ≤ z) :
    NativeCalculus.ActualBasis.Proof (code successorClosed f lo z) := by
  apply closeParameterSupplier
  apply Ordinal.domainSuccessorSupplier (.fvar 0) (shiftedLabels f lo) (lo+1) z (by omega)
  · intro i
    cases i with
    | zero => simp [shiftedLabels]
    | succ i => simpa [shiftedLabels] using Nat.lt_trans (hf i) (Nat.lt_succ_self lo)
  · omega
  · omega
  · omega

def zeroInhabited : Form := ∃¹ (Ordinal.domain (.bvar 0) ⋏ Ordinal.zero (.bvar 0))

def zeroInhabitedFromEmpty {Γ : List Form} (h : ND.Proof Γ emptyFormula) :
    ND.Proof Γ zeroInhabited := by
  apply exsElim h
  let σ : Ordinal.Formula 1 := Ordinal.zero (.bvar 0)
  let C := σ.free :: shifted Γ
  have hz : ND.Proof C (Ordinal.zero (.fvar 0)) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [σ]; ordinalSyntax)
  apply exsIntro _ (.fvar 0)
  convert andIntro (Ordinal.zeroDomain (.fvar 0) hz) hz using 1 <;>
    ((try simp only [zeroInhabited]); ordinalSyntax)

def zeroInhabitedDerivation : ND.Proof [emptyFormula] zeroInhabited :=
  zeroInhabitedFromEmpty (assumption (by simp))

def zeroInhabitedSupplier (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i, f i < lo) (hz : lo+1 < z)
    (hbudget : lo+lkBudget zeroInhabitedDerivation ≤ z) :
    NativeCalculus.ActualBasis.Proof (code zeroInhabited f lo z) := by
  apply compileContext [emptyFormula] _ zeroInhabitedDerivation f lo z hlo hf hbudget
  intro p hp
  have he : p = emptyFormula := by simpa using hp
  subst p
  exact emptySupplier f lo z hz

#print axioms successorClosedSupplier
#print axioms zeroInhabitedFromEmpty
#print axioms zeroInhabitedSupplier
end M6.PA.ForwardRelational

