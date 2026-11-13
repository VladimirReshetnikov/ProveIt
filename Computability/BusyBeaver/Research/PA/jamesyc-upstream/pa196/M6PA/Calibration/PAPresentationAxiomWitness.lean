module
public import M6PA.Calibration.PAPresentationRelationExt
public import M6PA.Theory
@[expose] public section

/-! Explicit Type-valued tags, including the induction body. The completeness
lemma is Prop-valued: it does not extract executable data from theory membership. -/
namespace M6.PA.Presentation
open FFL FFL.FirstOrder

inductive BaseTag where
  | addZero
  | addAssoc
  | addComm
  | addEqOfLt
  | zeroLe
  | zeroLtOne
  | oneLeOfZeroLt
  | addLtAdd
  | mulZero
  | mulOne
  | mulAssoc
  | mulComm
  | mulLtMul
  | distr
  | ltIrrefl
  | ltTrans
  | ltTri
  deriving DecidableEq, Repr

def BaseTag.sentence : BaseTag → ArithmeticSentence
  | .addZero => Arithmetic.PeanoMinus.Axiom.addZero
  | .addAssoc => Arithmetic.PeanoMinus.Axiom.addAssoc
  | .addComm => Arithmetic.PeanoMinus.Axiom.addComm
  | .addEqOfLt => Arithmetic.PeanoMinus.Axiom.addEqOfLt
  | .zeroLe => Arithmetic.PeanoMinus.Axiom.zeroLe
  | .zeroLtOne => Arithmetic.PeanoMinus.Axiom.zeroLtOne
  | .oneLeOfZeroLt => Arithmetic.PeanoMinus.Axiom.oneLeOfZeroLt
  | .addLtAdd => Arithmetic.PeanoMinus.Axiom.addLtAdd
  | .mulZero => Arithmetic.PeanoMinus.Axiom.mulZero
  | .mulOne => Arithmetic.PeanoMinus.Axiom.mulOne
  | .mulAssoc => Arithmetic.PeanoMinus.Axiom.mulAssoc
  | .mulComm => Arithmetic.PeanoMinus.Axiom.mulComm
  | .mulLtMul => Arithmetic.PeanoMinus.Axiom.mulLtMul
  | .distr => Arithmetic.PeanoMinus.Axiom.distr
  | .ltIrrefl => Arithmetic.PeanoMinus.Axiom.ltIrrefl
  | .ltTrans => Arithmetic.PeanoMinus.Axiom.ltTrans
  | .ltTri => Arithmetic.PeanoMinus.Axiom.ltTri

def BaseTag.proof : (t : BaseTag) → ordinaryPAeq.Proof (formula t.sentence)
  | .addZero => foundationAddZeroProof
  | .addAssoc => foundationAddAssocProof
  | .addComm => foundationAddCommProof
  | .addEqOfLt => foundationAddEqOfLtProof
  | .zeroLe => foundationZeroLeProof
  | .zeroLtOne => foundationZeroLtOneProof
  | .oneLeOfZeroLt => foundationOneLeOfZeroLtProof
  | .addLtAdd => foundationAddLtAddProof
  | .mulZero => foundationMulZeroProof
  | .mulOne => foundationMulOneProof
  | .mulAssoc => foundationMulAssocProof
  | .mulComm => foundationMulCommProof
  | .mulLtMul => foundationMulLtMulProof
  | .distr => foundationDistrProof
  | .ltIrrefl => foundationLtIrreflProof
  | .ltTrans => foundationLtTransProof
  | .ltTri => foundationLtTriProof

theorem BaseTag.mem (t : BaseTag) : t.sentence ∈ Arithmetic.PeanoMinus := by
  cases t with
  | addZero => exact Arithmetic.PeanoMinus.addZero
  | addAssoc => exact Arithmetic.PeanoMinus.addAssoc
  | addComm => exact Arithmetic.PeanoMinus.addComm
  | addEqOfLt => exact Arithmetic.PeanoMinus.addEqOfLt
  | zeroLe => exact Arithmetic.PeanoMinus.zeroLe
  | zeroLtOne => exact Arithmetic.PeanoMinus.zeroLtOne
  | oneLeOfZeroLt => exact Arithmetic.PeanoMinus.oneLeOfZeroLt
  | addLtAdd => exact Arithmetic.PeanoMinus.addLtAdd
  | mulZero => exact Arithmetic.PeanoMinus.mulZero
  | mulOne => exact Arithmetic.PeanoMinus.mulOne
  | mulAssoc => exact Arithmetic.PeanoMinus.mulAssoc
  | mulComm => exact Arithmetic.PeanoMinus.mulComm
  | mulLtMul => exact Arithmetic.PeanoMinus.mulLtMul
  | distr => exact Arithmetic.PeanoMinus.distr
  | ltIrrefl => exact Arithmetic.PeanoMinus.ltIrrefl
  | ltTrans => exact Arithmetic.PeanoMinus.ltTrans
  | ltTri => exact Arithmetic.PeanoMinus.ltTri

inductive EqualityTag where
  | refl | symm | trans | zero | one | add | mul | eq | lt
  deriving DecidableEq, Repr

def EqualityTag.sentence : EqualityTag → ArithmeticSentence
  | .refl => Theory.Eq.refl ℒₒᵣ
  | .symm => Theory.Eq.symm ℒₒᵣ
  | .trans => Theory.Eq.trans ℒₒᵣ
  | .zero => Theory.Eq.funcExt Language.ORing.Func.zero
  | .one => Theory.Eq.funcExt Language.ORing.Func.one
  | .add => Theory.Eq.funcExt Language.ORing.Func.add
  | .mul => Theory.Eq.funcExt Language.ORing.Func.mul
  | .eq => Theory.Eq.relExt Language.ORing.Rel.eq
  | .lt => Theory.Eq.relExt Language.ORing.Rel.lt

def EqualityTag.proof : (t : EqualityTag) → ordinaryPAeq.Proof (formula t.sentence)
  | .refl => foundationEqReflProof
  | .symm => foundationEqSymmProof
  | .trans => foundationEqTransProof
  | .zero => foundationEqZeroProof
  | .one => foundationEqOneProof
  | .add => foundationEqAddProof
  | .mul => foundationEqMulProof
  | .eq => foundationEqRelProof
  | .lt => foundationLtRelProof

theorem EqualityTag.mem (t : EqualityTag) : t.sentence ∈ Theory.eqAxiom ℒₒᵣ := by
  cases t with
  | refl => exact .refl
  | symm => exact .symm
  | trans => exact .trans
  | zero => exact Theory.eqAxiom.funcExt (L := ℒₒᵣ) Language.ORing.Func.zero
  | one => exact Theory.eqAxiom.funcExt (L := ℒₒᵣ) Language.ORing.Func.one
  | add => exact Theory.eqAxiom.funcExt (L := ℒₒᵣ) Language.ORing.Func.add
  | mul => exact Theory.eqAxiom.funcExt (L := ℒₒᵣ) Language.ORing.Func.mul
  | eq => exact Theory.eqAxiom.relExt (L := ℒₒᵣ) Language.ORing.Rel.eq
  | lt => exact Theory.eqAxiom.relExt (L := ℒₒᵣ) Language.ORing.Rel.lt

inductive AxiomTag where
  | base (t : BaseTag)
  | equality (t : EqualityTag)
  | induction (p : ArithmeticSemiproposition 1)

def AxiomTag.sentence : AxiomTag → ArithmeticSentence
  | .base t => t.sentence
  | .equality t => t.sentence
  | .induction p => (Arithmetic.succInd p).univCl

def AxiomTag.compile : (w : AxiomTag) → ordinaryPAeq.Proof (formula w.sentence)
  | .base t => t.proof
  | .equality t => t.proof
  | .induction p => foundationInductionSentenceProof p

theorem AxiomTag.mem (w : AxiomTag) : w.sentence ∈ theory := by
  cases w with
  | base t => exact Or.inl t.mem
  | equality t => exact Or.inl (.equal _ t.mem)
  | induction p => exact Or.inr ⟨p,Set.mem_univ p,rfl⟩

structure AxiomWitness (σ : ArithmeticSentence) where
  tag : AxiomTag
  correct : tag.sentence = σ

def AxiomWitness.compile {σ : ArithmeticSentence} (w : AxiomWitness σ) : ordinaryPAeq.Proof (formula σ) :=
  w.correct ▸ w.tag.compile

theorem AxiomWitness.mem {σ : ArithmeticSentence} (w : AxiomWitness σ) : σ ∈ theory :=
  w.correct ▸ w.tag.mem

theorem equality_witness_exists {σ : ArithmeticSentence} (h : σ ∈ Theory.eqAxiom ℒₒᵣ) :
    Nonempty (AxiomWitness σ) := by
  cases h with
  | refl => exact ⟨⟨.equality .refl,rfl⟩⟩
  | symm => exact ⟨⟨.equality .symm,rfl⟩⟩
  | trans => exact ⟨⟨.equality .trans,rfl⟩⟩
  | funcExt f => cases f with
    | zero => exact ⟨⟨.equality .zero,rfl⟩⟩
    | one => exact ⟨⟨.equality .one,rfl⟩⟩
    | add => exact ⟨⟨.equality .add,rfl⟩⟩
    | mul => exact ⟨⟨.equality .mul,rfl⟩⟩
  | relExt r => cases r with
    | eq => exact ⟨⟨.equality .eq,rfl⟩⟩
    | lt => exact ⟨⟨.equality .lt,rfl⟩⟩

theorem axiom_witness_exists {σ : ArithmeticSentence} (h : σ ∈ theory) : Nonempty (AxiomWitness σ) := by
  rcases h with h | ⟨p,hp,rfl⟩
  · cases h with
    | equal p hp => exact equality_witness_exists hp
    | addZero => exact ⟨⟨.base .addZero,rfl⟩⟩
    | addAssoc => exact ⟨⟨.base .addAssoc,rfl⟩⟩
    | addComm => exact ⟨⟨.base .addComm,rfl⟩⟩
    | addEqOfLt => exact ⟨⟨.base .addEqOfLt,rfl⟩⟩
    | zeroLe => exact ⟨⟨.base .zeroLe,rfl⟩⟩
    | zeroLtOne => exact ⟨⟨.base .zeroLtOne,rfl⟩⟩
    | oneLeOfZeroLt => exact ⟨⟨.base .oneLeOfZeroLt,rfl⟩⟩
    | addLtAdd => exact ⟨⟨.base .addLtAdd,rfl⟩⟩
    | mulZero => exact ⟨⟨.base .mulZero,rfl⟩⟩
    | mulOne => exact ⟨⟨.base .mulOne,rfl⟩⟩
    | mulAssoc => exact ⟨⟨.base .mulAssoc,rfl⟩⟩
    | mulComm => exact ⟨⟨.base .mulComm,rfl⟩⟩
    | mulLtMul => exact ⟨⟨.base .mulLtMul,rfl⟩⟩
    | distr => exact ⟨⟨.base .distr,rfl⟩⟩
    | ltIrrefl => exact ⟨⟨.base .ltIrrefl,rfl⟩⟩
    | ltTrans => exact ⟨⟨.base .ltTrans,rfl⟩⟩
    | ltTri => exact ⟨⟨.base .ltTri,rfl⟩⟩
  · exact ⟨⟨.induction p,rfl⟩⟩

theorem axiom_image_provable {σ : ArithmeticSentence} (h : σ ∈ theory) : ordinaryPAeq ⊢ formula σ := by
  rcases axiom_witness_exists h with ⟨w⟩
  exact ⟨w.compile⟩

#print axioms AxiomWitness.compile
#print axioms axiom_witness_exists
#print axioms axiom_image_provable
end M6.PA.Presentation

