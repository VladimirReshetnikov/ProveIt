import PA194AdditionSuccessorLawReverse
import PA194ModelStandardNoFree
set_option autoImplicit false
set_option maxHeartbeats 32000000
set_option maxRecDepth 8192
namespace PA194AdditionA3Target
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph

def target : Form := ∀⁰ ∀⁰ ∀⁰ ∀⁰ ∀⁰ ∀⁰
  (domain (.bvar 5) 🡒 domain (.bvar 4) 🡒 domain (.bvar 3) 🡒
   domain (.bvar 2) 🡒 domain (.bvar 1) 🡒 domain (.bvar 0) 🡒
   successor (.bvar 5) (.bvar 4) 🡒
   addResult (.bvar 4) (.bvar 3) (.bvar 2) 🡒
   addResult (.bvar 5) (.bvar 3) (.bvar 1) 🡒
   successor (.bvar 1) (.bvar 0) 🡒 orderIso (.bvar 2) (.bvar 0))

theorem identity_noFree : identityStatement.freeVariables = ∅ := by decide

theorem identity_shift : identityStatement.shift = identityStatement :=
  PA194ModelLogic.syntactic_noFree_shift_fixed 0 identityStatement identity_noFree

variable {Γ : List Form}
structure Inputs (Γ : List Form) where
  equality : FormulaEquality Γ
  empty : ND.Proof Γ emptyFormula
  adjunction : ND.Proof Γ adjunctionFormula
  separation : ND.Proof Γ closedInclusiveSeparation
  identity : ND.Proof Γ identityStatement
  coherence : ND.Proof Γ addCoherenceStatement

def Inputs.shift (I : Inputs Γ) : Inputs (ND.shifted Γ) where
  equality := I.equality.shifted
  empty := emptyClosedShift I.empty
  adjunction := adjunctionClosedShift I.adjunction
  separation := additionInclusiveSeparationShift I.separation
  identity := by simpa only [identity_shift] using ND.shiftProof I.identity
  coherence := by simpa only [PA194AdditionCoherenceClosed.shift] using ND.shiftProof I.coherence

def Inputs.weaken {Δ : List Form} (I : Inputs Γ) (inc : ∀ t, t ∈ Γ → t ∈ Δ) : Inputs Δ where
  equality := I.equality.weaken inc
  empty := ND.weaken I.empty inc
  adjunction := ND.weaken I.adjunction inc
  separation := ND.weaken I.separation inc
  identity := ND.weaken I.identity inc
  coherence := ND.weaken I.coherence inc

def proof (inputs : Inputs Γ) : ND.Proof Γ target := by
  unfold target
  apply ND.allIntro
  apply ND.allIntro
  apply ND.allIntro
  apply ND.allIntro
  apply ND.allIntro
  apply ND.allIntro
  let A : Form := domain (.fvar 5)
  let B : Form := domain (.fvar 4)
  let C : Form := domain (.fvar 3)
  let D : Form := domain (.fvar 2)
  let E : Form := domain (.fvar 1)
  let F : Form := domain (.fvar 0)
  let G : Form := successor (.fvar 5) (.fvar 4)
  let H : Form := addResult (.fvar 4) (.fvar 3) (.fvar 2)
  let I : Form := addResult (.fvar 5) (.fvar 3) (.fvar 1)
  let J : Form := successor (.fvar 1) (.fvar 0)
  let Δ := J :: I :: H :: G :: F :: E :: D :: C :: B :: A ::
    ND.shifted (ND.shifted (ND.shifted (ND.shifted (ND.shifted (ND.shifted Γ)))))
  have hA : ND.Proof Δ A := ND.assumption (by simp [Δ])
  have hC : ND.Proof Δ C := ND.assumption (by simp [Δ])
  have hE : ND.Proof Δ E := ND.assumption (by simp [Δ])
  have hG : ND.Proof Δ G := ND.assumption (by simp [Δ])
  have hH : ND.Proof Δ H := ND.assumption (by simp [Δ])
  have hI : ND.Proof Δ I := ND.assumption (by simp [Δ])
  have hJ : ND.Proof Δ J := ND.assumption (by simp [Δ])
  have inp : Inputs Δ := inputs.shift.shift.shift.shift.shift.shift.weaken (fun _ hp => by simp [Δ,hp])
  have hi := additionSuccessorLawReverse inp.equality 5 4 3 1 0 2 inp.empty inp.adjunction inp.separation inp.identity inp.coherence hA hC hE hG hJ hI hH
  have out := ND.impIntro (ND.impIntro (ND.impIntro (ND.impIntro (ND.impIntro
    (ND.impIntro (ND.impIntro (ND.impIntro (ND.impIntro (ND.impIntro hi)))))))))
  convert out using 1 <;> (try dsimp [Δ,A,B,C,D,E,F,G,H,I,J]) <;> coherenceInductionSyntax

#print axioms identity_noFree
#print axioms identity_shift
#print axioms Inputs.shift
#print axioms proof
end PA194AdditionA3Target
