import PA194AdditionCoherenceClosed
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8192
namespace PA194AdditionA2Target
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph

def target : Form := ∀⁰ ∀⁰ ∀⁰ ∀⁰ ∀⁰ ∀⁰
  (domain (.bvar 5) 🡒 domain (.bvar 4) 🡒 domain (.bvar 3) 🡒
   domain (.bvar 2) 🡒 domain (.bvar 1) 🡒 domain (.bvar 0) 🡒
   addResult (.bvar 5) (.bvar 4) (.bvar 3) 🡒
   addResult (.bvar 2) (.bvar 1) (.bvar 0) 🡒
   orderIso (.bvar 5) (.bvar 2) 🡒 orderIso (.bvar 4) (.bvar 1) 🡒
   orderIso (.bvar 3) (.bvar 0))

variable {Γ : List Form}
def globalShift (h : ND.Proof Γ addCoherenceStatement) :
    ND.Proof (ND.shifted Γ) addCoherenceStatement := by
  simpa only [PA194AdditionCoherenceClosed.shift] using ND.shiftProof h

def proof (h : ND.Proof Γ addCoherenceStatement) : ND.Proof Γ target := by
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
  let G : Form := addResult (.fvar 5) (.fvar 4) (.fvar 3)
  let H : Form := addResult (.fvar 2) (.fvar 1) (.fvar 0)
  let I : Form := orderIso (.fvar 5) (.fvar 2)
  let J : Form := orderIso (.fvar 4) (.fvar 1)
  let Δ := J :: I :: H :: G :: F :: E :: D :: C :: B :: A ::
    ND.shifted (ND.shifted (ND.shifted (ND.shifted (ND.shifted (ND.shifted Γ)))))
  have hA : ND.Proof Δ A := ND.assumption (by simp [Δ])
  have hB : ND.Proof Δ B := ND.assumption (by simp [Δ])
  have hD : ND.Proof Δ D := ND.assumption (by simp [Δ])
  have hE : ND.Proof Δ E := ND.assumption (by simp [Δ])
  have hG : ND.Proof Δ G := ND.assumption (by simp [Δ])
  have hH : ND.Proof Δ H := ND.assumption (by simp [Δ])
  have hI : ND.Proof Δ I := ND.assumption (by simp [Δ])
  have hJ : ND.Proof Δ J := ND.assumption (by simp [Δ])
  have hglobal : ND.Proof Δ addCoherenceStatement :=
    ND.weaken (globalShift (globalShift (globalShift (globalShift (globalShift (globalShift h))))))
      (fun _ hp => by simp [Δ,hp])
  have hi := additionCoherenceApply 5 2 4 1 3 0 hglobal hA hD hB hE hI hJ hG hH
  have out := ND.impIntro (ND.impIntro (ND.impIntro (ND.impIntro (ND.impIntro
    (ND.impIntro (ND.impIntro (ND.impIntro (ND.impIntro (ND.impIntro hi)))))))))
  convert out using 1 <;> (try dsimp [Δ,A,B,C,D,E,F,G,H,I,J]) <;> coherenceInductionSyntax

#print axioms globalShift
#print axioms proof
end PA194AdditionA2Target
