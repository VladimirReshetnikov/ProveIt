module
public import M6PA.Theory
public import M6PA.Calibration.PAPresentationZeroLe
@[expose] public section

namespace M6.PA.Presentation
open FFL FFL.FirstOrder

theorem rew_implies_any {ξ ζ : Type} {n m : Nat} (ω : Rew language ξ n ζ m)
    (p q : Semiformula language ξ n) : Semiformula.rewAux ω (implies p q) =
      implies (Semiformula.rewAux ω p) (Semiformula.rewAux ω q) := by
  exact congrArg (fun r : Semiformula language ζ m => Semiformula.or r (Semiformula.rewAux ω q))
    (Semiformula.rewAux_neg ω p)

theorem less_body_free (a b : GroundTerm) :
    (eq (add (Rew.bShift a) (succ (.bvar 0))) (Rew.bShift b)).free =
      eq (add (Rew.shift a) (succ (.fvar 0))) (Rew.shift b) := by
  change Semiformula.rewAux Rew.free _ = _
  rw [eq_rew,rew_add,rew_succ,Rew.free_bShift_app,Rew.free_bShift_app]
  rfl

def ND.lessElim {Γ : List ND.Form} {q : ND.Form} (a b : GroundTerm)
    (h : ND.Proof Γ (less a b))
    (d : ND.Proof (eq (add (Rew.shift a) (succ (.fvar 0))) (Rew.shift b) :: ND.shifted Γ) q.shift) :
    ND.Proof Γ q := by
  apply ND.exsElim h
  rw [less_body_free]
  exact d

theorem less_shift (a b : GroundTerm) :
    (less a b).shift = less (Rew.shift a) (Rew.shift b) := less_rew Rew.shift a b

def addLtAddInstance (a b c : GroundTerm) : ND.Proof addLawsContext
    (implies (less a b) (less (add a c) (add b c))) := by
  let Γ := addLawsContext
  let E := equalityContextPremises.weaken (Δ := Γ) (by intro p hp; simp [Γ,addLawsContext,hp])
  apply ND.impIntro
  let Δ := less a b :: Γ
  have hab : ND.Proof Δ (less a b) := ND.assumption (by simp [Δ])
  apply ND.lessElim a b hab
  let x := Rew.shift a
  let y := Rew.shift b
  let z := Rew.shift c
  let w : GroundTerm := .fvar 0
  let h := eq (add x (succ w)) y
  let Θ := h :: ND.shifted Δ
  have incl : ∀ p,p ∈ Γ → p ∈ Θ := by
    intro p hp
    apply List.mem_cons_of_mem
    exact closed_members_shifted addLawsContext_closed (fun p hp => List.mem_cons_of_mem _ hp) p hp
  let ET := E.weaken incl
  let A := derivedAddLaws.weaken incl
  have hw : ND.Proof Θ h := ND.assumption (by simp [Θ])
  have h1 := A.assoc x z (succ w)
  have h2 := ET.additionOf (ET.reflexive x) (A.comm z (succ w))
  have h3 := ET.symmetryOf (A.assoc x (succ w) z)
  have h4 := ET.additionOf hw (ET.reflexive z)
  have he := ET.transitivityOf (ET.transitivityOf (ET.transitivityOf h1 h2) h3) h4
  have hout := ND.lessIntro (add x z) (add y z) w he
  simpa only [less_shift,rew_add] using hout

def foundationAddLtAddProof : ordinaryPAeq.Proof (formula Arithmetic.PeanoMinus.Axiom.addLtAdd) := by
  let Γ := addLawsContext
  have hc := addLawsContext_closed
  have hp : ND.Proof Γ (Rewriting.emb (formula Arithmetic.PeanoMinus.Axiom.addLtAdd)) := by
    apply ND.allIntro
    apply ND.allIntro
    apply ND.allIntro
    have h := addLtAddInstance (.fvar 2) (.fvar 1) (.fvar 0)
    convert h using 1 <;> first
      | (change ND.shifted (ND.shifted (ND.shifted Γ)) = Γ;
          rw [shifted_closed Γ hc,shifted_closed Γ hc,shifted_closed Γ hc])
      | (change Semiformula.rewAux Rew.free
            (Semiformula.rewAux (Rew.q Rew.free)
              (Semiformula.rewAux (Rew.q Rew.free).q
                (Semiformula.rewAux Rew.emb.q.q.q
                  (implies (less (.bvar 2) (.bvar 1))
                    (less (add (.bvar 2) (.bvar 0)) (add (.bvar 1) (.bvar 0))))))) = _;
          simp only [rew_implies_any,less_rew,rew_add]; simp [Rew.q])
  have h := ND.parameterTheoryProof hp addLawsContext_mem_theory
  simpa only [Semiformula.univCl_coe_sentence] using h

#print axioms addLtAddInstance
#print axioms foundationAddLtAddProof
end M6.PA.Presentation
