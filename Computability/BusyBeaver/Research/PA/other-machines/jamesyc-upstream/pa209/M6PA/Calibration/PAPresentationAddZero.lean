module
public import M6PA.Theory
public import M6PA.Calibration.PAPresentationSentences
@[expose] public section

/-! First fixed PA-minus image: x+0=x. The target's defining recursion is
on the FIRST argument, so this right-zero equation is proved by induction. -/
namespace M6.PA.Presentation
open FFL FFL.FirstOrder

def rightZeroProperty : Semiproposition language 1 := eq (add (.bvar 0) zero) (.bvar 0)
def rightZeroContext : List ND.Form :=
  equalityContext ++ [addZero,addSucc,inductionFormula rightZeroProperty]

def rightZeroCertificate : ND.Proof rightZeroContext (.all rightZeroProperty) := by
  let Γ := rightZeroContext
  let E := equalityContextPremises.weaken (Δ := Γ) (by intro q hq; simp [Γ,rightZeroContext,hq])
  have az : ND.Proof Γ addZero := ND.assumption (by simp [Γ,rightZeroContext])
  have ar : ND.Proof Γ addSucc := ND.assumption (by simp [Γ,rightZeroContext])
  have ind : ND.Proof Γ (inductionFormula rightZeroProperty) :=
    ND.assumption (by simp [Γ,rightZeroContext])
  have base : ND.Proof Γ (Semiformula.rewAux (Rew.subst ![zero]) rightZeroProperty) := by
    have h := ND.allElim _ zero az
    convert h using 1 <;> dsimp [addZero,rightZeroProperty] <;> equalityInstanceSyntax
  have step : ND.Proof Γ (.all (implies rightZeroProperty
      (Semiformula.rewAux (Rew.subst ![succ (.bvar 0)]) rightZeroProperty))) := by
    apply ND.allIntro
    let x : GroundTerm := .fvar 0
    have ar' := ND.shiftClosed ar (by
      simp [addSucc,eq,add,succ,Semiformula.freeVariables,Semiterm.freeVariables,Fin.univ_succ])
    have hr : ND.Proof (ND.shifted Γ) (eq (add (succ x) zero) (succ (add x zero))) := by
      have h := ND.allElim2 _ x zero ar'
      convert h using 1 <;> dsimp [addSucc,x] <;> equalityInstanceSyntax
    have hs : ND.Proof (ND.shifted Γ)
        (implies (eq (add x zero) x) (eq (add (succ x) zero) (succ x))) := by
      apply ND.impIntro
      have up : ∀ q, q ∈ ND.shifted Γ → q ∈ eq (add x zero) x :: ND.shifted Γ :=
        fun q hq => List.mem_cons_of_mem _ hq
      let E' := E.shifted.weaken up
      have hi : ND.Proof (eq (add x zero) x :: ND.shifted Γ) (eq (add x zero) x) :=
        ND.assumption (by simp)
      exact E'.transitivityOf (ND.weaken hr up)
        (ND.mp hi (E'.successor (add x zero) x))
    convert hs using 1 <;> dsimp [rightZeroProperty,x] <;> equalityInstanceSyntax
  exact ND.mp step (ND.mp base ind)

theorem rightZeroContext_is_PAeq (q : ND.Form) (hq : q ∈ rightZeroContext) : PAeqAxiom q := by
  simp only [rightZeroContext,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with hq | rfl | rfl | rfl
  · exact equalityContext_is_PAeq q hq
  · exact .fixed _ (by simp [fixedAxioms])
  · exact .fixed _ (by simp [fixedAxioms])
  · exact .induction rightZeroProperty

def rightZeroProof : ordinaryPAeq.Proof (Semiformula.all rightZeroProperty).univCl :=
  ND.parameterTheoryProof rightZeroCertificate (fun q hq => ⟨q,rightZeroContext_is_PAeq q hq,rfl⟩)

theorem addZero_image : formula Arithmetic.PeanoMinus.Axiom.addZero =
    (Semiformula.all rightZeroProperty).univCl := by
  apply (Semiformula.coe_inj _ _).mp
  rw [Semiformula.coe_univCl_eq_univCl']
  rw [Semiformula.univCl'_eq_self_of _ (by
    simp [rightZeroProperty,eq,add,zero,Semiformula.freeVariables,Semiterm.freeVariables,Fin.univ_succ])]
  change Semiformula.rewAux Rew.emb (formula Arithmetic.PeanoMinus.Axiom.addZero) = _
  rw [←formula_emb]
  apply congrArg (@Semiformula.all language Nat 0)
  apply congrArg (Semiformula.rel (L := language) (ξ := Nat) (n := 1) Rel.eq)
  funext i
  fin_cases i <;> rfl

def foundationAddZeroProof : ordinaryPAeq.Proof (formula Arithmetic.PeanoMinus.Axiom.addZero) := by
  rw [addZero_image]
  exact rightZeroProof

#print axioms rightZeroCertificate
#print axioms foundationAddZeroProof
end M6.PA.Presentation
