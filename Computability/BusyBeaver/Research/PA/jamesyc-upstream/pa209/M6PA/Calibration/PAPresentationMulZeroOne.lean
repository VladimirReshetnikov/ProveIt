module
public import M6PA.Theory
public import M6PA.Calibration.PAPresentationAddComm
@[expose] public section

/-! Fixed images four and five: x*0=0 and x*1=x, each derived by explicit
first-argument successor induction, not assumed as target defining axioms. -/
namespace M6.PA.Presentation
open FFL FFL.FirstOrder

def mulZeroProperty : Semiproposition language 1 := eq (mul (.bvar 0) zero) zero
def mulZeroContext : List ND.Form :=
  equalityContext ++ [mulZero,mulSucc,addZero,inductionFormula mulZeroProperty]

def mulZeroCertificate : ND.Proof mulZeroContext (.all mulZeroProperty) := by
  let Γ := mulZeroContext
  let E := equalityContextPremises.weaken (Δ := Γ) (by intro q hq; simp [Γ,mulZeroContext,hq])
  have mz : ND.Proof Γ mulZero := ND.assumption (by simp [Γ,mulZeroContext])
  have mr : ND.Proof Γ mulSucc := ND.assumption (by simp [Γ,mulZeroContext])
  have az : ND.Proof Γ addZero := ND.assumption (by simp [Γ,mulZeroContext])
  have ind : ND.Proof Γ (inductionFormula mulZeroProperty) := ND.assumption (by simp [Γ,mulZeroContext])
  have base : ND.Proof Γ (Semiformula.rewAux (Rew.subst ![zero]) mulZeroProperty) := by
    have h := ND.allElim _ zero mz
    convert h using 1 <;> dsimp [mulZero,mulZeroProperty] <;> equalityInstanceSyntax
  have step : ND.Proof Γ (.all (implies mulZeroProperty
      (Semiformula.rewAux (Rew.subst ![succ (.bvar 0)]) mulZeroProperty))) := by
    apply ND.allIntro
    let x : GroundTerm := .fvar 0
    let ES := E.shifted
    have mr' := ND.shiftClosed mr (by
      simp [mulSucc,eq,add,mul,succ,Semiformula.freeVariables,Semiterm.freeVariables,Fin.univ_succ])
    have az' := ND.shiftClosed az (by
      simp [addZero,eq,add,zero,Semiformula.freeVariables,Semiterm.freeVariables,Fin.univ_succ])
    have h1 : ND.Proof (ND.shifted Γ) (eq (mul (succ x) zero) (add zero (mul x zero))) := by
      have h := ND.allElim2 _ zero x mr'
      convert h using 1 <;> dsimp [mulSucc,x] <;> equalityInstanceSyntax
    have h2 : ND.Proof (ND.shifted Γ) (eq (add zero (mul x zero)) (mul x zero)) := by
      have h := ND.allElim _ (mul x zero) az'
      convert h using 1 <;> dsimp [addZero,x] <;> equalityInstanceSyntax
    have hs : ND.Proof (ND.shifted Γ) (implies (eq (mul x zero) zero) (eq (mul (succ x) zero) zero)) := by
      apply ND.impIntro
      have up : ∀ q, q ∈ ND.shifted Γ → q ∈ eq (mul x zero) zero :: ND.shifted Γ :=
        fun q hq => List.mem_cons_of_mem _ hq
      exact (ES.weaken up).transitivityOf (ND.weaken (ES.transitivityOf h1 h2) up)
        (ND.assumption (by simp))
    convert hs using 1 <;> dsimp [mulZeroProperty,x] <;> equalityInstanceSyntax
  exact ND.mp step (ND.mp base ind)

theorem mulZeroContext_is_PAeq (q : ND.Form) (hq : q ∈ mulZeroContext) : PAeqAxiom q := by
  simp only [mulZeroContext,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with hq | rfl | rfl | rfl | rfl
  · exact equalityContext_is_PAeq q hq
  · exact .fixed _ (by simp [fixedAxioms])
  · exact .fixed _ (by simp [fixedAxioms])
  · exact .fixed _ (by simp [fixedAxioms])
  · exact .induction mulZeroProperty

def foundationMulZeroProof : ordinaryPAeq.Proof (formula Arithmetic.PeanoMinus.Axiom.mulZero) := by
  have h := ND.parameterTheoryProof mulZeroCertificate (T := ordinaryPAeq)
    (fun q hq => ⟨q,mulZeroContext_is_PAeq q hq,rfl⟩)
  have he : formula Arithmetic.PeanoMinus.Axiom.mulZero = (Semiformula.all mulZeroProperty).univCl := by
    apply (Semiformula.coe_inj _ _).mp
    rw [Semiformula.coe_univCl_eq_univCl']
    rw [Semiformula.univCl'_eq_self_of _ (by
      simp [mulZeroProperty,eq,mul,zero,Semiformula.freeVariables,Semiterm.freeVariables,Fin.univ_succ])]
    change Semiformula.rewAux Rew.emb (formula Arithmetic.PeanoMinus.Axiom.mulZero) = _
    rw [←formula_emb]
    apply congrArg (@Semiformula.all language Nat 0)
    apply congrArg (Semiformula.rel (L := language) (ξ := Nat) (n := 1) Rel.eq)
    funext i; fin_cases i <;> rfl
  rw [he]
  exact h

def mulOneProperty : Semiproposition language 1 := eq (mul (.bvar 0) (succ zero)) (.bvar 0)
def mulOneContext : List ND.Form :=
  equalityContext ++ [mulZero,mulSucc,addZero,addSucc,inductionFormula mulOneProperty]

def mulOneCertificate : ND.Proof mulOneContext (.all mulOneProperty) := by
  let Γ := mulOneContext
  let E := equalityContextPremises.weaken (Δ := Γ) (by intro q hq; simp [Γ,mulOneContext,hq])
  have mz : ND.Proof Γ mulZero := ND.assumption (by simp [Γ,mulOneContext])
  have mr : ND.Proof Γ mulSucc := ND.assumption (by simp [Γ,mulOneContext])
  have az : ND.Proof Γ addZero := ND.assumption (by simp [Γ,mulOneContext])
  have ar : ND.Proof Γ addSucc := ND.assumption (by simp [Γ,mulOneContext])
  have ind : ND.Proof Γ (inductionFormula mulOneProperty) := ND.assumption (by simp [Γ,mulOneContext])
  have base : ND.Proof Γ (Semiformula.rewAux (Rew.subst ![zero]) mulOneProperty) := by
    have h := ND.allElim _ (succ zero) mz
    convert h using 1 <;> dsimp [mulZero,mulOneProperty] <;> equalityInstanceSyntax
  have step : ND.Proof Γ (.all (implies mulOneProperty
      (Semiformula.rewAux (Rew.subst ![succ (.bvar 0)]) mulOneProperty))) := by
    apply ND.allIntro
    let x : GroundTerm := .fvar 0
    let one : GroundTerm := succ zero
    let ES := E.shifted
    have mr' := ND.shiftClosed mr (by
      simp [mulSucc,eq,add,mul,succ,Semiformula.freeVariables,Semiterm.freeVariables,Fin.univ_succ])
    have az' := ND.shiftClosed az (by
      simp [addZero,eq,add,zero,Semiformula.freeVariables,Semiterm.freeVariables,Fin.univ_succ])
    have ar' := ND.shiftClosed ar (by
      simp [addSucc,eq,add,succ,Semiformula.freeVariables,Semiterm.freeVariables,Fin.univ_succ])
    have h1 : ND.Proof (ND.shifted Γ) (eq (mul (succ x) one) (add one (mul x one))) := by
      have h := ND.allElim2 _ one x mr'
      convert h using 1 <;> dsimp [mulSucc,x,one] <;> equalityInstanceSyntax
    have h2 : ND.Proof (ND.shifted Γ) (eq (add one (mul x one)) (succ (add zero (mul x one)))) := by
      have h := ND.allElim2 _ zero (mul x one) ar'
      convert h using 1 <;> dsimp [addSucc,x,one] <;> equalityInstanceSyntax
    have hz : ND.Proof (ND.shifted Γ) (eq (add zero (mul x one)) (mul x one)) := by
      have h := ND.allElim _ (mul x one) az'
      convert h using 1 <;> dsimp [addZero,x,one] <;> equalityInstanceSyntax
    have h3 := ND.mp hz (ES.successor (add zero (mul x one)) (mul x one))
    have hs : ND.Proof (ND.shifted Γ)
        (implies (eq (mul x one) x) (eq (mul (succ x) one) (succ x))) := by
      apply ND.impIntro
      have up : ∀ q, q ∈ ND.shifted Γ → q ∈ eq (mul x one) x :: ND.shifted Γ :=
        fun q hq => List.mem_cons_of_mem _ hq
      let E' := ES.weaken up
      have hi : ND.Proof (eq (mul x one) x :: ND.shifted Γ) (eq (mul x one) x) := ND.assumption (by simp)
      exact E'.transitivityOf (ND.weaken (ES.transitivityOf (ES.transitivityOf h1 h2) h3) up)
        (ND.mp hi (E'.successor (mul x one) x))
    convert hs using 1 <;> dsimp [mulOneProperty,x,one] <;> equalityInstanceSyntax
  exact ND.mp step (ND.mp base ind)

theorem mulOneContext_is_PAeq (q : ND.Form) (hq : q ∈ mulOneContext) : PAeqAxiom q := by
  simp only [mulOneContext,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with hq | rfl | rfl | rfl | rfl | rfl
  · exact equalityContext_is_PAeq q hq
  · exact .fixed _ (by simp [fixedAxioms])
  · exact .fixed _ (by simp [fixedAxioms])
  · exact .fixed _ (by simp [fixedAxioms])
  · exact .fixed _ (by simp [fixedAxioms])
  · exact .induction mulOneProperty

def foundationMulOneProof : ordinaryPAeq.Proof (formula Arithmetic.PeanoMinus.Axiom.mulOne) := by
  have h := ND.parameterTheoryProof mulOneCertificate (T := ordinaryPAeq)
    (fun q hq => ⟨q,mulOneContext_is_PAeq q hq,rfl⟩)
  have he : formula Arithmetic.PeanoMinus.Axiom.mulOne = (Semiformula.all mulOneProperty).univCl := by
    apply (Semiformula.coe_inj _ _).mp
    rw [Semiformula.coe_univCl_eq_univCl']
    rw [Semiformula.univCl'_eq_self_of _ (by
      simp [mulOneProperty,eq,mul,succ,zero,Semiformula.freeVariables,Semiterm.freeVariables,Fin.univ_succ])]
    change Semiformula.rewAux Rew.emb (formula Arithmetic.PeanoMinus.Axiom.mulOne) = _
    rw [←formula_emb]
    apply congrArg (@Semiformula.all language Nat 0)
    apply congrArg (Semiformula.rel (L := language) (ξ := Nat) (n := 1) Rel.eq)
    funext i; fin_cases i <;> rfl
  rw [he]
  exact h

#print axioms foundationMulZeroProof
#print axioms foundationMulOneProof
end M6.PA.Presentation
