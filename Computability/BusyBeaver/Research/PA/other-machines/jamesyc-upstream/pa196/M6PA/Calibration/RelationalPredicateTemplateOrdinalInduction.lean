module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateTemplateOrdinalBadTrace
public import M6PA.Calibration.RelationalPredicateTemplateLiftAxiomShift
@[expose] public section
namespace M6.PA.RelationalPredicateTemplate.Ordinal
open FFL FFL.FirstOrder ND
def separationShift {Γ : List Form} (p : Formula 1)
    (h : ND.Proof Γ (separationFormula p)) :
    ND.Proof (shifted Γ) (separationFormula p.shift) := by
  convert shiftProof h using 1
  templateTraceSyntax
  have he : (Rew.shift : Rew sourceLanguage Nat 0 Nat 0).q.q.q.comp
      (Rew.map (fun _ : Fin 1 => (0 : Fin 3)) id) =
      (Rew.map (fun _ : Fin 1 => (0 : Fin 3)) id).comp Rew.shift := by
    ext i <;> simp [Rew.comp_app]
  rw [he]
  finishTemplateSyntax

def inductionAt {Γ : List Form} (e : EqualityProofs Γ) (p : Formula 1) (a : Nat)
    (et : ND.Proof Γ (liftFormula RelationalSource.transitivityFormula)) (hi : ND.Proof Γ (liftFormula RelationalSource.Ordinal.intersectionFormula))
    (hadj : ND.Proof Γ (liftFormula RelationalSource.adjunctionFormula))
    (hsep : ND.Proof Γ (separationFormula (∼p)))
    (hbase : ND.Proof Γ (inductionBase p)) (hstep : ND.Proof Γ (inductionStep p))
    (ha : ND.Proof Γ (domain (.fvar a))) : ND.Proof Γ (p/[.fvar a]) := by
  apply byContradiction
  let bad : Form := ∼(p/[.fvar a])
  let D := bad :: Γ
  have hn : ND.Proof D bad := assumption (by simp [D])
  apply exsElim (rawSuccessor (.fvar a) (up hadj bad))
  let σ : Formula 1 := successor (Rew.bShift (.fvar a)) (.bvar 0)
  let C := σ.free :: shifted D
  have ds : ND.Proof C (successor (.fvar (a+1)) (.fvar 0)) := by
    have h : ND.Proof C σ.free := assumption (by simp [C])
    convert h using 1 ; dsimp [σ] ; templateSuccessorSyntax
  have da := up (domainShift a (up ha bad)) σ.free
  have es := (e.up bad).shift.up σ.free
  have db := successorDomain es (.fvar (a+1)) (.fvar 0) (up (equalityTransShift (up et bad)) σ.free)
    (up (intersectionAxiomShift (up hi bad)) σ.free) da ds
  have point := mp (ND.orRight (eqRefl es (a+1))) (andRight (successorAt (a+1) 0 (a+1) ds))
  have dn : ND.Proof C (∼(p.shift/[.fvar (a+1)])) := by
    have h := up (shiftProof hn) σ.free
    have he : (∼(p/[(.fvar a : Term 0)])).shift = ∼(p/[.fvar a]).shift := by simp
    change ND.Proof C ((∼(p/[.fvar a])).shift) at h
    rw [he,predicateInstanceShift] at h
    exact h
  have dsep : ND.Proof C (separationFormula (∼p.shift)) := by
    simpa [C,D] using up (separationShift (∼p) (up hsep bad)) σ.free
  exact badInsideOrdinalContradiction es p.shift 0 (a+1) db point dn dsep
    (up (inductionBaseShift p (up hbase bad)) σ.free)
    (up (inductionStepShift p (up hstep bad)) σ.free)

/-- Arbitrary nested quantifiers and every Nat free parameter are retained. -/
def uniformInduction {Γ : List Form} (e : EqualityProofs Γ) (p : Formula 1)
    (et : ND.Proof Γ (liftFormula RelationalSource.transitivityFormula)) (hi : ND.Proof Γ (liftFormula RelationalSource.Ordinal.intersectionFormula))
    (hadj : ND.Proof Γ (liftFormula RelationalSource.adjunctionFormula))
    (hsep : ND.Proof Γ (separationFormula (∼p)))
    (hbase : ND.Proof Γ (inductionBase p)) (hstep : ND.Proof Γ (inductionStep p)) :
    ND.Proof Γ (inductionConclusion p) := by
  apply allIntro
  let d : Form := domain (.fvar 0)
  have hd : ND.Proof (d :: shifted Γ) d := assumption (by simp)
  have sep : ND.Proof (d :: shifted Γ) (separationFormula (∼p.shift)) := by
    simpa using up (separationShift (∼p) hsep) d
  have h := impIntro (inductionAt (e.shift.up d) p.shift 0
    (up (equalityTransShift et) d) (up (intersectionAxiomShift hi) d)
    (up (inductionAdjunctionShift hadj) d) sep
    (up (inductionBaseShift p hbase) d) (up (inductionStepShift p hstep) d) hd)
  rw [LawfulSyntacticRewriting.app_subst_fbar_zero_comp_shift_eq_free] at h
  convert h using 1
  dsimp [d]
  templateOrdinalSyntax

#print axioms separationShift
#print axioms inductionAt
#print axioms uniformInduction
end M6.PA.RelationalPredicateTemplate.Ordinal
