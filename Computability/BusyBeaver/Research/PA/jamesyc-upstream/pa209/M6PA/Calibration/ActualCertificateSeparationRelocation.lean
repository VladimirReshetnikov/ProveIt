module
public import M6PA.Theory
public import M6PA.Calibration.ActualCertificateSeparationRaw
public import M6PA.Calibration.FoundationRelationalSequentConditional
@[expose] public section

/-! Finite raw-separation output alpha conversion. Actual property-vacuity
certificates at both output labels are explicit premises. -/
namespace M6.PA.ActualCertificateEquivalence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualCertificateConstructors ActualCertificateConstructors.Dominated
open RelationalSource.Numeric
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

noncomputable def separationBody (a b c p : V) : V :=
  wal b (wa (wim (wel c b) (wa (wel a b) p)) (wim (wa (wel a b) p) (wel c b)))

noncomputable def separationBodyVacuity (a b c p x : V)
    (hxa : x≠a) (hxb : x≠b) (hxc : x≠c)
    (hp : Certificate (wim p (wal x p))) :
    Certificate (wim (separationBody a b c p) (wal x (separationBody a b c p))) := by
  let hm := membershipVacuity c b x hxc hxb
  let ht := conjunctionVacuity x (wel a b) p (membershipVacuity a b x hxa hxb) hp
  exact universalVacuity x b _ (conjunctionVacuity x _ _
    (implicationVacuity x _ _ hm ht) (implicationVacuity x _ _ ht hm))

noncomputable def separationOutputAlpha (a b q c z p : V)
    (hzq : z≠q) (hzc : z≠c) (hzb : z≠b)
    (hqa : q≠a) (hqb : q≠b) (hca : c≠a) (hcb : c≠b) (hqc : q≠c)
    (hpq : Certificate (wim p (wal q p))) (hpc : Certificate (wim p (wal c p))) :
    BiWitness (separationValue a b q p) (separationValue a b c p) := by
  let e := ActualArithmeticGraph.eval neighborhoodExpr q c z 0
  let hm : ConditionalBiWitness e (wel q b) (wel c b) :=
    ⟨neighborhoodRightCongruence q c z b hzq hzc hzb,
      implicationCompose (neighborhoodSymmetry q c z)
        (neighborhoodRightCongruence c q z b hzc hzq hzb)⟩
  let ht := ConditionalBiWitness.refl e (wa (wel a b) p)
  let hclause := ((hm.imp ht).imp (ht.imp hm).neg).neg
  let heVac : Certificate (wim e (wal b e)) :=
    neighborhoodEqualityVacuity q c z b (Ne.symm hqb) (Ne.symm hcb) (Ne.symm hzb)
  let bodies : ConditionalBiWitness e (separationBody a b q p) (separationBody a b c p) :=
    hclause.all b heVac
  let targetVac := separationBodyVacuity a b c p q hqa hqb hqc hpq
  let sourceVac := separationBodyVacuity a b q p c hca hcb (Ne.symm hqc) hpc
  let alpha := universalAlphaNeighborhood q c z
    (wn (separationBody a b q p)) (wn (separationBody a b c p)) hzq hzc
    bodies.neg.forward bodies.neg.backward
    (negationVacuity q _ targetVac) (negationVacuity c _ sourceVac)
  let h : BiWitness (wal q (wn (separationBody a b q p)))
    (wal c (wn (separationBody a b c p))) := ⟨alpha.1,alpha.2⟩
  exact h.neg

#print axioms separationBodyVacuity
#print axioms separationOutputAlpha
end M6.PA.ActualCertificateEquivalence

