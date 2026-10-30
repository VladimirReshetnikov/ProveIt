import DiophantineConsistency.PRAIOpenCompleteness
import DiophantineConsistency.PRADomainWitnessBound
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DiophantineConsistency.PRANegDomainWitnessBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.StrictSigmaOneInduction
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
attribute [local irreducible] bitDef pairDef
 theorem neg_domain_bound (u s w : V) (hxs : u+s ≤ w) (hs : s ≤ w)
 (hposu : PRABitFullWitnessBound.bitMajorant u ≤ w)
 (hnegu : PRANegBitFullWitnessBound.negBitMajorant u ≤ w)
 (hposs : PRABitFullWitnessBound.bitMajorant s ≤ w)
 (hnegs : PRANegBitFullWitnessBound.negBitMajorant s ≤ w) :
 (∼domainDef.val).Evalb ![u,s] → (bnd (∼domainDef.val)).Evalb ![u,s,w] := by
  intro h
  simp [domainDef, Semiformula.ballLT, FirstOrder.ball, DeMorgan.imply, bnd, bnd_open] at h ⊢
  obtain ⟨x,hx,hh⟩ := h
  refine ⟨x,lt_of_lt_of_le hx hxs,hx,?_⟩
  simp [LogicalConnective.iff, DeMorgan.imply, bnd]
  have hh' : ¬(bitDef.val.Evalb ![x,u] ↔ PRADomainExistsBound.existsInside.Evalb ![x,u,s]) := by
    intro heq
    apply hh
    constructor
    · intro hmem
      have hb : bitDef.val.Evalb ![x,u] := by simpa [Semiformula.Operator.val,operator_mem_def] using hmem
      have he := heq.mp hb
      simpa [PRADomainExistsBound.existsInside,Semiformula.bexsLT,FirstOrder.bexs] using he
    · intro he
      have he' : PRADomainExistsBound.existsInside.Evalb ![x,u,s] := by
        simpa [PRADomainExistsBound.existsInside,Semiformula.bexsLT,FirstOrder.bexs] using he
      have hb := heq.mpr he'
      simpa [Semiformula.Operator.val,operator_mem_def] using hb
  by_cases hb : bitDef.val.Evalb ![x,u]
  · left
    have hno : ¬ PRADomainExistsBound.existsInside.Evalb ![x,u,s] := by
      intro he
      apply hh'
      exact ⟨fun _ => he,fun _ => hb⟩
    have he : (∼PRANegDomainExistsBound.existsInside).Evalb ![x,u,s] := by
      simpa [PRADomainExistsBound.existsInside,PRANegDomainExistsBound.existsInside] using hno
    exact ⟨PRADomainWitnessBound.bit_inside_bound x u s w hposu hb,
      PRANegDomainExistsBound.neg_exists_bound x u s w hnegs he⟩
  · right
    have he : PRADomainExistsBound.existsInside.Evalb ![x,u,s] := by
      by_contra hno
      apply hh'
      exact ⟨fun h => (hb h).elim,fun h => (hno h).elim⟩
    have hn : (∼bitDef.val).Evalb ![x,u] := by simpa using hb
    exact ⟨PRADomainExistsBound.exists_bound x u s w hs hposs he,
      PRADomainWitnessBound.neg_bit_inside_bound x u s w hnegu hn⟩
def negDomainMajorant (u s : V) : V := u+s+PRADomainWitnessBound.domainMajorant u s
theorem neg_domain_bound_explicit (u s : V) : (∼domainDef.val).Evalb ![u,s] →
 (bnd (∼domainDef.val)).Evalb ![u,s,negDomainMajorant u s] := by
  letI : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  let A := PRABitFullWitnessBound.bitMajorant u
  let B := PRANegBitFullWitnessBound.negBitMajorant u
  let C := PRABitFullWitnessBound.bitMajorant s
  let D := PRANegBitFullWitnessBound.negBitMajorant s
  have hd : PRADomainWitnessBound.domainMajorant u s ≤ negDomainMajorant u s := by
    exact le_add_of_nonneg_left (zero_le : 0 ≤ u+s)
  have hx : u+s ≤ negDomainMajorant u s := le_add_of_nonneg_right zero_le
  have hs : s ≤ PRADomainWitnessBound.domainMajorant u s := by
    simp [PRADomainWitnessBound.domainMajorant,add_assoc]
  have ha : A ≤ PRADomainWitnessBound.domainMajorant u s := by
    simpa [PRADomainWitnessBound.domainMajorant,A,B,C,D,add_assoc,add_comm,add_left_comm] using
      (le_add_of_nonneg_right (a := A) (b := s+B+C+D) (zero_le : 0 ≤ s+B+C+D))
  have hb : B ≤ PRADomainWitnessBound.domainMajorant u s := by
    simpa [PRADomainWitnessBound.domainMajorant,A,B,C,D,add_assoc,add_comm,add_left_comm] using
      (le_add_of_nonneg_right (a := B) (b := s+A+C+D) (zero_le : 0 ≤ s+A+C+D))
  have hc : C ≤ PRADomainWitnessBound.domainMajorant u s := by
    simpa [PRADomainWitnessBound.domainMajorant,A,B,C,D,add_assoc,add_comm,add_left_comm] using
      (le_add_of_nonneg_right (a := C) (b := s+A+B+D) (zero_le : 0 ≤ s+A+B+D))
  have hdd : D ≤ PRADomainWitnessBound.domainMajorant u s := by
    simpa [PRADomainWitnessBound.domainMajorant,A,B,C,D,add_assoc,add_comm,add_left_comm] using
      (le_add_of_nonneg_right (a := D) (b := s+A+B+C) (zero_le : 0 ≤ s+A+B+C))
  exact neg_domain_bound u s (negDomainMajorant u s) hx (le_trans hs hd) (le_trans ha hd)
    (le_trans hb hd) (le_trans hc hd) (le_trans hdd hd)
noncomputable def negDomain : ArithmeticSemisentence 2 := ∼domainDef.val
noncomputable def boundedNegDomain : ArithmeticSemisentence 3 := bnd negDomain
noncomputable def negDomainBoundBody : ArithmeticSemisentence 2 :=
  “u s. !negDomain u s → !boundedNegDomain u s
    (u+s + (s + (((u⁴+1)+(u²+1)+(2*u²+1)+(u⁴+u⁴+2*u+1))+u+1) +
     (((2*u+1)+(2*u²+1))+u+1) + (((s⁴+1)+(s²+1)+(2*s²+1)+(s⁴+s⁴+2*s+1))+s+1) +
     (((2*s+1)+(2*s²+1))+s+1)))”
theorem negDomainBoundBody_model (e : Fin 2 → V) : negDomainBoundBody.Eval e Empty.elim := by
  simpa [negDomainBoundBody,boundedNegDomain,negDomain,negDomainMajorant,PRADomainWitnessBound.domainMajorant,
    PRABitFullWitnessBound.bitMajorant,PRANegBitFullWitnessBound.negBitMajorant,
    PRANegExponentialWitnessBound.negExponentialMajorant,PRAExponentialWitnessBound.exponentialMajorant,
    Semiformula.eval_substs] using neg_domain_bound_explicit (e 0) (e 1)
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
noncomputable def negDomainBoundSentence : Sentence language := ∀⁰* Semiformula.lMap embedding negDomainBoundBody
theorem candidate_proves_neg_domain_bound : PRA ⊢ negDomainBoundSentence := by
  apply PRAIOpenCompleteness.proves_allClosure
  intro M _ _ e
  exact negDomainBoundBody_model e
end DiophantineConsistency.PRANegDomainWitnessBound
