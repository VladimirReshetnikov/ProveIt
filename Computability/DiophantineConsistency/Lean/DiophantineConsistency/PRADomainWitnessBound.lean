import DiophantineConsistency.PRAIOpenCompleteness
import DiophantineConsistency.PRADomainExistsBound
import DiophantineConsistency.PRANegDomainExistsBound
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DiophantineConsistency.PRADomainWitnessBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.StrictSigmaOneInduction
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
attribute [local irreducible] bitDef pairDef
private theorem bnd_rew_inside (ψ : ArithmeticSemisentence 2) (x u s w t : V)
    (ht : t ≤ w) (hb : (bnd ψ).Evalb ![x,u,t]) :
    (bnd (Rew.subst ![#0,#1] ▹ ψ)).Evalb ![x,u,s,w] := by
  letI : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  have hm := eval_bnd_mono ψ ![x,u] (Empty.elim : Empty → V) ht (by simpa using hb)
  let ω : Rew ℒₒᵣ Empty 2 Empty 3 := Rew.subst ![#0,#1]
  have hn := PRABndRewriting.natural ψ ω ![x,u,s] w
  have hv : (fun j => (ω #j).val ![x,u,s] Empty.elim) = ![x,u] := by
    funext j; refine Fin.cases rfl (fun k => ?_) j; exact Fin.cases rfl (fun k => Fin.elim0 k) k
  have hs : Fin.snoc ![x,u,s] w = ![x,u,s,w] := by simp
  have hs' : Fin.snoc ![x,u] w = ![x,u,w] := by simp
  rw [hv, hs, hs'] at hn
  rw [hs'] at hm
  exact hn.mpr hm

theorem bit_inside_bound (x u s w : V) (hw : PRABitFullWitnessBound.bitMajorant u ≤ w)
 (h : bitDef.val.Evalb ![x,u]) : (bnd “x u s. x ∈ u”).Evalb ![x,u,s,w] := by
  have hb := bnd_rew_inside bitDef.val x u s w _ hw (PRABitFullWitnessBound.bit_bound x u h)
  simpa [Semiformula.Operator.operator, operator_mem_def, Rewriting.emb] using hb

theorem neg_bit_inside_bound (x u s w : V) (hw : PRANegBitFullWitnessBound.negBitMajorant u ≤ w)
 (h : (∼bitDef.val).Evalb ![x,u]) : (bnd (∼“x u s. x ∈ u”)).Evalb ![x,u,s,w] := by
  have hb := bnd_rew_inside (∼bitDef.val) x u s w _ hw (PRANegBitFullWitnessBound.negBit_bound x u h)
  let ω : Rew ℒₒᵣ Empty 2 Empty 3 := Rew.subst ![#0,#1]
  have heq : (ω ▹ (∼bitDef.val)) = ∼(ω ▹ bitDef.val) := by
    exact LogicalConnective.HomClass.map_neg (Semiformula.rew ω) bitDef.val
  rw [heq] at hb
  simpa [Semiformula.Operator.operator, operator_mem_def, Rewriting.emb] using hb
 theorem domain_bound (u s w : V) (hs : s ≤ w)
 (hposu : PRABitFullWitnessBound.bitMajorant u ≤ w)
 (hnegu : PRANegBitFullWitnessBound.negBitMajorant u ≤ w)
 (hposs : PRABitFullWitnessBound.bitMajorant s ≤ w)
 (hnegs : PRANegBitFullWitnessBound.negBitMajorant s ≤ w) :
 domainDef.val.Evalb ![u,s] → (bnd domainDef.val).Evalb ![u,s,w] := by
  intro h
  simp [domainDef, Semiformula.ballLT, FirstOrder.ball, DeMorgan.imply, bnd, bnd_open] at h ⊢
  intro x
  rcases h x with hx | he
  · exact Or.inl hx
  · right
    by_cases hbit : bitDef.val.Evalb ![x,u]
    · constructor
      · right
        have hx : PRADomainExistsBound.existsInside.Evalb ![x,u,s] := by
          simpa [PRADomainExistsBound.existsInside, Semiformula.bexsLT, FirstOrder.bexs] using
            he.mp (by simpa [Semiformula.Operator.val, operator_mem_def] using hbit)
        have hb := PRADomainExistsBound.exists_bound x u s w hs hposs hx
        exact hb
      · right
        exact bit_inside_bound x u s w hposu hbit
    · constructor
      · left
        have hb : (∼bitDef.val).Evalb ![x,u] := by simpa using hbit
        exact neg_bit_inside_bound x u s w hnegu hb
      · left
        have hno : ¬ PRANegDomainExistsBound.existsInside.Evalb ![x,u,s] := by
          intro hex
          have hex' : ∃ y < s, (Semiformula.Eval ![y,x,u,s] Empty.elim)
              (bexsIn (#3) (↑pairDef/[#0,#2,#1])) := by
            simpa [PRANegDomainExistsBound.existsInside, Semiformula.bexsLT, FirstOrder.bexs] using hex
          apply hbit
          simpa [Semiformula.Operator.val, operator_mem_def] using he.mpr hex'
        have hx : (∼PRANegDomainExistsBound.existsInside).Evalb ![x,u,s] := by simpa using hno
        have hb := PRANegDomainExistsBound.neg_exists_bound x u s w hnegs hx
        exact hb
def domainMajorant (u s : V) : V := s + PRABitFullWitnessBound.bitMajorant u +
 PRANegBitFullWitnessBound.negBitMajorant u + PRABitFullWitnessBound.bitMajorant s +
 PRANegBitFullWitnessBound.negBitMajorant s

theorem domain_bound_explicit (u s : V) : domainDef.val.Evalb ![u,s] →
 (bnd domainDef.val).Evalb ![u,s,domainMajorant u s] := by
  letI : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  let A := PRABitFullWitnessBound.bitMajorant u
  let B := PRANegBitFullWitnessBound.negBitMajorant u
  let C := PRABitFullWitnessBound.bitMajorant s
  let D := PRANegBitFullWitnessBound.negBitMajorant s
  apply domain_bound u s (domainMajorant u s)
  · simp [domainMajorant,add_assoc]
  · simpa [domainMajorant,A,B,C,D,add_assoc,add_comm,add_left_comm] using
      (le_add_of_nonneg_right (a := A) (b := s+B+C+D) (zero_le : 0 ≤ s+B+C+D))
  · simpa [domainMajorant,A,B,C,D,add_assoc,add_comm,add_left_comm] using
      (le_add_of_nonneg_right (a := B) (b := s+A+C+D) (zero_le : 0 ≤ s+A+C+D))
  · simpa [domainMajorant,A,B,C,D,add_assoc,add_comm,add_left_comm] using
      (le_add_of_nonneg_right (a := C) (b := s+A+B+D) (zero_le : 0 ≤ s+A+B+D))
  · simpa [domainMajorant,A,B,C,D,add_assoc,add_comm,add_left_comm] using
      (le_add_of_nonneg_right (a := D) (b := s+A+B+C) (zero_le : 0 ≤ s+A+B+C))
noncomputable def boundedDomain : ArithmeticSemisentence 3 := bnd domainDef.val
noncomputable def domainBoundBody : ArithmeticSemisentence 2 :=
  “u s. !domainDef u s → !boundedDomain u s
    (s + (((u⁴+1)+(u²+1)+(2*u²+1)+(u⁴+u⁴+2*u+1))+u+1) +
     (((2*u+1)+(2*u²+1))+u+1) + (((s⁴+1)+(s²+1)+(2*s²+1)+(s⁴+s⁴+2*s+1))+s+1) +
     (((2*s+1)+(2*s²+1))+s+1))”
theorem domainBoundBody_model (e : Fin 2 → V) : domainBoundBody.Eval e Empty.elim := by
  simp [domainBoundBody,boundedDomain,Semiformula.eval_substs]
  exact domain_bound_explicit (e 0) (e 1)
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
noncomputable def domainBoundSentence : Sentence language := ∀⁰* Semiformula.lMap embedding domainBoundBody
theorem candidate_proves_domain_bound : PRA ⊢ domainBoundSentence := by
  apply PRAIOpenCompleteness.proves_allClosure
  intro M _ _ e
  exact domainBoundBody_model e
end DiophantineConsistency.PRADomainWitnessBound
