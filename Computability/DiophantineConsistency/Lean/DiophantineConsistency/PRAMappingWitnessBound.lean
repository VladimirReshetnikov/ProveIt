import DiophantineConsistency.PRAIOpenCompleteness
import DiophantineConsistency.PRASeqDomainBound
import DiophantineConsistency.PRAMemRelWitnessBound
import DiophantineConsistency.PRANegMemRelWitnessBound
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DiophantineConsistency.PRAMappingWitnessBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.StrictSigmaOneInduction
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
attribute [local irreducible] domainDef bitDef memRel
 theorem mapping_bound (m w : V)
 (hsize : 2*m+1 ≤ w)
 (hdom : PRADomainWitnessBound.domainMajorant (2*m) m ≤ w)
 (hneg : PRANegBitFullWitnessBound.negBitMajorant (2*m) ≤ w)
 (hrel : ∀ x y, x ≤ 2*m → y ≤ m → PRAMemRelWitnessBound.memRelMajorant m x y ≤ w)
 (hrelneg : PRANegBitFullWitnessBound.negBitMajorant m ≤ w) :
 isMappingDef.val.Evalb ![m] → (bnd isMappingDef.val).Evalb ![m,w] := by
  intro h
  simp [isMappingDef,Semiformula.bexsLTSucc,Semiformula.bexsLT,FirstOrder.bexs,
    ballIn,Semiformula.ballLT,FirstOrder.ball,DeMorgan.imply,bnd,bnd_open] at h ⊢
  obtain ⟨d,hd,hdomEval,hrest⟩ := h
  have hd' : d ≤ 2*m := lt_succ_iff_le.mp hd
  have hdomsize : PRADomainWitnessBound.domainMajorant d m ≤ w :=
    le_trans (PRASeqDomainBound.domainMajorant_mono_left d (2*m) m hd') hdom
  have hb := PRADomainWitnessBound.domain_bound_explicit d m hdomEval
  letI : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  have hs : Fin.snoc ![d,m] (PRADomainWitnessBound.domainMajorant d m) = ![d,m,PRADomainWitnessBound.domainMajorant d m] := by simp
  have hm := eval_bnd_mono domainDef.val ![d,m] (Empty.elim : Empty → V) hdomsize (by rw [hs]; exact hb)
  let ω : Rew ℒₒᵣ Empty 2 Empty 2 := Rew.subst ![#0,#1]
  have hn := PRABndRewriting.natural domainDef.val ω ![d,m] w
  have hv : (fun j => (ω #j).val ![d,m] Empty.elim) = ![d,m] := by
    funext j; refine Fin.cases rfl (fun k => ?_) j; exact Fin.cases rfl (fun k => Fin.elim0 k) k
  have hs' : Fin.snoc ![d,m] w = ![d,m,w] := by simp
  rw [hv,hs'] at hn
  rw [hs'] at hm
  refine ⟨d,lt_of_lt_of_le hd hsize,hd,hn.mpr hm,?_⟩
  intro x
  by_cases hxd : d ≤ x
  · exact Or.inl hxd
  · have hxm : x < d := lt_of_not_ge hxd
    rcases hrest x with hx | hx | hx
    · exact (hxd hx).elim
    · right; left
      have hx' : (∼bitDef.val).Evalb ![x,d] := by simpa [Semiformula.Operator.val,operator_mem_def] using hx
      have hdneg : PRANegBitFullWitnessBound.negBitMajorant d ≤ w :=
        le_trans (PRASeqDomainBound.negBitMajorant_mono d (2*m) hd') hneg
      exact PRADomainWitnessBound.neg_bit_inside_bound x d m w hdneg hx'
    · right; right
      obtain ⟨y,hy,hxy,huniq⟩ := hx
      have hm2 : m ≤ 2*m+1 := by simp [two_mul,add_assoc]
      have hmw : m ≤ w := le_trans hm2 hsize
      refine ⟨y,lt_of_lt_of_le hy hmw,hy,?_,?_⟩
      · have hr : memRel.val.Evalb ![m,x,y] := by simpa [Semiformula.Operator.val,memRelOpr] using hxy
        have hrb := PRAMemRelWitnessBound.memRel_bound_explicit m x y hr
        have hrs : PRAMemRelWitnessBound.memRelMajorant m x y ≤ w := hrel x y (le_trans (le_of_lt hxm) hd') (le_of_lt hy)
        have hsc : Fin.snoc ![m,x,y] (PRAMemRelWitnessBound.memRelMajorant m x y) = ![m,x,y,PRAMemRelWitnessBound.memRelMajorant m x y] := by simp
        have hrm := eval_bnd_mono memRel.val ![m,x,y] (Empty.elim : Empty → V) hrs (by rw [hsc]; exact hrb)
        let ωr : Rew ℒₒᵣ Empty 3 Empty 4 := Rew.subst ![#3,#1,#0]
        have hrn := PRABndRewriting.natural memRel.val ωr ![y,x,d,m] w
        have hrv : (fun j => (ωr #j).val ![y,x,d,m] Empty.elim) = ![m,x,y] := by
          funext j; refine Fin.cases rfl (fun k => ?_) j; refine Fin.cases rfl (fun k => ?_) k
          exact Fin.cases rfl (fun k => Fin.elim0 k) k
        have hrw : Fin.snoc ![y,x,d,m] w = ![y,x,d,m,w] := by simp
        have hrw' : Fin.snoc ![m,x,y] w = ![m,x,y,w] := by simp
        rw [hrv,hrw,hrw'] at hrn
        rw [hrw'] at hrm
        simpa [Semiformula.Operator.operator,memRelOpr,Rewriting.emb] using hrn.mpr hrm
      · intro y'
        rcases huniq y' with hy' | hy' | hy'
        · exact Or.inl hy'
        · right; left
          have hr : (∼memRel.val).Evalb ![m,x,y'] := by simpa [Semiformula.Operator.val,memRelOpr] using hy'
          have hrb := PRANegMemRelWitnessBound.neg_memRel_bound m x y' w hrelneg hr
          let ωr : Rew ℒₒᵣ Empty 3 Empty 5 := Rew.subst ![#4,#2,#0]
          have hrn := PRABndRewriting.natural (∼memRel.val) ωr ![y',y,x,d,m] w
          have hrv : (fun j => (ωr #j).val ![y',y,x,d,m] Empty.elim) = ![m,x,y'] := by
            funext j; refine Fin.cases rfl (fun k => ?_) j; refine Fin.cases rfl (fun k => ?_) k
            exact Fin.cases rfl (fun k => Fin.elim0 k) k
          have hrw : Fin.snoc ![y',y,x,d,m] w = ![y',y,x,d,m,w] := by simp
          have hrw' : Fin.snoc ![m,x,y'] w = ![m,x,y',w] := by simp
          rw [hrv,hrw,hrw'] at hrn
          have hrb' := hrn.mpr hrb
          have hre : (ωr ▹ (∼memRel.val)) = ∼(ωr ▹ memRel.val) := by
            exact LogicalConnective.HomClass.map_neg (Semiformula.rew ωr) memRel.val
          rw [hre] at hrb'
          simpa [Semiformula.Operator.operator,memRelOpr,Rewriting.emb] using hrb'
        · exact Or.inr (Or.inr hy')
def relationFamilyMajorant (m : V) : V := (2*m+m+1)^2+1 + PRABitFullWitnessBound.bitMajorant m
def mappingMajorant (m : V) : V := (2*m+1) + PRADomainWitnessBound.domainMajorant (2*m) m +
 PRANegBitFullWitnessBound.negBitMajorant (2*m) + relationFamilyMajorant m

theorem relationFamily_bound (m x y : V) (hx : x ≤ 2*m) (hy : y ≤ m) :
 PRAMemRelWitnessBound.memRelMajorant m x y ≤ relationFamilyMajorant m := by
  letI : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  have hadd : x+y+1 ≤ 2*m+m+1 := by
    have h := add_le_add hx hy
    simpa [add_comm] using add_le_add_right h 1
  have hp := pow_le_pow_left₀ (zero_le : 0 ≤ x+y+1) hadd 2
  unfold PRAMemRelWitnessBound.memRelMajorant relationFamilyMajorant
  exact add_le_add (add_le_add hp le_rfl) le_rfl

theorem mapping_bound_explicit (m : V) : isMappingDef.val.Evalb ![m] →
 (bnd isMappingDef.val).Evalb ![m,mappingMajorant m] := by
  letI : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  let A := 2*m+1
  let B := PRADomainWitnessBound.domainMajorant (2*m) m
  let C := PRANegBitFullWitnessBound.negBitMajorant (2*m)
  let D := relationFamilyMajorant m
  have hA : A ≤ mappingMajorant m := by
    simp [mappingMajorant,A,add_assoc]
  have hB : B ≤ mappingMajorant m := by
    simpa [mappingMajorant,A,B,C,D,add_assoc,add_comm,add_left_comm] using
      (le_add_of_nonneg_right (a := B) (b := A+C+D) (zero_le : 0 ≤ A+C+D))
  have hC : C ≤ mappingMajorant m := by
    simpa [mappingMajorant,A,B,C,D,add_assoc,add_comm,add_left_comm] using
      (le_add_of_nonneg_right (a := C) (b := A+B+D) (zero_le : 0 ≤ A+B+D))
  have hD : D ≤ mappingMajorant m := by
    simpa [mappingMajorant,A,B,C,D,add_assoc,add_comm,add_left_comm] using
      (le_add_of_nonneg_right (a := D) (b := A+B+C) (zero_le : 0 ≤ A+B+C))
  apply mapping_bound m (mappingMajorant m) hA hB hC
  · intro x y hx hy
    exact le_trans (relationFamily_bound m x y hx hy) hD
  · have hm : m ≤ 2*m := by simp [two_mul]
    exact le_trans (PRASeqDomainBound.negBitMajorant_mono m (2*m) hm) hC
noncomputable def boundedMapping : ArithmeticSemisentence 2 := bnd isMappingDef.val
noncomputable def mappingBoundBody : ArithmeticSemisentence 1 :=
  “m. !isMappingDef m → !boundedMapping m
    ((2*m+1) +
      (m + ((((2*m)⁴+1)+((2*m)²+1)+(2*(2*m)²+1)+((2*m)⁴+(2*m)⁴+2*(2*m)+1))+(2*m)+1) +
       (((2*(2*m)+1)+(2*(2*m)²+1))+(2*m)+1) +
       (((m⁴+1)+(m²+1)+(2*m²+1)+(m⁴+m⁴+2*m+1))+m+1) + (((2*m+1)+(2*m²+1))+m+1)) +
      (((2*(2*m)+1)+(2*(2*m)²+1))+(2*m)+1) +
      ((2*m+m+1)²+1 + (((m⁴+1)+(m²+1)+(2*m²+1)+(m⁴+m⁴+2*m+1))+m+1)))”
theorem mappingBoundBody_model (e : Fin 1 → V) : mappingBoundBody.Eval e Empty.elim := by
  simp [mappingBoundBody,boundedMapping,Semiformula.eval_substs]
  have he : ![e 0] = e := by
    funext j; exact Fin.cases rfl (fun k => Fin.elim0 k) j
  rw [←he]
  exact mapping_bound_explicit (e 0)
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
noncomputable def mappingBoundSentence : Sentence language := ∀⁰* Semiformula.lMap embedding mappingBoundBody
theorem candidate_proves_mapping_bound : PRA ⊢ mappingBoundSentence := by
  apply PRAIOpenCompleteness.proves_allClosure
  intro M _ _ e
  exact mappingBoundBody_model e
end DiophantineConsistency.PRAMappingWitnessBound
