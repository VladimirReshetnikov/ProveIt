import DiophantineConsistency.PRAMappingWitnessBound
import DiophantineConsistency.PRANegDomainWitnessBound
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DiophantineConsistency.PRANegMappingWitnessBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.StrictSigmaOneInduction
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
attribute [local irreducible] domainDef bitDef memRel
 theorem neg_mapping_bound (m w : V)
 (hsize : 2*m+1 ≤ w)
 (hdom : ∀ d, d ≤ 2*m → PRANegDomainWitnessBound.negDomainMajorant d m ≤ w)
 (hpos : PRABitFullWitnessBound.bitMajorant (2*m) ≤ w)
 (hrelneg : PRANegBitFullWitnessBound.negBitMajorant m ≤ w)
 (hrel : ∀ x y, x ≤ 2*m → y ≤ m → PRAMemRelWitnessBound.memRelMajorant m x y ≤ w) :
 (∼isMappingDef.val).Evalb ![m] → (bnd (∼isMappingDef.val)).Evalb ![m,w] := by
  intro h
  simp [isMappingDef,Semiformula.bexsLTSucc,Semiformula.bexsLT,FirstOrder.bexs,
    ballIn,Semiformula.ballLT,FirstOrder.ball,DeMorgan.imply,bnd,bnd_open] at h ⊢
  intro d
  by_cases hd : 2*m+1 ≤ d
  · exact Or.inl hd
  · have hd' : d ≤ 2*m := lt_succ_iff_le.mp (lt_of_not_ge hd)
    rcases h d with hh | hh | hh
    · exact (hd hh).elim
    · right; left
      have hdom' : (∼domainDef.val).Evalb ![d,m] := by simpa using hh
      have hb := PRANegDomainWitnessBound.neg_domain_bound_explicit d m hdom'
      letI : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
      have hs : Fin.snoc ![d,m] (PRANegDomainWitnessBound.negDomainMajorant d m) = ![d,m,PRANegDomainWitnessBound.negDomainMajorant d m] := by
        funext j; refine Fin.cases rfl (fun k => ?_) j; refine Fin.cases rfl (fun k => ?_) k
        exact Fin.cases rfl (fun k => Fin.elim0 k) k
      have hm := eval_bnd_mono (∼domainDef.val) ![d,m] (Empty.elim : Empty → V) (hdom d hd') (by rw [hs]; exact hb)
      let ω : Rew ℒₒᵣ Empty 2 Empty 2 := Rew.subst ![#0,#1]
      have hn := PRABndRewriting.natural (∼domainDef.val) ω ![d,m] w
      have hv : (fun j => (ω #j).val ![d,m] Empty.elim) = ![d,m] := by
        funext j; refine Fin.cases rfl (fun k => ?_) j; exact Fin.cases rfl (fun k => Fin.elim0 k) k
      have hs' : Fin.snoc ![d,m] w = ![d,m,w] := by
        funext j; refine Fin.cases rfl (fun k => ?_) j; refine Fin.cases rfl (fun k => ?_) k
        exact Fin.cases rfl (fun k => Fin.elim0 k) k
      rw [hv,hs'] at hn
      rw [hs'] at hm
      have hh := hn.mpr hm
      have heq : (ω ▹ (∼domainDef.val)) = ∼(ω ▹ domainDef.val) := by
        exact LogicalConnective.HomClass.map_neg (Semiformula.rew ω) domainDef.val
      rw [heq] at hh
      exact hh
    · right; right
      obtain ⟨x,hx,hbit,hrest⟩ := hh
      have hx2 : x ≤ 2*m := le_trans (le_of_lt hx) hd'
      have hxw : x < w := lt_of_lt_of_le (lt_succ_iff_le.mpr hx2) hsize
      refine ⟨x,hxw,hx,?_,?_⟩
      · have hbit' : bitDef.val.Evalb ![x,d] := by simpa [Semiformula.Operator.val,operator_mem_def] using hbit
        have hpos' : PRABitFullWitnessBound.bitMajorant d ≤ w :=
          le_trans (PRASeqDomainBound.bitMajorant_mono d (2*m) hd') hpos
        exact PRADomainWitnessBound.bit_inside_bound x d m w hpos' hbit'
      · intro y
        rcases hrest y with hy | hy | hy
        · exact Or.inl hy
        · right; left
          have hr : (∼memRel.val).Evalb ![m,x,y] := by simpa [Semiformula.Operator.val,memRelOpr] using hy
          have hrb := PRANegMemRelWitnessBound.neg_memRel_bound m x y w hrelneg hr
          let ωr : Rew ℒₒᵣ Empty 3 Empty 4 := Rew.subst ![#3,#1,#0]
          have hrn := PRABndRewriting.natural (∼memRel.val) ωr ![y,x,d,m] w
          have hrv : (fun j => (ωr #j).val ![y,x,d,m] Empty.elim) = ![m,x,y] := by
            funext j; refine Fin.cases rfl (fun k => ?_) j; refine Fin.cases rfl (fun k => ?_) k
            exact Fin.cases rfl (fun k => Fin.elim0 k) k
          have hrw : Fin.snoc ![y,x,d,m] w = ![y,x,d,m,w] := by
            funext j; refine Fin.cases rfl (fun k => ?_) j; refine Fin.cases rfl (fun k => ?_) k
            refine Fin.cases rfl (fun k => ?_) k; refine Fin.cases rfl (fun k => ?_) k
            exact Fin.cases rfl (fun k => Fin.elim0 k) k
          have hrw' : Fin.snoc ![m,x,y] w = ![m,x,y,w] := by
            funext j; refine Fin.cases rfl (fun k => ?_) j; refine Fin.cases rfl (fun k => ?_) k
            refine Fin.cases rfl (fun k => ?_) k; exact Fin.cases rfl (fun k => Fin.elim0 k) k
          rw [hrv,hrw,hrw'] at hrn
          have hrb' := hrn.mpr hrb
          have hre : (ωr ▹ (∼memRel.val)) = ∼(ωr ▹ memRel.val) := by
            exact LogicalConnective.HomClass.map_neg (Semiformula.rew ωr) memRel.val
          rw [hre] at hrb'
          simpa [Semiformula.Operator.operator,memRelOpr,Rewriting.emb] using hrb'
        · right; right
          obtain ⟨y',hy',hrel',hne⟩ := hy
          have hm2 : m ≤ 2*m+1 := by simp [two_mul,add_assoc]
          have hmw : m ≤ w := le_trans hm2 hsize
          refine ⟨y',lt_of_lt_of_le hy' hmw,hy',?_,hne⟩
          have hr : memRel.val.Evalb ![m,x,y'] := by simpa [Semiformula.Operator.val,memRelOpr] using hrel'
          have hrb := PRAMemRelWitnessBound.memRel_bound_explicit m x y' hr
          have hrs : PRAMemRelWitnessBound.memRelMajorant m x y' ≤ w := hrel x y' hx2 (le_of_lt hy')
          letI : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
          have hsc : Fin.snoc ![m,x,y'] (PRAMemRelWitnessBound.memRelMajorant m x y') = ![m,x,y',PRAMemRelWitnessBound.memRelMajorant m x y'] := by
            funext j; refine Fin.cases rfl (fun k => ?_) j; refine Fin.cases rfl (fun k => ?_) k
            refine Fin.cases rfl (fun k => ?_) k; exact Fin.cases rfl (fun k => Fin.elim0 k) k
          have hrm := eval_bnd_mono memRel.val ![m,x,y'] (Empty.elim : Empty → V) hrs (by rw [hsc]; exact hrb)
          let ωr : Rew ℒₒᵣ Empty 3 Empty 5 := Rew.subst ![#4,#2,#0]
          have hrn := PRABndRewriting.natural memRel.val ωr ![y',y,x,d,m] w
          have hrv : (fun j => (ωr #j).val ![y',y,x,d,m] Empty.elim) = ![m,x,y'] := by
            funext j; refine Fin.cases rfl (fun k => ?_) j; refine Fin.cases rfl (fun k => ?_) k
            exact Fin.cases rfl (fun k => Fin.elim0 k) k
          have hrw : Fin.snoc ![y',y,x,d,m] w = ![y',y,x,d,m,w] := by
            funext j; refine Fin.cases rfl (fun k => ?_) j; refine Fin.cases rfl (fun k => ?_) k
            refine Fin.cases rfl (fun k => ?_) k; refine Fin.cases rfl (fun k => ?_) k
            refine Fin.cases rfl (fun k => ?_) k; exact Fin.cases rfl (fun k => Fin.elim0 k) k
          have hrw' : Fin.snoc ![m,x,y'] w = ![m,x,y',w] := by
            funext j; refine Fin.cases rfl (fun k => ?_) j; refine Fin.cases rfl (fun k => ?_) k
            refine Fin.cases rfl (fun k => ?_) k; exact Fin.cases rfl (fun k => Fin.elim0 k) k
          rw [hrv,hrw,hrw'] at hrn
          rw [hrw'] at hrm
          simpa [Semiformula.Operator.operator,memRelOpr,Rewriting.emb] using hrn.mpr hrm
def negMappingMajorant (m : V) : V := (2*m+1) + PRANegDomainWitnessBound.negDomainMajorant (2*m) m +
 PRABitFullWitnessBound.bitMajorant (2*m) + PRANegBitFullWitnessBound.negBitMajorant (2*m) +
 PRAMappingWitnessBound.relationFamilyMajorant m

theorem negDomainMajorant_mono_left (a b s : V) (h : a ≤ b) :
 PRANegDomainWitnessBound.negDomainMajorant a s ≤ PRANegDomainWitnessBound.negDomainMajorant b s := by
  unfold PRANegDomainWitnessBound.negDomainMajorant
  exact add_le_add (add_le_add h le_rfl) (PRASeqDomainBound.domainMajorant_mono_left a b s h)

theorem neg_mapping_bound_explicit (m : V) : (∼isMappingDef.val).Evalb ![m] →
 (bnd (∼isMappingDef.val)).Evalb ![m,negMappingMajorant m] := by
  letI : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  let A := 2*m+1
  let B := PRANegDomainWitnessBound.negDomainMajorant (2*m) m
  let C := PRABitFullWitnessBound.bitMajorant (2*m)
  let D := PRANegBitFullWitnessBound.negBitMajorant (2*m)
  let E := PRAMappingWitnessBound.relationFamilyMajorant m
  have hA : A ≤ negMappingMajorant m := by simp [negMappingMajorant,A,add_assoc]
  have hB : B ≤ negMappingMajorant m := by
    simpa [negMappingMajorant,A,B,C,D,E,add_assoc,add_comm,add_left_comm] using
      (le_add_of_nonneg_right (a := B) (b := A+C+D+E) (zero_le : 0 ≤ A+C+D+E))
  have hC : C ≤ negMappingMajorant m := by
    simpa [negMappingMajorant,A,B,C,D,E,add_assoc,add_comm,add_left_comm] using
      (le_add_of_nonneg_right (a := C) (b := A+B+D+E) (zero_le : 0 ≤ A+B+D+E))
  have hD : D ≤ negMappingMajorant m := by
    simpa [negMappingMajorant,A,B,C,D,E,add_assoc,add_comm,add_left_comm] using
      (le_add_of_nonneg_right (a := D) (b := A+B+C+E) (zero_le : 0 ≤ A+B+C+E))
  have hE : E ≤ negMappingMajorant m := by
    simpa [negMappingMajorant,A,B,C,D,E,add_assoc,add_comm,add_left_comm] using
      (le_add_of_nonneg_right (a := E) (b := A+B+C+D) (zero_le : 0 ≤ A+B+C+D))
  apply neg_mapping_bound m (negMappingMajorant m) hA ?_ hC ?_ ?_
  · intro d hd
    exact le_trans (negDomainMajorant_mono_left d (2*m) m hd) hB
  · have hm : m ≤ 2*m := by simp [two_mul]
    exact le_trans (PRASeqDomainBound.negBitMajorant_mono m (2*m) hm) hD
  · intro x y hx hy
    exact le_trans (PRAMappingWitnessBound.relationFamily_bound m x y hx hy) hE
noncomputable def negMapping : ArithmeticSemisentence 1 := ∼isMappingDef.val
noncomputable def boundedNegMapping : ArithmeticSemisentence 2 := bnd negMapping
noncomputable def negMappingBoundBody : ArithmeticSemisentence 1 :=
  “m. !negMapping m → !boundedNegMapping m ((2*(m)+1)+((2*(m))+(m)+((m)+((((2*(m))⁴+1)+((2*(m))²+1)+(2*(2*(m))²+1)+((2*(m))⁴+(2*(m))⁴+2*(2*(m))+1))+(2*(m))+1)+(((2*(2*(m))+1)+(2*(2*(m))²+1))+(2*(m))+1)+((((m)⁴+1)+((m)²+1)+(2*(m)²+1)+((m)⁴+(m)⁴+2*(m)+1))+(m)+1)+(((2*(m)+1)+(2*(m)²+1))+(m)+1)))+((((2*(m))⁴+1)+((2*(m))²+1)+(2*(2*(m))²+1)+((2*(m))⁴+(2*(m))⁴+2*(2*(m))+1))+(2*(m))+1)+(((2*(2*(m))+1)+(2*(2*(m))²+1))+(2*(m))+1)+((2*(m)+(m)+1)²+1+((((m)⁴+1)+((m)²+1)+(2*(m)²+1)+((m)⁴+(m)⁴+2*(m)+1))+(m)+1)))”
theorem negMappingBoundBody_model (e : Fin 1 → V) : negMappingBoundBody.Eval e Empty.elim := by
  simp [negMappingBoundBody,boundedNegMapping,negMapping,Semiformula.eval_substs]
  have he : ![e 0] = e := by
    funext j; exact Fin.cases rfl (fun k => Fin.elim0 k) j
  rw [←he]
  intro h
  have h' : (∼isMappingDef.val).Evalb ![e 0] := by simpa using h
  exact neg_mapping_bound_explicit (e 0) h'
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
noncomputable def negMappingBoundSentence : Sentence language := ∀⁰* Semiformula.lMap embedding negMappingBoundBody
theorem candidate_proves_neg_mapping_bound : PRA ⊢ negMappingBoundSentence := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ hM
  letI : M↓[language] ⊧* PRA := hM
  letI : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
  letI : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
  letI : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
  letI : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
  letI : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  simp only [models_iff, negMappingBoundSentence, Semiformula.eval_allClosure]
  intro e
  rw [Semiformula.eval_lMap, reduct_eq_standard]
  exact negMappingBoundBody_model e
end DiophantineConsistency.PRANegMappingWitnessBound
