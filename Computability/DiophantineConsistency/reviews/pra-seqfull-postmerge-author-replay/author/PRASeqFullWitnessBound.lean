import DiophantineConsistency.PRAMappingWitnessBound
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DiophantineConsistency.PRASeqFullWitnessBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.StrictSigmaOneInduction
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
def seqMajorant (s : V) : V := (2*s+1) + PRAExponentialWitnessBound.exponentialMajorant (2*s+1) +
 PRADomainWitnessBound.domainMajorant (2*s) s + PRAMappingWitnessBound.mappingMajorant s

theorem seq_bound_explicit (s : V) : seqDef.val.Evalb ![s] →
 (bnd seqDef.val).Evalb ![s,seqMajorant s] := by
  letI : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  let A := 2*s+1
  let B := PRAExponentialWitnessBound.exponentialMajorant (2*s+1)
  let C := PRADomainWitnessBound.domainMajorant (2*s) s
  let D := PRAMappingWitnessBound.mappingMajorant s
  have hA : A ≤ seqMajorant s := by simp [seqMajorant,A,add_assoc]
  have hB : B ≤ seqMajorant s := by
    simpa [seqMajorant,A,B,C,D,add_assoc,add_comm,add_left_comm] using
      (le_add_of_nonneg_right (a := B) (b := A+C+D) (zero_le : 0 ≤ A+C+D))
  have hC : C ≤ seqMajorant s := by
    simpa [seqMajorant,A,B,C,D,add_assoc,add_comm,add_left_comm] using
      (le_add_of_nonneg_right (a := C) (b := A+B+D) (zero_le : 0 ≤ A+B+D))
  have hD : D ≤ seqMajorant s := by
    simpa [seqMajorant,A,B,C,D,add_assoc,add_comm,add_left_comm] using
      (le_add_of_nonneg_right (a := D) (b := A+B+C) (zero_le : 0 ≤ A+B+C))
  apply PRASeqDomainBound.seq_bound_of_domain s (seqMajorant s) hA hB hC
  intro hm
  have hb := PRAMappingWitnessBound.mapping_bound_explicit s hm
  have hs : Fin.snoc ![s] (PRAMappingWitnessBound.mappingMajorant s) = ![s,PRAMappingWitnessBound.mappingMajorant s] := by
    funext j; refine Fin.cases rfl (fun k => ?_) j; exact Fin.cases rfl (fun k => Fin.elim0 k) k
  have hm' := eval_bnd_mono isMappingDef.val ![s] (Empty.elim : Empty → V) hD (by rw [hs]; exact hb)
  have hs' : Fin.snoc ![s] (seqMajorant s) = ![s,seqMajorant s] := by
    funext j; refine Fin.cases rfl (fun k => ?_) j; exact Fin.cases rfl (fun k => Fin.elim0 k) k
  rw [hs'] at hm'
  exact hm'
noncomputable def boundedSeq : ArithmeticSemisentence 2 := bnd seqDef.val
noncomputable def seqBoundBody : ArithmeticSemisentence 1 :=
  “s. !seqDef s → !boundedSeq s ((2*(s)+1)+(((2*(s)+1)⁴+1)+((2*(s)+1)²+1)+(2*(2*(s)+1)²+1)+((2*(s)+1)⁴+(2*(s)+1)⁴+2*(2*(s)+1)+1))+((s)+((((2*(s))⁴+1)+((2*(s))²+1)+(2*(2*(s))²+1)+((2*(s))⁴+(2*(s))⁴+2*(2*(s))+1))+(2*(s))+1)+(((2*(2*(s))+1)+(2*(2*(s))²+1))+(2*(s))+1)+((((s)⁴+1)+((s)²+1)+(2*(s)²+1)+((s)⁴+(s)⁴+2*(s)+1))+(s)+1)+(((2*(s)+1)+(2*(s)²+1))+(s)+1))+((2*(s)+1)+((s)+((((2*(s))⁴+1)+((2*(s))²+1)+(2*(2*(s))²+1)+((2*(s))⁴+(2*(s))⁴+2*(2*(s))+1))+(2*(s))+1)+(((2*(2*(s))+1)+(2*(2*(s))²+1))+(2*(s))+1)+((((s)⁴+1)+((s)²+1)+(2*(s)²+1)+((s)⁴+(s)⁴+2*(s)+1))+(s)+1)+(((2*(s)+1)+(2*(s)²+1))+(s)+1))+(((2*(2*(s))+1)+(2*(2*(s))²+1))+(2*(s))+1)+((2*(s)+(s)+1)²+1+((((s)⁴+1)+((s)²+1)+(2*(s)²+1)+((s)⁴+(s)⁴+2*(s)+1))+(s)+1))))”
theorem seqBoundBody_model (e : Fin 1 → V) : seqBoundBody.Eval e Empty.elim := by
  simp [seqBoundBody,boundedSeq,Semiformula.eval_substs]
  have he : ![e 0] = e := by
    funext j; exact Fin.cases rfl (fun k => Fin.elim0 k) j
  rw [←he]
  exact seq_bound_explicit (e 0)
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
noncomputable def seqBoundSentence : Sentence language := ∀⁰* Semiformula.lMap embedding seqBoundBody
theorem candidate_proves_seq_bound : PRA ⊢ seqBoundSentence := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ hM
  letI : M↓[language] ⊧* PRA := hM
  letI : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
  letI : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
  letI : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
  letI : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
  letI : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  simp only [models_iff, seqBoundSentence, Semiformula.eval_allClosure]
  intro e
  rw [Semiformula.eval_lMap, reduct_eq_standard]
  exact seqBoundBody_model e
end DiophantineConsistency.PRASeqFullWitnessBound
