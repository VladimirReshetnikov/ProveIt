import PA196PAQVecTowerAlgebra
import PA194PAeqQVecSeqTrace
import PA194QVecCeiling
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace PA194PAeqQVecCeiling
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194PAeqQVecSeqTrace PA196PAQVecTowerAlgebra
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem bounded_trace (seed limit : V) :
    ∃ qs : V, (construction (V := V)).CSeq ![seed] qs ∧ limit + 1 = lh qs ∧
      ∀ i ≤ limit, znth qs i ≤ iter limit seed := by
  obtain ⟨qs,hq,hlq⟩ := exists_trace seed limit
  obtain ⟨bs,hb,hlb⟩ := exists_bound_trace seed limit
  refine ⟨qs,hq,hlq,?_⟩
  intro i hi
  have hbmem := hb.seq.znth (show i < lh bs by rw [←hlb]; exact lt_of_le_of_lt hi (by simp))
  have heq : znth bs i = iter i seed := by
    exact ((boundConstruction (V := V)).result_graph ![seed] _ _).mpr ⟨bs,hb,hbmem⟩
  calc
    znth qs i ≤ znth bs i := trace_bounded seed limit qs bs hq hb hlq hlb i hi
    _ = iter i seed := heq
    _ ≤ iter limit seed := iter_index_mono i limit seed hi

theorem bounded_trace_explicit (seed limit : V) :
    ∃ qs : V, (construction (V := V)).CSeq ![seed] qs ∧ limit + 1 = lh qs ∧
      znth qs 0 = seed ∧
      (∀ i < limit, znth qs (i+1) = qVec PA194PAeq.language (znth qs i)) ∧
      ∀ i ≤ limit, znth qs i ≤ iter limit seed := by
  obtain ⟨qs,hq,hl,hbound⟩ := bounded_trace seed limit
  exact ⟨qs,hq,hl,trace_start seed qs hq,(fun i hi => trace_step seed limit qs i hq hl hi),hbound⟩

/-- The same tower value bounds both arithmetic and PAeq qVec histories
started from the same seed, at every model-internal index. -/
theorem paired_source_target_traces (seed limit : V) :
    ∃ source target : V,
      (PA196PAQVecSeqTrace.construction (V := V)).CSeq ![seed] source ∧
      (PA194PAeqQVecSeqTrace.construction (V := V)).CSeq ![seed] target ∧
      limit + 1 = lh source ∧ limit + 1 = lh target ∧
      ∀ i ≤ limit, znth source i ≤ iter limit seed ∧ znth target i ≤ iter limit seed := by
  obtain ⟨source,hs,hls,hbs⟩ := PA194QVecCeiling.bounded_trace seed limit
  obtain ⟨target,ht,hlt,hbt⟩ := bounded_trace seed limit
  exact ⟨source,target,hs,ht,hls,hlt,fun i hi => ⟨hbs i hi,hbt i hi⟩⟩

#print axioms paired_source_target_traces
#print axioms bounded_trace_explicit
#print axioms bounded_trace
end PA194PAeqQVecCeiling
