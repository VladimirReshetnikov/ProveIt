import PA196PAQVecTowerConnect

/-! A coded path with steps bounded by the qVec numerical majorant is dominated by the candidate-PRA
tower at all model-internal indices. This does not identify the path with
any particular formula-substitution recursion. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace PA196PAQVecPathBound
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PA196PRAQVecTower PA196PRAQVecHistory PA196PRAQVecTraceMatrix
  PA196PRAQVecTraceTotal PA196PAQVecSeqTrace PA196PAQVecTowerConnect

variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem path_le_tower_of_majorant (path seed limit : M)
    (hbase : znth path 0 ≤ seed)
    (hstep : ∀ i < limit, znth path (i+1) ≤
      PRAWitnessCodeGrowth.tau (znth path i + 8) (22 * znth path i + 22)) :
    ∀ i ≤ limit, znth path i ≤ tower i seed := by
  obtain ⟨cons,hcons⟩ := PRAHistorySeqConsCode.PRA_has_seqConsCode
  let h := history cons limit seed
  obtain ⟨hc,hl,hm⟩ := history_cseq cons hcons limit seed
  have hinvariant : ∀ i ≤ limit, znth path i ≤ znth h i := by
    intro i
    induction i using ISigma1.sigma1_succ_induction
    · definability
    case zero =>
      intro _
      rw [bound_start seed h hc]
      exact hbase
    case succ i ih =>
      intro hi
      have hlt : i < limit := lt_iff_succ_le.mpr hi
      have hprev := ih (le_trans le_self_add hi)
      rw [bound_step seed limit h i hc hl hlt]
      exact le_trans (hstep i hlt)
        (PRAWitnessCodeGrowth.tau_mono (add_le_add hprev le_rfl)
          (add_le_add (mul_le_mul' le_rfl hprev) le_rfl))
  intro i hi
  have ht := traceHistory cons hcons limit seed
  obtain ⟨_,_,hmem⟩ := (trace_eval limit h seed).mp ht
  have hi' : i < limit+1 := lt_of_le_of_lt hi (by simp)
  have hpair : ⟪i,tower i seed⟫ ∈ h := by
    exact ((memRel_defined (V := M)).iff (v := ![h,i,tower i seed])).mp (hmem i hi')
  have heq : znth h i = tower i seed := hc.seq.znth_eq_of_mem hpair
  simpa [heq] using hinvariant i hi

theorem path_le_tower (path seed limit : M)
    (hbase : znth path 0 ≤ seed)
    (hstep : ∀ i < limit, znth path (i+1) ≤ qVec ℒₒᵣ (znth path i)) :
    ∀ i ≤ limit, znth path i ≤ tower i seed := by
  apply path_le_tower_of_majorant path seed limit hbase
  intro i hi
  exact le_trans (hstep i hi) (PA196PAQVecGrowth.qVec_le _)

#print axioms path_le_tower_of_majorant
#print axioms path_le_tower
end PA196PAQVecPathBound
