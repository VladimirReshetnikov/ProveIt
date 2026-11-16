import PA196PRAQVecTraceTotal
import PA196PAQVecSeqTrace
import PA196PAQVecTowerModel

/-! Identify the candidate-PRA tower with the arithmetic IΣ₁ construction,
using the candidate-PRA sequence history at arbitrary model indices. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace PA196PAQVecTowerConnect
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PA196PRAQVecTower PA196PRAQVecHistory PA196PRAQVecTraceMatrix
  PA196PRAQVecTraceTotal PA196PAQVecSeqTrace PA196PAQVecTowerModel

variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem history_cseq (cons : Code 2)
    (hcons : PRA ⊢ PRAHistorySeqConsCode.graphSentence cons) (n seed : M) :
    let h := history cons n seed
    (boundConstruction (V := M)).CSeq ![seed] h ∧
      n + 1 = lh h ∧ ⟪n, tower n seed⟫ ∈ h := by
  let h := history cons n seed
  have ht := traceHistory cons hcons n seed
  obtain ⟨hseq,hlh,hmem⟩ := (trace_eval n h seed).mp ht
  have hs : Seq h := by
    have hh := (seq_defined (V := M)).iff (v := ![h])
    exact hh.mp hseq
  have hl : n + 1 = lh h := by
    have hh := (lh_defined (V := M)).iff (v := ![n + 1,h])
    exact hh.mp hlh
  have hm (i : M) (hi : i < n+1) : ⟪i, tower i seed⟫ ∈ h := by
    have hh := (memRel_defined (V := M)).iff (v := ![h,i,tower i seed])
    exact hh.mp (hmem i hi)
  have hzero : ⟪(0 : M), seed⟫ ∈ h := by
    have hh := hm 0 (by simp)
    simpa [tower_zero] using hh
  have hsuccessor : ∀ i < lh h - 1, ∀ z, ⟪i,z⟫ ∈ h →
      ⟪i+1, (boundConstruction (V := M)).succ ![seed] i z⟫ ∈ h := by
    intro i hi z hiz
    have hi' : i < n := by simpa [←hl] using hi
    have himem := hm i (lt_trans hi' (by simp))
    have hz : z = tower i seed := hs.isMapping.uniq hiz himem
    have hinext : i+1 < n+1 := by simpa [add_comm] using add_lt_add_right hi' 1
    have hnext := hm (i+1) hinext
    rw [tower_succ_eq_tau] at hnext
    simpa [boundConstruction, hz] using hnext
  refine ⟨⟨hs, ?_, hsuccessor⟩,hl,hm n (by simp)⟩
  simpa [boundConstruction] using hzero

theorem tower_eq_bound_result (n seed : M) :
    tower n seed = (boundConstruction (V := M)).result ![seed] n := by
  obtain ⟨cons,hcons⟩ := PRAHistorySeqConsCode.PRA_has_seqConsCode
  obtain ⟨hc,_,hm⟩ := history_cseq cons hcons n seed
  exact ((boundConstruction (V := M)).result_graph ![seed] _ _).mpr
    ⟨history cons n seed, hc, hm⟩

theorem qVec_iter_le_tower (n seed : M) :
    (construction (V := M)).result ![seed] n ≤ tower n seed := by
  rw [tower_eq_bound_result]
  exact result_bound seed n

#print axioms history_cseq
#print axioms tower_eq_bound_result
#print axioms qVec_iter_le_tower
end PA196PAQVecTowerConnect
