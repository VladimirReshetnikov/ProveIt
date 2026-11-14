import PA196PAQVecTowerConnect

/-! Explicit paths through recursive formula-substitution calls. A branch of
and/or keeps the parameter; all/exs replaces it by qVec. Paths are coded
HFS sequences of pairs (parameter, formula). The path is assumed, not
extracted from the substitution fixpoint in this module. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace PA196PASubstitutionPath
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAWitnessCodeGrowth
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

/-- A recursive call branch of the actual Substs construction. -/
def step (w p w' p' : M) : Prop :=
  (∃ a b, p = a ^⋏ b ∧ (p' = a ∨ p' = b) ∧ w' = w) ∨
  (∃ a b, p = a ^⋎ b ∧ (p' = a ∨ p' = b) ∧ w' = w) ∨
  (∃ a, p = ^∀ a ∧ p' = a ∧ w' = qVec ℒₒᵣ w) ∨
  (∃ a, p = ^∃ a ∧ p' = a ∧ w' = qVec ℒₒᵣ w)

omit [Structure.Eq language M] [M↓[language] ⊧* PRA] in
theorem step_bounds {w p w' p' : M} (h : step w p w' p') :
    w' ≤ tau (w+8) (22*w+22) ∧ p'+2 ≤ p := by
  rcases h with ⟨a,b,rfl,(rfl|rfl),rfl⟩ | ⟨a,b,rfl,(rfl|rfl),rfl⟩ |
    ⟨a,rfl,rfl,rfl⟩ | ⟨a,rfl,rfl,rfl⟩
  · exact ⟨le_trans le_self_add (le_tau _ _), add_two_le_and_left _ _⟩
  · exact ⟨le_trans le_self_add (le_tau _ _), add_two_le_and_right _ _⟩
  · exact ⟨le_trans le_self_add (le_tau _ _), add_two_le_or_left _ _⟩
  · exact ⟨le_trans le_self_add (le_tau _ _), add_two_le_or_right _ _⟩
  · exact ⟨PA196PAQVecGrowth.qVec_le _, add_two_le_all _⟩
  · exact ⟨PA196PAQVecGrowth.qVec_le _, add_two_le_exs _⟩

noncomputable def parameter (path i : M) : M := π₁ (znth path i)
noncomputable def formula (path i : M) : M := π₂ (znth path i)
instance parameter_definable : 𝚺₁-Function₂ (parameter : M → M → M) := by
  unfold parameter; definability
instance formula_definable : 𝚺₁-Function₂ (formula : M → M → M) := by
  unfold formula; definability

theorem path_bounds (path seed limit : M)
    (hbase : parameter path 0 ≤ seed)
    (hstep : ∀ i < limit, step (parameter path i) (formula path i)
      (parameter path (i+1)) (formula path (i+1))) :
    ∀ i ≤ limit, parameter path i ≤ tower i seed ∧ i + formula path i ≤ formula path 0 := by
  obtain ⟨cons,hcons⟩ := PRAHistorySeqConsCode.PRA_has_seqConsCode
  let h := history cons limit seed
  obtain ⟨hc,hl,hm⟩ := history_cseq cons hcons limit seed
  have hinvariant : ∀ i ≤ limit, parameter path i ≤ znth h i ∧ i + formula path i ≤ formula path 0 := by
    intro i
    induction i using ISigma1.sigma1_succ_induction
    · definability
    case zero =>
      intro _
      rw [bound_start seed h hc]
      exact ⟨hbase, by simp⟩
    case succ i ih =>
      intro hi
      have hlt : i < limit := lt_iff_succ_le.mpr hi
      obtain ⟨hprev,hformula⟩ := ih (le_trans le_self_add hi)
      obtain ⟨hparam,hdec⟩ := step_bounds (hstep i hlt)
      constructor
      · rw [bound_step seed limit h i hc hl hlt]
        exact le_trans hparam (tau_mono (add_le_add hprev le_rfl)
          (add_le_add (mul_le_mul' le_rfl hprev) le_rfl))
      · have hq : formula path (i+1) + 1 ≤ formula path i :=
          le_trans (add_le_add le_rfl (by norm_num : (1:M) ≤ 2)) hdec
        calc
          (i+1) + formula path (i+1) = i + (formula path (i+1) + 1) := by ring
          _ ≤ i + formula path i := add_le_add le_rfl hq
          _ ≤ formula path 0 := hformula
  intro i hi
  obtain ⟨hp,hf⟩ := hinvariant i hi
  have ht := traceHistory cons hcons limit seed
  obtain ⟨_,_,hmem⟩ := (trace_eval limit h seed).mp ht
  have hi' : i < limit+1 := lt_of_le_of_lt hi (by simp)
  have hpair : ⟪i,tower i seed⟫ ∈ h := by
    exact ((memRel_defined (V := M)).iff (v := ![h,i,tower i seed])).mp (hmem i hi')
  have heq : znth h i = tower i seed := hc.seq.znth_eq_of_mem hpair
  exact ⟨by simpa [heq] using hp, hf⟩

#print axioms step_bounds
#print axioms path_bounds
end PA196PASubstitutionPath
