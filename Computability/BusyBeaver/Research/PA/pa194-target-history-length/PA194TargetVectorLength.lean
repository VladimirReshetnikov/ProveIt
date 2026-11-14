import PA194TargetGuardedHistory
import DiophantineConsistency.PRABoundedSearchUniversal
import DiophantineConsistency.PRABoundedSearchFreeze
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194TargetVectorLength
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PRABoundedSearchCode PRABoundedSearchUniversal PRABoundedSearchFreeze
 PA194PathIterator PA194TermShiftCodeModel PA194CloseVariable PA194TargetCantor
 PA194TargetStep PA194TargetSound PA194TargetExtendedStep PA194ParamHistory PA194StackCode PA194StackHistory
 PA194TargetGuardedHistory
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def tailCode : Code 1 := stackComponent secondProjection
noncomputable def drop : Code 2 := dropCode tailCode
noncomputable def lengthCode : Code 1 := bin (searchCode drop) (.proj 0) (.proj 0)

theorem drop_zero (v : M) : F drop ![0,v] = v := by
  exact modelDropBase tailCode v

theorem drop_succ (i v : M) : F drop ![i+1,v] = F drop ![i,sndIdx v] := by
  rw [drop,modelDropShift]
  change F (dropCode tailCode) ![i,F (stackComponent secondProjection) (fun _ => v)] = _
  rw [PA194SearchVector.component_second]

theorem bounded_pred_generic (f : M → M → M) (g : M → M) (v : M)
    (hf : 𝚺₁-Function₂ f) (hg : 𝚺₁-Function₁ g) :
    𝚺₁-Predicate (fun i : M => ∀ w ≤ v, (f i w = 0 ∧ g w ≤ i) ∨ (f i w ≠ 0 ∧ i < g w)) := by
  haveI := hf
  haveI := hg
  definability

theorem bounded_pred_def (v : M) :
    𝚺₁-Predicate (fun i : M => ∀ w ≤ v, F drop ![i,w] = 0 ↔ len w ≤ i) := by
  have hf : 𝚺₁-Function₂ (fun i w : M => F drop ![i,w]) := by
    have h : 𝚺₁.DefinableFunction (fun e : Fin 2 → M => F drop e) :=
      HierarchySymbol.Defined.to_definable _ (PA194CodeGraph.modelGraph (M := M) drop)
    convert h using 1
    funext e
    exact congrArg (fun e : Fin 2 → M => F drop e) (Matrix.fun_eq_vec_two e).symm
  have h := bounded_pred_generic (fun i w : M => F drop ![i,w]) len v hf inferInstance
  convert h using 1
  funext i
  apply propext
  apply forall_congr'
  intro w
  apply forall_congr'
  intro hw
  by_cases hzero : F drop ![i,w] = 0 <;> by_cases hlen : len w ≤ i <;>
    simp [hzero,hlen,← not_le]

theorem drop_eq_zero_iff (i v : M) : F drop ![i,v] = 0 ↔ len v ≤ i := by
  suffices ∀ w ≤ v, F drop ![i,w] = 0 ↔ len w ≤ i from this v (by simp)
  induction i using ISigma1.sigma1_succ_induction with
  | hP => exact bounded_pred_def v
  | zero =>
    intro w hw
    rw [drop_zero]
    simp
  | succ i ih =>
    intro w hw
    rw [drop_succ]
    rcases nil_or_adjoin w with (rfl | ⟨x,t,rfl⟩)
    · have hz := ih 0 (by simp)
      simpa [sndIdx,pi₂_zero] using hz
    · have ht := ih t (le_trans (le_of_lt (lt_adjoin' x t)) hw)
      simpa using ht

theorem search_at_length (v : M) : F (searchCode drop) ![len v,v] = len v := by
  have h := modelSearchUniversal drop (len v) (fun _ => v)
  have hv (x : M) : Fin.cases x (fun _ : Fin 1 => v) = ![x,v] := by
    funext i
    exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i
  simp only [hv] at h
  change (F (searchCode drop) ![len v,v] = len v ↔
    ∀ x : M, x < len v → F drop ![x,v] ≠ 0) at h
  apply h.mpr
  intro x hx hz
  have hl := (drop_eq_zero_iff x v).mp hz
  exact (not_lt_of_ge hl) hx

theorem length_model (v : M) : F lengthCode ![v] = len v := by
  have hs := search_at_length v
  obtain ⟨k,hk⟩ := le_iff_exists_add.mp (len_le v)
  have hb : F drop ![F (searchCode drop) ![len v,v],v] = 0 := by
    rw [hs,drop_eq_zero_iff]
  have hv (x : M) : Fin.cases x (fun _ : Fin 1 => v) = ![x,v] := by
    funext i
    exact Fin.cases rfl (fun j => Fin.cases rfl (fun q => Fin.elim0 q) j) i
  have hb' : F drop (Fin.cases (F (searchCode drop) (Fin.cases (len v) (fun _ : Fin 1 => v))) (fun _ : Fin 1 => v)) = F (.zero 0) Fin.elim0 := by
    rw [hv,hv]
    exact hb
  have hf := modelSearchFreeze drop (len v) k (fun _ => v) hb'
  simp only [hv] at hf
  change F (searchCode drop) ![len v + k,v] = F (searchCode drop) ![len v,v] at hf
  rw [←hk,hs] at hf
  rw [lengthCode,modelBin,modelProjection]
  simp only [Matrix.cons_val_zero]
  exact hf

/-- Compute the actual vector length and feed it to the guarded target step. -/
noncomputable def autoNext : Code 4 :=
  app4 PA194TargetGuardedHistory.next (.proj 0) (.proj 1) (.proj 2) (unary lengthCode (.proj 2))
noncomputable def autoHistory : Code 3 := PA194ParamHistory.historyCode autoNext

theorem autoNext_model (n hist program spare : M) :
    F autoNext ![n,hist,program,spare] =
      if n < len program then F extended ![n,hist,program.[n]] else 0 := by
  rw [autoNext,app4_model]
  simp only [modelProjection,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
  rw [modelUnary,modelProjection]
  simp only [Matrix.cons_val_two]
  change F PA194TargetGuardedHistory.next ![n,hist,program,F lengthCode (fun _ => program)] = _
  have hv : (fun _ : Fin 1 => program) = ![program] := by
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  rw [hv,length_model,PA194TargetGuardedHistory.next_model]

theorem auto_rejects_past_length (n hist program spare : M) (h : len program ≤ n) :
    F autoNext ![n,hist,program,spare] = 0 := by
  rw [autoNext_model,if_neg (not_lt_of_ge h)]

theorem autoHistory_step (n program spare : M) :
    F autoHistory ![n+1,program,spare] =
      pair (if n < len program then F extended ![n,F autoHistory ![n,program,spare],program.[n]] else 0)
        (F autoHistory ![n,program,spare])+1 := by
  rw [autoHistory,PA194ParamHistory.modelStep,autoNext_model]

theorem autoHistory_newest (n program spare : M) :
    F lookup ![0,F autoHistory ![n+1,program,spare]] =
      if n < len program then F extended ![n,F autoHistory ![n,program,spare],program.[n]] else 0 := by
  rw [autoHistory_step]
  exact modelLookupZero firstProjection secondProjection firstProjection_certified _ _

theorem autoHistory_earlier (n i program spare : M) :
    F lookup ![i+1,F autoHistory ![n+1,program,spare]] =
      F lookup ![i,F autoHistory ![n,program,spare]] := by
  rw [autoHistory_step]
  exact modelLookupConsSucc firstProjection secondProjection secondProjection_certified _ _ _

theorem autoHistory_sound (G : M → Prop) (hG : 𝚺₁-Predicate G)
    (hLeaf : ∀ a b, G (F machineHead1 ![a,b]))
    (hGen : ∀ label a, G a → G (allValue label a))
    (hMP : ∀ a b, G a → G (impValue a b) → G b)
    (hNew : LeafClosure G)
    (program spare n : M) : GoodHistory G n (F autoHistory ![n,program,spare]) := by
  have hf : 𝚺₁-Function₁ (fun n : M => F autoHistory ![n,program,spare]) :=
    PA194CodeInstance.unary_of_three autoHistory program spare
  have hdef := relation_substitution_def (GoodHistory G) _ (goodHistory_definable G hG) hf
  induction n using ISigma1.sigma1_succ_induction with
  | hP => exact hdef
  | zero =>
    intro i hi
    exact False.elim (not_lt_zero hi)
  | succ n ih =>
    intro i hi
    rcases zero_or_succ i with rfl | ⟨j,rfl⟩
    · rw [autoHistory_newest]
      by_cases hn : n < len program
      · rw [if_pos hn]
        exact extended_sound G hLeaf hGen hMP hNew n _ _ ih
      · rw [if_neg hn]
        exact Or.inl rfl
    · rw [autoHistory_earlier]
      apply ih j
      exact (add_lt_add_iff_right 1).mp hi

theorem autoAccepted_sound (G : M → Prop) (hG : 𝚺₁-Predicate G)
    (hLeaf : ∀ a b, G (F machineHead1 ![a,b]))
    (hGen : ∀ label a, G a → G (allValue label a))
    (hMP : ∀ a b, G a → G (impValue a b) → G b)
    (hNew : LeafClosure G)
    (program spare n i v : M) (hi : i < n)
    (hv : F lookup ![i,F autoHistory ![n,program,spare]] = v+1) : G v := by
  have h := autoHistory_sound G hG hLeaf hGen hMP hNew program spare n i hi
  rw [hv] at h
  exact (good_value_accepted G v).mp h

#print axioms autoNext_model
#print axioms auto_rejects_past_length
#print axioms autoHistory_sound
#print axioms autoAccepted_sound
#print axioms length_model
#print axioms drop_eq_zero_iff
end models
end PA194TargetVectorLength
