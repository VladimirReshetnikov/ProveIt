import ZFCinPA.ModelCodedRenamingSets
import ZFCinPA.ModelCodedRenamingAxioms
import ZFCinPA.ModelCodedRenamingBindOne

/-!
Bounded two-counter transport of arbitrary internal derivations under represented
free renaming. The auxiliary theorem states its exact syntactic axiom-closure
resource; the actual ZF/ZFC corollaries discharge it with the checked literal
axiom recognizers. The induction is Sigma1: both changing counters are bounded
by one fixed internal budget. This does not translate C254 proof rows or give a
consistency comparison.
-/
namespace LeanProofs.ZFCinPA.ModelCodedProofRenaming
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA.ModelCodedFreeRenaming
open LeanProofs.ZFCinPA.ModelCodedRenamingSets
open LeanProofs.ZFCinPA.ModelCodedRenamingAxioms
open LeanProofs.ZFCinPA.ModelCodedRenamingBindOne
open LeanProofs.ZFCinPA.ModelCodedBindOne
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]
variable {T : Theory L} [T.Δ₁]

private lemma budget_mono {child parent level newLevel offset newOffset total : V}
    (hc : child ≤ parent) (hk : newLevel ≤ level) (ho : newOffset ≤ offset)
    (hb : parent+level+offset ≤ total) : child+newLevel+newOffset ≤ total :=
  le_trans (add_le_add (add_le_add hc hk) ho) hb
private lemma budget_lift {child parent level offset total : V}
    (hc : child < parent) (hb : parent+level+offset ≤ total) :
    child+(level+1)+offset ≤ total := by
  calc
    child+(level+1)+offset = (child+1)+level+offset := by ac_rfl
    _ ≤ parent+level+offset := add_le_add (add_le_add (lt_iff_succ_le.mp hc) le_rfl) le_rfl
    _ ≤ total := hb
private lemma budget_offset {child parent level offset total : V}
    (hc : child < parent) (hb : parent+level+offset ≤ total) :
    child+level+(offset+1) ≤ total := by
  calc
    child+level+(offset+1) = (child+1)+level+offset := by ac_rfl
    _ ≤ parent+level+offset := add_le_add (add_le_add (lt_iff_succ_le.mp hc) le_rfl) le_rfl
    _ ≤ total := hb
private lemma level_le_budget (proof level offset : V) : level ≤ proof+level+offset := by
  have h : level ≤ proof+level := by simp
  exact le_trans h (by simp)
private lemma offset_le_budget (proof level offset : V) : offset ≤ proof+level+offset := by
  simp

/-- Only bounded counter quantifiers occur in the actual induction predicate. -/
theorem derivable_rename_bounded (chosen total : V)
    (hAx : ∀ level offset p : V, IsFormula L p → p ∈ T.Δ₁Class →
      rename L chosen level offset p ∈ T.Δ₁Class) :
    ∀ d : V, Derivation T d → ∀ level ≤ total, ∀ offset ≤ total,
      d+level+offset ≤ total →
      Derivable T (setRename L chosen level offset (fstIdx d)) := by
  apply ISigma1.sigma1_order_induction (P := fun d : V =>
    Derivation T d → ∀ level ≤ total, ∀ offset ≤ total,
      d+level+offset ≤ total →
      Derivable T (setRename L chosen level offset (fstIdx d)))
  · apply HierarchySymbol.Definable.imp (by definability)
    apply HierarchySymbol.Definable.ball_le (by definability)
    apply HierarchySymbol.Definable.ball_le (by definability)
    apply HierarchySymbol.Definable.imp (by definability)
    definability
  · intro d ih hd level hk offset ho hb
    rcases hd.case with ⟨hseq,
      (⟨sequence,p,rfl,hp,hnp⟩ | ⟨sequence,rfl,hp⟩ |
       ⟨sequence,p,q,dp,dq,rfl,hpq,hdp,hdq⟩ |
       ⟨sequence,p,q,dp,rfl,hpq,hdp⟩ |
       ⟨sequence,p,dp,rfl,hp,hdp⟩ |
       ⟨sequence,p,term,dp,rfl,hp,ht,hdp⟩ |
       ⟨sequence,dp,rfl,hsub,hdp⟩ |
       ⟨sequence,dp,rfl,hsequence,hdp⟩ |
       ⟨sequence,p,dp,dn,rfl,hdp,hdn⟩ |
       ⟨sequence,p,rfl,hp,hT⟩)⟩
    · have hs : IsFormulaSet L sequence := by simpa only [fstIdx_axL] using hseq
      have hm : neg L (rename L chosen level offset p) ∈
          setRename L chosen level offset sequence := by
        rw [←rename_neg chosen level offset (hs p hp).isUFormula]
        exact rename_mem_setRename chosen level offset hnp
      simpa only [fstIdx_axL] using Derivable.em
        (setRename_isFormulaSet chosen level offset hs)
        (rename L chosen level offset p) (rename_mem_setRename chosen level offset hp) hm
    · have hs : IsFormulaSet L sequence := by simpa only [fstIdx_verumIntro] using hseq
      have hm : ^⊤ ∈ setRename L chosen level offset sequence := by
        simpa only [rename_verum] using rename_mem_setRename chosen level offset hp
      simpa only [fstIdx_verumIntro] using
        Derivable.verum (setRename_isFormulaSet chosen level offset hs) hm
    · have hs : IsFormulaSet L sequence := by simpa only [fstIdx_andIntro] using hseq
      have hparts : IsFormula L p ∧ IsFormula L q := IsSemiformula.and.mp (hs _ hpq)
      have ihp := ih dp (dp_lt_andIntro sequence p q dp dq) hdp.2 level hk offset ho
        (budget_mono (le_of_lt (dp_lt_andIntro sequence p q dp dq)) le_rfl le_rfl hb)
      have ihq := ih dq (dq_lt_andIntro sequence p q dp dq) hdq.2 level hk offset ho
        (budget_mono (le_of_lt (dq_lt_andIntro sequence p q dp dq)) le_rfl le_rfl hb)
      rw [hdp.1,setRename_insert] at ihp
      rw [hdq.1,setRename_insert] at ihq
      have hm : (rename L chosen level offset p ^⋏ rename L chosen level offset q) ∈
          setRename L chosen level offset sequence := by
        rw [←rename_and chosen level offset hparts.1.isUFormula hparts.2.isUFormula]
        exact rename_mem_setRename chosen level offset hpq
      simpa only [fstIdx_andIntro] using Derivable.and_m hm ihp ihq
    · have hs : IsFormulaSet L sequence := by simpa only [fstIdx_orIntro] using hseq
      have hparts : IsFormula L p ∧ IsFormula L q := IsSemiformula.or.mp (hs _ hpq)
      have ihp := ih dp (d_lt_orIntro sequence p q dp) hdp.2 level hk offset ho
        (budget_mono (le_of_lt (d_lt_orIntro sequence p q dp)) le_rfl le_rfl hb)
      rw [hdp.1,setRename_insert,setRename_insert] at ihp
      have hm : (rename L chosen level offset p ^⋎ rename L chosen level offset q) ∈
          setRename L chosen level offset sequence := by
        rw [←rename_or chosen level offset hparts.1.isUFormula hparts.2.isUFormula]
        exact rename_mem_setRename chosen level offset hpq
      simpa only [fstIdx_orIntro] using Derivable.or_m hm ihp
    · have hs : IsFormulaSet L sequence := by simpa only [fstIdx_allIntro] using hseq
      have hp1 : IsSemiformula L 1 p := by simpa using hs _ hp
      have hchild : dp+(level+1)+offset ≤ total :=
        budget_lift (s_lt_allIntro sequence p dp) hb
      have hk' : level+1 ≤ total := le_trans (level_le_budget dp (level+1) offset) hchild
      have ihp := ih dp (s_lt_allIntro sequence p dp) hdp.2 (level+1) hk' offset ho hchild
      rw [hdp.1,setRename_insert,rename_free_lift chosen level offset hp1,
        setRename_shift_lift chosen level offset hs] at ihp
      have hm : ^∀ (rename L chosen level offset p) ∈
          setRename L chosen level offset sequence := by
        rw [←rename_all chosen level offset hp1.isUFormula]
        exact rename_mem_setRename chosen level offset hp
      simpa only [fstIdx_allIntro] using Derivable.all_m hm ihp
    · have hs : IsFormulaSet L sequence := by simpa only [fstIdx_exsIntro] using hseq
      have hp1 : IsSemiformula L 1 p := by simpa using hs _ hp
      have ihp := ih dp (d_lt_exsIntro sequence p term dp) hdp.2 level hk offset ho
        (budget_mono (le_of_lt (d_lt_exsIntro sequence p term dp)) le_rfl le_rfl hb)
      rw [hdp.1,setRename_insert,rename_substs1 chosen level offset hp1 ht] at ihp
      have hm : ^∃ (rename L chosen level offset p) ∈
          setRename L chosen level offset sequence := by
        rw [←rename_exs chosen level offset hp1.isUFormula]
        exact rename_mem_setRename chosen level offset hp
      simpa only [fstIdx_exsIntro] using Derivable.ex_m hm
        (termRename_isSemiterm chosen level offset ht) ihp
    · have hs : IsFormulaSet L sequence := by simpa only [fstIdx_wkRule] using hseq
      have ihp := ih dp (d_lt_wkRule sequence dp) hdp level hk offset ho
        (budget_mono (le_of_lt (d_lt_wkRule sequence dp)) le_rfl le_rfl hb)
      simpa only [fstIdx_wkRule] using Derivable.wk
        (setRename_isFormulaSet chosen level offset hs)
        (setRename_subset chosen level offset hsub) ihp
    · rcases zero_or_succ level with rfl | ⟨level,rfl⟩
      · have hchild : dp+0+(offset+1) ≤ total :=
          budget_offset (d_lt_shiftRule sequence dp) hb
        have ho' : offset+1 ≤ total := le_trans (offset_le_budget dp 0 (offset+1)) hchild
        have ihp := ih dp (d_lt_shiftRule sequence dp) hdp 0 (by simp) (offset+1) ho' hchild
        simpa only [fstIdx_shiftRule,hsequence,
          setRename_shift_offset chosen offset hdp.isFormulaSet] using ihp
      · have ihp := ih dp (d_lt_shiftRule sequence dp) hdp level
          (le_trans (by simp) hk) offset ho
          (budget_mono (le_of_lt (d_lt_shiftRule sequence dp)) (by simp) le_rfl hb)
        have hshift := Derivable.shift ihp
        simpa only [fstIdx_shiftRule,hsequence,
          setRename_shift_lift chosen level offset hdp.isFormulaSet] using hshift
    · have hp0 : IsFormula L p := hdp.isFormulaSet p (by simp)
      have ihp := ih dp (d₁_lt_cutRule sequence p dp dn) hdp.2 level hk offset ho
        (budget_mono (le_of_lt (d₁_lt_cutRule sequence p dp dn)) le_rfl le_rfl hb)
      have ihn := ih dn (d₂_lt_cutRule sequence p dp dn) hdn.2 level hk offset ho
        (budget_mono (le_of_lt (d₂_lt_cutRule sequence p dp dn)) le_rfl le_rfl hb)
      rw [hdp.1,setRename_insert] at ihp
      rw [hdn.1,setRename_insert,rename_neg chosen level offset hp0.isUFormula] at ihn
      simpa only [fstIdx_cutRule] using Derivable.cut (rename L chosen level offset p) ihp ihn
    · have hs : IsFormulaSet L sequence := by simpa only [fstIdx_axm] using hseq
      simpa only [fstIdx_axm] using Derivable.by_axm
        (setRename_isFormulaSet chosen level offset hs)
        (rename L chosen level offset p) (rename_mem_setRename chosen level offset hp)
        (hAx level offset p (hs p hp) hT)

/-- The budget is chosen from the supplied arbitrary internal proof code. -/
theorem derivable_rename (chosen : V)
    (hAx : ∀ level offset p : V, IsFormula L p → p ∈ T.Δ₁Class →
      rename L chosen level offset p ∈ T.Δ₁Class)
    {d : V} (hd : Derivation T d) :
    Derivable T (setRename L chosen 0 0 (fstIdx d)) :=
  derivable_rename_bounded chosen d hAx d hd 0 (by simp) 0 (by simp) (by simp)

theorem provable_rename (chosen : V)
    (hAx : ∀ level offset p : V, IsFormula L p → p ∈ T.Δ₁Class →
      rename L chosen level offset p ∈ T.Δ₁Class)
    {p : V} (hp : Provable T p) : Provable T (rename L chosen 0 0 p) := by
  rcases hp.toDerivable with ⟨d,hd⟩
  have h := derivable_rename chosen hAx hd.2
  rw [hd.1,setRename_insert,setRename_empty] at h
  exact h.toProvable

/-- Actual ZF proof renaming has no remaining axiom-closure hypothesis. -/
theorem zf_provable_rename (chosen : V) {p : V} (hp : Provable (𝗭𝗙 : SetTheory) p) :
    Provable (𝗭𝗙 : SetTheory) (rename ℒₛₑₜ chosen 0 0 p) :=
  provable_rename chosen (fun level offset _ hf hT => zf_rename_mem chosen level offset hf hT) hp
/-- Actual ZFC proof renaming has no remaining axiom-closure hypothesis. -/
theorem zfc_provable_rename (chosen : V) {p : V} (hp : Provable (𝗭𝗙𝗖 : SetTheory) p) :
    Provable (𝗭𝗙𝗖 : SetTheory) (rename ℒₛₑₜ chosen 0 0 p) :=
  provable_rename chosen (fun level offset _ hf hT => zfc_rename_mem chosen level offset hf hT) hp

private lemma provable_namedAll_of_renamed {p : V} (chosen : V) (hp : IsFormula L p)
    (h : Provable T (rename L chosen 0 0 p)) : Provable T (namedAll L chosen p) := by
  have hbody : IsSemiformula L 1 (bindOneAt L chosen 0 p) := by
    simpa only [zero_add] using bindOneAt_isSemiformula hp chosen
  have hfree : Derivable T (insert (free L (bindOneAt L chosen 0 p)) (∅ : V)) := by
    rw [free_bindOneAt hp chosen]
    exact h.toDerivable
  have hall : Derivable T (insert (^∀ (bindOneAt L chosen 0 p)) (∅ : V)) := by
    apply Derivable.all hbody
    simpa only [setShift_empty] using hfree
  exact hall.toProvable

/-- Named GEN for all internal ZF formulas, including formulas containing free zero. -/
theorem zf_provable_namedAll (chosen : V) {p : V} (hp : Provable (𝗭𝗙 : SetTheory) p) :
    Provable (𝗭𝗙 : SetTheory) (namedAll ℒₛₑₜ chosen p) := by
  have hf : IsFormula ℒₛₑₜ p := hp.toDerivable.isFormulaSet p (by simp)
  exact provable_namedAll_of_renamed chosen hf (zf_provable_rename chosen hp)
/-- Named GEN for all internal ZFC formulas, with no closed-matrix premise. -/
theorem zfc_provable_namedAll (chosen : V) {p : V} (hp : Provable (𝗭𝗙𝗖 : SetTheory) p) :
    Provable (𝗭𝗙𝗖 : SetTheory) (namedAll ℒₛₑₜ chosen p) := by
  have hf : IsFormula ℒₛₑₜ p := hp.toDerivable.isFormulaSet p (by simp)
  exact provable_namedAll_of_renamed chosen hf (zfc_provable_rename chosen hp)

end LeanProofs.ZFCinPA.ModelCodedProofRenaming
