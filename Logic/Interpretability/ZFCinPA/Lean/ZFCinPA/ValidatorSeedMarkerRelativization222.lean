import ZFCinPA.ValidatorSeedMarkerDischarge222

set_option autoImplicit false
set_option Elab.async false
noncomputable section

/-! Moving-marker transport of actual internally coded source derivations.
The first tagged stage preserves raw equality and membership. Axiom images
remain exactly the displayed resource with p<j; no Good or semantic premise
replaces them. All counter induction is internal I-Sigma1 induction. -/
namespace LeanProofs.ZFCinPA.ValidatorSeedMarkerRelativization222
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LO.FirstOrder.SetTheory
open LeanProofs.BoundedPAConsistency.InternalRelativization
open ValidatorFullSeedTheory222 ValidatorSeedSourceBasis222 ValidatorSeedMarkerDischarge222
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def tagRel (j p : V) : V := relativize ℒₛₑₜ (domainCode j) p
def tagSet (j s : V) : V := relSet ℒₛₑₜ (domainCode j) s
def emptyGuard (j : V) : V := neg ℒₛₑₜ (emptyCode j)
def taggedSeq (j s : V) : V := insert (emptyGuard j) (tagSet j s ∪ sideSet j)

instance tagRel_definable : 𝚺₁-Function₂[V] tagRel := by unfold tagRel; definability
instance tagSet_definable : 𝚺₁-Function₂[V] tagSet := by unfold tagSet; definability
instance emptyGuard_definable : 𝚺₁-Function₁[V] emptyGuard := by unfold emptyGuard; definability
instance taggedSeq_definable : 𝚺₁-Function₂[V] taggedSeq := by unfold taggedSeq; definability

theorem tagRel_typed (j : V) {n p : V} (hp : IsSemiformula ℒₛₑₜ n p) :
    IsSemiformula ℒₛₑₜ n (tagRel j p) := isSemiformula_relativize (domain_typed j) hp
theorem emptyGuard_typed (j : V) : IsFormula ℒₛₑₜ (emptyGuard j) := (empty_typed j).neg
theorem taggedSeq_typed (j : V) {s : V} (hs : IsFormulaSet ℒₛₑₜ s) :
    IsFormulaSet ℒₛₑₜ (taggedSeq j s) := by
  simp [taggedSeq,tagSet,sideSet,emptyGuard_typed,
    isFormulaSet_relSet (domain_typed j) hs,isFormulaSet_domSet (domain_typed j)]

theorem tagRel_neg (j : V) {p : V} (hp : IsUFormula ℒₛₑₜ p) :
    neg ℒₛₑₜ (tagRel j p)=tagRel j (neg ℒₛₑₜ p) :=
  relativize_neg (domain_typed j).isUFormula hp
theorem tagRel_subst (j : V) {n p : V} (hp : IsSemiformula ℒₛₑₜ n p)
    {a w : V} (hw : IsSemitermVec ℒₛₑₜ n a w) :
    subst ℒₛₑₜ w (tagRel j p)=tagRel j (subst ℒₛₑₜ w p) :=
  relativize_subst (domain_typed j) hp hw
theorem tagRel_substs1 (j : V) {n t p : V} (ht : IsSemiterm ℒₛₑₜ n t)
    (hp : IsSemiformula ℒₛₑₜ 1 p) :
    substs1 ℒₛₑₜ t (tagRel j p)=tagRel j (substs1 ℒₛₑₜ t p) :=
  relativize_substs1 (domain_typed j) ht hp

/-- The domain shifts to the next marker; it is never assumed shift-fixed. -/
theorem tagRel_shift (j : V) {p : V} (hp : IsUFormula ℒₛₑₜ p) :
    shift ℒₛₑₜ (tagRel j p)=tagRel (j+1) (shift ℒₛₑₜ p) := by
  unfold tagRel
  apply IsUFormula.ISigma1.sigma1_succ_induction
    (P := fun p => shift ℒₛₑₜ (relativize ℒₛₑₜ (domainCode j) p)=
      relativize ℒₛₑₜ (domainCode (j+1)) (shift ℒₛₑₜ p)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ p hp
  · definability
  · intro k r v hr hv; simp [hr,hv,hv.termShiftVec]
  · intro k r v hr hv; simp [hr,hv,hv.termShiftVec]
  · simp
  · simp
  · intro p q hp hq ihp ihq
    simp [hp,hq,isUFormula_relativize (domain_typed j).isUFormula hp,
      isUFormula_relativize (domain_typed j).isUFormula hq,hp.shift,hq.shift,ihp,ihq]
  · intro p q hp hq ihp ihq
    simp [hp,hq,isUFormula_relativize (domain_typed j).isUFormula hp,
      isUFormula_relativize (domain_typed j).isUFormula hq,hp.shift,hq.shift,ihp,ihq]
  · intro p hp ihp
    simp [hp,isUFormula_relativize (domain_typed j).isUFormula hp,hp.shift,
      (domain_typed j).isUFormula.neg,ihp,shift_neg (domain_typed j),shift_domain]
  · intro p hp ihp
    simp [hp,isUFormula_relativize (domain_typed j).isUFormula hp,hp.shift,
      (domain_typed j).isUFormula,ihp,shift_domain]

theorem tagRel_free (j : V) {p : V} (hp : IsSemiformula ℒₛₑₜ 1 p) :
    free ℒₛₑₜ (tagRel j p)=tagRel (j+1) (free ℒₛₑₜ p) := by
  simp only [free]
  rw [tagRel_shift j hp.isUFormula,
    tagRel_substs1 (j+1) (show IsSemiterm ℒₛₑₜ 0 (^&0 : V) by simp) hp.shift]

theorem tagSet_shift (j : V) {s : V} (hs : IsFormulaSet ℒₛₑₜ s) :
    setShift ℒₛₑₜ (tagSet j s)=tagSet (j+1) (setShift ℒₛₑₜ s) := by
  apply mem_ext; intro y
  simp only [tagSet,mem_setShift_iff,mem_relSet_iff]
  constructor
  · rintro ⟨z,⟨p,hp,rfl⟩,rfl⟩
    exact ⟨shift ℒₛₑₜ p,⟨p,hp,rfl⟩,tagRel_shift j (hs p hp).isUFormula⟩
  · rintro ⟨z,⟨p,hp,rfl⟩,rfl⟩
    exact ⟨tagRel j p,⟨p,hp,rfl⟩,(tagRel_shift j (hs p hp).isUFormula).symm⟩

theorem emptyGuard_shift (j : V) : shift ℒₛₑₜ (emptyGuard j)=emptyGuard (j+1) := by
  rw [emptyGuard,shift_neg (empty_typed j),shift_empty]; rfl

theorem taggedSeq_insert (j p s : V) :
    taggedSeq j (insert p s)=insert (tagRel j p) (taggedSeq j s) := by
  simp only [taggedSeq,tagSet,relSet_insert]
  apply mem_ext; intro y
  simp only [mem_bitInsert_iff,mem_cup_iff,tagRel]
  tauto

theorem tagRel_mem_seq (j : V) {p s : V} (hp : p∈s) : tagRel j p∈taggedSeq j s := by
  exact mem_bitInsert_iff.mpr (Or.inr (mem_cup_iff.mpr
    (Or.inl (relativize_mem_relSet hp))))

theorem taggedSeq_mono (j : V) {s t : V} (h : s⊆t) : taggedSeq j s⊆taggedSeq j t := by
  intro y hy
  rcases mem_bitInsert_iff.mp hy with rfl|hy
  · simp [taggedSeq]
  · rcases mem_cup_iff.mp hy with hy|hy
    · exact mem_bitInsert_iff.mpr (Or.inr (mem_cup_iff.mpr (Or.inl (relSet_subset h hy))))
    · exact mem_bitInsert_iff.mpr (Or.inr (mem_cup_iff.mpr (Or.inr hy)))

/-- Opening ALL supplies exactly the extra zero-slot side formula. -/
theorem taggedSeq_succ (j : V) {s : V} (hs : IsFormulaSet ℒₛₑₜ s) :
    taggedSeq (j+1) (setShift ℒₛₑₜ s)=
      insert (free ℒₛₑₜ (neg ℒₛₑₜ (domainCode j))) (setShift ℒₛₑₜ (taggedSeq j s)) := by
  simp only [taggedSeq,mem_setShift_insert,mem_setShift_union,
    emptyGuard_shift,tagSet_shift j hs,sideSet_succ]
  apply mem_ext; intro y
  simp only [mem_bitInsert_iff,mem_cup_iff]
  tauto

/-- Every internal term of the set language is a free variable. -/
theorem term_eq_fvar {t : V} (ht : IsTerm ℒₛₑₜ t) : ∃ i : V, t=^&i :=
  SetRelativization.isTerm_eq_fvar ht

theorem exs_label_bound {s p i dp j : V} (hj : exsIntro s p (^&i) dp<j) : i<j :=
  lt_trans (var_lt_qqFvar i) (lt_trans (t_lt_exsIntro s p (^&i) dp) hj)

theorem all_child_budget {child parent j B : V} (hc : child<parent) (hb : parent+j≤B) :
    child+(j+1)≤B := by
  calc
    child+(j+1)=(child+1)+j := by ac_rfl
    _≤parent+j := add_le_add (lt_iff_succ_le.mp hc) le_rfl
    _≤B := hb

theorem predecessor_child_bound {child parent k : V} (hc : child<parent) (hj : parent<k+1) :
    child<k := lt_of_lt_of_le hc (lt_succ_iff_le.mp hj)

private theorem budget_mono {child parent j B : V} (hc : child≤parent) (hb : parent+j≤B) :
    child+j≤B := le_trans (add_le_add hc le_rfl) hb

section Transport
variable {T : SetTheory} [T.Δ₁]

/-- Exactly the still-needed actual source axiom images, with the marker
reserved above that axiom code. This is not a proof-transform premise. -/
def AxiomImages (T : SetTheory) [T.Δ₁] (V : Type*) [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] : Prop :=
  ∀ p j : V, IsFormula ℒₛₑₜ p → p∈T.Δ₁Class → p<j →
    Derivable seedTheory (insert (tagRel j p) (insert (emptyGuard j) (sideSet j)))

/-- Only bounded counter quantifiers occur in the explicit Sigma1 motive. -/
theorem derivable_tagged_bounded (B : V) (hAx : AxiomImages T V) :
    ∀ der : V, Derivation T der → ∀ j≤B,
      der<j → der+j≤B → Derivable seedTheory (taggedSeq j (fstIdx der)) := by
  apply ISigma1.sigma1_order_induction (P := fun der : V =>
    Derivation T der → ∀ j≤B, der<j → der+j≤B →
      Derivable seedTheory (taggedSeq j (fstIdx der)))
  · apply HierarchySymbol.Definable.imp (by definability)
    apply HierarchySymbol.Definable.ball_le (by definability)
    apply HierarchySymbol.Definable.imp (by definability)
    apply HierarchySymbol.Definable.imp (by definability)
    definability
  · intro der ih hd j hjB hdj hb
    have ih_same (child : V) (hc : child<der) (hdchild : Derivation T child) :
        Derivable seedTheory (taggedSeq j (fstIdx child)) :=
      ih child hc hdchild j hjB (lt_trans hc hdj) (budget_mono (le_of_lt hc) hb)
    rcases hd.case with ⟨hseq,
      (⟨s,p,rfl,hp,hn⟩ | ⟨s,rfl,hv⟩ |
       ⟨s,p,q,dp,dq,rfl,hpq,hdp,hdq⟩ |
       ⟨s,p,q,dp,rfl,hpq,hdp⟩ |
       ⟨s,p,dp,rfl,hp,hdp⟩ |
       ⟨s,p,t,dp,rfl,hp,ht,hdp⟩ |
       ⟨s,dp,rfl,hsub,hdp⟩ |
       ⟨s,dp,rfl,hshift,hdp⟩ |
       ⟨s,p,dp,dn,rfl,hdp,hdn⟩ |
       ⟨s,p,rfl,hp,hT⟩)⟩
    -- Logical initial sequent.
    · have hs : IsFormulaSet ℒₛₑₜ s := by simpa only [fstIdx_axL] using hseq
      have hn' : neg ℒₛₑₜ (tagRel j p)∈taggedSeq j s := by
        rw [tagRel_neg j (hs p hp).isUFormula]
        exact tagRel_mem_seq j hn
      simpa only [fstIdx_axL] using
        Derivable.em (taggedSeq_typed j hs) (tagRel j p) (tagRel_mem_seq j hp) hn'
    -- Verum.
    · have hs : IsFormulaSet ℒₛₑₜ s := by simpa only [fstIdx_verumIntro] using hseq
      have hm : (^⊤ : V)∈taggedSeq j s := by
        simpa only [tagRel,relativize_verum] using tagRel_mem_seq j hv
      simpa only [fstIdx_verumIntro] using Derivable.verum (taggedSeq_typed j hs) hm
    -- Conjunction, both children keep marker j.
    · have hs : IsFormulaSet ℒₛₑₜ s := by simpa only [fstIdx_andIntro] using hseq
      have hpqF := IsSemiformula.and.mp (hs _ hpq)
      have hcp := dp_lt_andIntro s p q dp dq
      have hcq := dq_lt_andIntro s p q dp dq
      have ihp := ih_same dp hcp hdp.2
      have ihq := ih_same dq hcq hdq.2
      rw [hdp.1,taggedSeq_insert] at ihp
      rw [hdq.1,taggedSeq_insert] at ihq
      have hm : tagRel j p ^⋏ tagRel j q∈taggedSeq j s := by
        simpa only [tagRel,relativize_and hpqF.1.isUFormula hpqF.2.isUFormula] using tagRel_mem_seq j hpq
      simpa only [fstIdx_andIntro] using Derivable.and_m hm ihp ihq
    -- Disjunction.
    · have hs : IsFormulaSet ℒₛₑₜ s := by simpa only [fstIdx_orIntro] using hseq
      have hpqF := IsSemiformula.or.mp (hs _ hpq)
      have hc := d_lt_orIntro s p q dp
      have ihp := ih_same dp hc hdp.2
      rw [hdp.1,taggedSeq_insert,taggedSeq_insert] at ihp
      have hm : tagRel j p ^⋎ tagRel j q∈taggedSeq j s := by
        simpa only [tagRel,relativize_or hpqF.1.isUFormula hpqF.2.isUFormula] using tagRel_mem_seq j hpq
      simpa only [fstIdx_orIntro] using Derivable.or_m hm ihp
    -- ALL opens the child at marker j+1.
    · have hs : IsFormulaSet ℒₛₑₜ s := by simpa only [fstIdx_allIntro] using hseq
      have hp1 : IsSemiformula ℒₛₑₜ 1 p := by simpa using hs _ hp
      have hc := s_lt_allIntro s p dp
      have hbudget := all_child_budget hc hb
      have hj1 : j+1≤B := le_trans (by simp : j+1≤dp+(j+1)) hbudget
      have ihp := ih dp hc hdp.2 (j+1) hj1 (lt_trans (lt_trans hc hdj) (by simp)) hbudget
      rw [hdp.1,taggedSeq_insert,←tagRel_free j hp1,taggedSeq_succ j hs] at ihp
      have hm : ^∀ (neg ℒₛₑₜ (domainCode j) ^⋎ tagRel j p)∈taggedSeq j s := by
        simpa only [tagRel,relativize_all hp1.isUFormula] using tagRel_mem_seq j hp
      have hswap : Derivable seedTheory
          (insert (free ℒₛₑₜ (neg ℒₛₑₜ (domainCode j)))
            (insert (free ℒₛₑₜ (tagRel j p)) (setShift ℒₛₑₜ (taggedSeq j s)))) := by
        apply Derivable.ofSetEq (fun y => ?_) ihp
        simp only [mem_bitInsert_iff]
        tauto
      simp only [fstIdx_allIntro]
      apply Derivable.all_m hm
      rw [free_or (domain_typed j).neg (tagRel_typed j hp1)]
      exact Derivable.or hswap
    -- EXS uses the actual term/proof coding bounds to find its domain side formula.
    · have hs : IsFormulaSet ℒₛₑₜ s := by simpa only [fstIdx_exsIntro] using hseq
      have hp1 : IsSemiformula ℒₛₑₜ 1 p := by simpa using hs _ hp
      obtain ⟨i,rfl⟩ := term_eq_fvar ht
      have hij : i<j := exs_label_bound hdj
      have hc := d_lt_exsIntro s p (^&i) dp
      have ihp := ih_same dp hc hdp.2
      rw [hdp.1,taggedSeq_insert] at ihp
      have hm : ^∃ (domainCode j ^⋏ tagRel j p)∈taggedSeq j s := by
        simpa only [tagRel,relativize_exs hp1.isUFormula] using tagRel_mem_seq j hp
      have hsub : substs1 ℒₛₑₜ (^&i) (domainCode j ^⋏ tagRel j p)=
          substs1 ℒₛₑₜ (^&i) (domainCode j) ^⋏ tagRel j (substs1 ℒₛₑₜ (^&i) p) := by
        simp only [substs1]
        rw [substs_and (domain_typed j).isUFormula (tagRel_typed j hp1).isUFormula]
        congr 1
        exact tagRel_substs1 j (show IsSemiterm ℒₛₑₜ 0 (^&i : V) by simp) hp1
      simp only [fstIdx_exsIntro]
      apply Derivable.ex_m hm ht
      rw [hsub]
      refine Derivable.and ?_ ihp
      refine Derivable.em (by simp [taggedSeq_typed j hs,
        (domain_typed j).substs1 (show IsSemiterm ℒₛₑₜ 0 (^&i : V) by simp)])
        (substs1 ℒₛₑₜ (^&i) (domainCode j)) (by simp) ?_
      exact mem_bitInsert_iff.mpr (Or.inr (mem_bitInsert_iff.mpr
        (Or.inr (mem_cup_iff.mpr (Or.inr (domF_mem_domSet hij))))))
    -- Weakening.
    · have hs : IsFormulaSet ℒₛₑₜ s := by simpa only [fstIdx_wkRule] using hseq
      have hc := d_lt_wkRule s dp
      have ihp := ih_same dp hc hdp
      simpa only [fstIdx_wkRule] using
        Derivable.wk (taggedSeq_typed j hs) (taggedSeq_mono j hsub) ihp
    -- SHIFT uses an actual predecessor, justified by parent<j.
    · have hs : IsFormulaSet ℒₛₑₜ s := by simpa only [fstIdx_shiftRule] using hseq
      have hc := d_lt_shiftRule s dp
      rcases zero_or_succ j with rfl | ⟨k,rfl⟩
      · simp at hdj
      · have hkB : k≤B := le_trans (by simp) hjB
        have hchild := predecessor_child_bound hc hdj
        have hbudget : dp+k≤B := le_trans
          (add_le_add (le_of_lt hc) (by simp : k≤k+1)) hb
        have ihp := ih dp hc hdp k hkB hchild hbudget
        have hshifted := Derivable.shift ihp
        simp only [fstIdx_shiftRule]
        refine Derivable.wk (taggedSeq_typed (k+1) hs) ?_ hshifted
        intro y hy
        rw [hshift,taggedSeq_succ k hdp.isFormulaSet]
        exact mem_bitInsert_iff.mpr (Or.inr hy)
    -- CUT keeps the same marker in both branches.
    · have hp0 : IsFormula ℒₛₑₜ p := hdp.isFormulaSet p (by simp)
      have hcp := d₁_lt_cutRule s p dp dn
      have hcn := d₂_lt_cutRule s p dp dn
      have ihp := ih_same dp hcp hdp.2
      have ihn := ih_same dn hcn hdn.2
      rw [hdp.1,taggedSeq_insert] at ihp
      rw [hdn.1,taggedSeq_insert,←tagRel_neg j hp0.isUFormula] at ihn
      simpa only [fstIdx_cutRule] using Derivable.cut (tagRel j p) ihp ihn
    -- The actual theory axiom resource, with p<parent<j.
    · have hs : IsFormulaSet ℒₛₑₜ s := by simpa only [fstIdx_axm] using hseq
      have himage := hAx p j (hs p hp) hT (lt_trans (p_lt_axm s p) hdj)
      simp only [fstIdx_axm]
      refine Derivable.wk (taggedSeq_typed j hs) ?_ himage
      intro y hy
      rcases mem_bitInsert_iff.mp hy with rfl|hy
      · exact tagRel_mem_seq j hp
      · rcases mem_bitInsert_iff.mp hy with rfl|hy
        · simp [taggedSeq]
        · exact mem_bitInsert_iff.mpr (Or.inr (mem_cup_iff.mpr (Or.inr hy)))

theorem derivable_tagged (hAx : AxiomImages T V) {der j : V}
    (hd : Derivation T der) (hj : der<j) :
    Derivable seedTheory (taggedSeq j (fstIdx der)) :=
  derivable_tagged_bounded (der+j) hAx der hd j (by simp) hj le_rfl

theorem taggedSeq_falsum (j : V) :
    taggedSeq j (insert (^⊥ : V) ∅)=residual j := by
  have he : tagSet j (∅ : V)=∅ := by
    apply mem_ext; intro y
    simp [tagSet,mem_relSet_iff]
  simp only [taggedSeq,tagSet,relSet_insert,relativize_falsum]
  change insert (emptyGuard j)
    (insert (^⊥ : V) (tagSet j ∅) ∪ sideSet j)=residual j
  rw [he]
  apply mem_ext; intro y
  simp only [residual,emptyGuard,mem_bitInsert_iff,mem_cup_iff,not_mem_empty]
  tauto

/-- Conditional only on the exact internal source axiom images. -/
theorem provable_falsum_of_tagged (hAx : AxiomImages T V)
    (h : Provable T (^⊥ : V)) : Provable seedTheory (^⊥ : V) := by
  obtain ⟨der,hd⟩ := h.toDerivable
  have htag := derivable_tagged hAx hd.2 (show der<der+1 by simp)
  rw [hd.1,taggedSeq_falsum] at htag
  exact provable_falsum_of_residual (der+1) htag

/-- The already proved I-Sigma1 seed interpreter yields an actual C222
history value, retaining precisely the source axiom-image boundary. -/
theorem refutation_witness (hAx : AxiomImages T V)
    (h : Provable T (^⊥ : V)) : ∃ d : V,
      _root_.SetTheory.BusyBeaver.ZFC.ArithmeticHistory222.value d=2 :=
  seedTheory_refutation_witness (provable_falsum_of_tagged hAx h)

end Transport
end LeanProofs.ZFCinPA.ValidatorSeedMarkerRelativization222
