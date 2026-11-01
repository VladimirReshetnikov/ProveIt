import ZFCinPA.ValidatorSeedMarkerRelativization222
import ZFCinPA.ValidatorSeedTaggedCollection222
import ZFCinPA.NativeGicDelta1
import ZFCinPA.NativePeel

set_option autoImplicit false
set_option Elab.async false
noncomputable section

/-! Images of the actual GIC recognizer in the moving tagged seed domain.
The matrix is relativized before its two slots are swapped. Arbitrary
internal universal closures use a decreasing marker and Sigma1 induction.
No shift-fixed marker, raw container axiom, quotient or WF image is assumed. -/
namespace LeanProofs.ZFCinPA.ValidatorSeedGicImages222
open Classical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LO.FirstOrder.SetTheory LO.Entailment LO.Entailment.FiniteContext
open LeanProofs.BoundedPAConsistency.InternalRelativization
open ValidatorFullSeedTheory222 ValidatorSeedSourceBasis222 ValidatorSeedMarkerDischarge222
open ValidatorSeedMarkerRelativization222 ValidatorSeedTaggedCollection222
open scoped LO.FirstOrder.Arithmetic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The typed wrapper retains the exact already represented family. -/
def tagged {n : ℕ} (j : V) (p : Semiformula V ℒₛₑₜ n) : Semiformula V ℒₛₑₜ n :=
  ⟨tagRel j p.val,tagRel_typed j p.isSemiformula⟩
@[simp] theorem tagged_val {n : ℕ} (j : V) (p : Semiformula V ℒₛₑₜ n) :
    (tagged j p).val=tagRel j p.val := rfl

def guard (j : V) (n : ℕ) : Semiformula V ℒₛₑₜ (n+1) :=
  memTerm (Bootstrapping.Semiterm.fvar j) (Bootstrapping.Semiterm.bvar 0)
@[simp] theorem guard_val (j : V) (n : ℕ) : (guard j n).val=domainCode j := by
  simp [guard,memTerm,domainCode,memberCode]
  change ((1:ℕ):V)=1
  simp
@[simp] theorem tagged_and {n : ℕ} (j : V) (p q : Semiformula V ℒₛₑₜ n) :
    tagged j (p⋏q)=tagged j p⋏tagged j q := by
  ext; exact relativize_and p.isSemiformula.isUFormula q.isSemiformula.isUFormula
@[simp] theorem tagged_imp {n : ℕ} (j : V) (p q : Semiformula V ℒₛₑₜ n) :
    tagged j (p🡒q)=tagged j p🡒tagged j q := by
  ext
  simp only [tagged_val,Bootstrapping.Semiformula.val_imp,Bootstrapping.imp]
  rw [show tagRel j (neg ℒₛₑₜ p.val ^⋎ q.val)=
      tagRel j (neg ℒₛₑₜ p.val) ^⋎ tagRel j q.val from
      relativize_or p.isSemiformula.isUFormula.neg q.isSemiformula.isUFormula,
    ←tagRel_neg j p.isSemiformula.isUFormula]
@[simp] theorem tagged_all {n : ℕ} (j : V) (p : Semiformula V ℒₛₑₜ (n+1)) :
    tagged j (∀⁰p)=∀⁰(guard j n🡒tagged j p) := by
  ext
  simp only [tagged_val,Bootstrapping.Semiformula.val_all,Bootstrapping.Semiformula.val_imp,
    guard_val,Bootstrapping.imp]
  exact relativize_all p.isSemiformula.isUFormula
@[simp] theorem tagged_exs {n : ℕ} (j : V) (p : Semiformula V ℒₛₑₜ (n+1)) :
    tagged j (∃⁰p)=∃⁰(guard j n⋏tagged j p) := by
  ext
  simp only [tagged_val,Bootstrapping.Semiformula.val_exs,Bootstrapping.Semiformula.val_and,guard_val]
  exact relativize_exs p.isSemiformula.isUFormula
@[simp] theorem tagged_subst {n m : ℕ} (j : V) (p : Semiformula V ℒₛₑₜ n)
    (w : SemitermVec V ℒₛₑₜ n m) : tagged j (p.subst w)=(tagged j p).subst w := by
  ext; exact (tagRel_subst j p.isSemiformula w.isSemitermVec).symm
@[simp] theorem tagged_rel {n k : ℕ} (j : V) (r : (ℒₛₑₜ).Rel k)
    (w : SemitermVec V ℒₛₑₜ k n) :
    tagged j (Semiformula.rel r w)=Semiformula.rel r w := by
  ext
  exact relativize_rel (codeIn_rel_quote r) w.isSemitermVec.isUTerm
@[simp] theorem tagged_mem {n : ℕ} (j : V) (t u : Semiterm V ℒₛₑₜ n) :
    tagged j (memTerm t u)=memTerm t u := tagged_rel j _ _
@[simp] theorem tagged_shift {n : ℕ} (j : V) (p : Semiformula V ℒₛₑₜ n) :
    (tagged j p).shift=tagged (j+1) p.shift := by
  ext; exact tagRel_shift j p.isSemiformula.isUFormula
@[simp] theorem tagged_free (j : V) (p : Semiformula V ℒₛₑₜ 1) :
    (tagged j p).free=tagged (j+1) p.free := by
  ext; exact tagRel_free j (by simp)

/-- Collection uses (output,input); GIC uses (input,output). -/
def swapped (j : V) (K : Semiformula V ℒₛₑₜ 2) : Semiformula V ℒₛₑₜ 2 :=
  (tagged j K).subst ![Bootstrapping.Semiterm.bvar 1,Bootstrapping.Semiterm.bvar 0]
theorem swapped_support (j : V) (K : Semiformula V ℒₛₑₜ 2) :
    (swapped j K).subst ![(Bootstrapping.Semiterm.bvar 1 : Semiterm V ℒₛₑₜ 3),Bootstrapping.Semiterm.bvar 0]=
      (tagged j K).subst ![Bootstrapping.Semiterm.bvar 0,Bootstrapping.Semiterm.bvar 1] := by
  simp [swapped,Bootstrapping.Semiformula.substs_substs,Matrix.vecHead,Matrix.vecTail]
theorem swapped_coverage (j : V) (K : Semiformula V ℒₛₑₜ 2) :
    (swapped j K).subst ![(Bootstrapping.Semiterm.bvar 0 : Semiterm V ℒₛₑₜ 3),Bootstrapping.Semiterm.bvar 1]=
      (tagged j K).subst ![Bootstrapping.Semiterm.bvar 1,Bootstrapping.Semiterm.bvar 0] := by
  simp [swapped,Bootstrapping.Semiformula.substs_substs,Matrix.vecHead,Matrix.vecTail]

private def inner (K : Semiformula V ℒₛₑₜ 2) : Semiformula V ℒₛₑₜ 1 :=
  ∃⁰ ((∀⁰ ((⌜gicAtomYB3⌝ : Semiformula V ℒₛₑₜ 3) 🡒
      ∃⁰ (K.subst ![⌜(#0 : SyntacticSemiterm ℒₛₑₜ 4)⌝,⌜(#1 : SyntacticSemiterm ℒₛₑₜ 4)⌝]))) ⋏
    (∀⁰ ((⌜gicAtomXA3⌝ : Semiformula V ℒₛₑₜ 3) 🡒
      ((∃⁰ (K.subst ![⌜(#1 : SyntacticSemiterm ℒₛₑₜ 4)⌝,⌜(#0 : SyntacticSemiterm ℒₛₑₜ 4)⌝])) 🡒
        ∃⁰ ((⌜gicAtomYB4⌝ : Semiformula V ℒₛₑₜ 4) ⋏
          K.subst ![⌜(#1 : SyntacticSemiterm ℒₛₑₜ 4)⌝,⌜(#0 : SyntacticSemiterm ℒₛₑₜ 4)⌝])))))

/-- Exact opened body, including every quantifier in K and both slot orders. -/
theorem gic_open_binding (j : V) (K : Semiformula V ℒₛₑₜ 2) :
    (guard j 0 🡒 tagged j (inner K)).free=
      (memTerm (Bootstrapping.Semiterm.fvar (j+1)) (Bootstrapping.Semiterm.fvar 0) 🡒
        ∃⁰ collectionBody (swapped (j+1) K.shift)
          (Bootstrapping.Semiterm.fvar 0) (Bootstrapping.Semiterm.fvar (j+1))) := by
  simp [inner,guard,collectionBody,swapped,gicAtomYB3,gicAtomXA3,gicAtomYB4,memTerm,
    Bootstrapping.Semiformula.free,Bootstrapping.Semiformula.shift_substs,
    Bootstrapping.Semiformula.substs_substs,SemitermVec.q,Matrix.vecHead,Matrix.vecTail]

private theorem guarded_generalize (j : V) (X : Semiformula V ℒₛₑₜ 1)
    (h : Source V ⊢ (emptyAt (Bootstrapping.Semiterm.fvar j)).shift 🡒
      (guard j 0 🡒 tagged j X).free) :
    Provable seedTheory (imp ℒₛₑₜ (emptyCode j) (tagRel j (^∀X.val))) := by
  have hg := TProof.generalizeAux h.get
  have hp : Source V ⊢ emptyAt (Bootstrapping.Semiterm.fvar j) 🡒 tagged j (∀⁰ X) := by
    simpa only [tagged_all] using (show Source V ⊢ _ from ⟨hg⟩)
  simpa only [Bootstrapping.Semiformula.val_imp,empty_binding,tagged_val,
    Bootstrapping.Semiformula.val_all] using (tprovable_iff_provable.mp hp)

/-- Every internally typed GIC body has its actual guarded source proof. -/
theorem gic_body_image (K : Semiformula V ℒₛₑₜ 2) (j : V) :
    Provable seedTheory (imp ℒₛₑₜ (emptyCode j) (tagRel j (gicBodyVal K.val))) := by
  have hc := tagged_collection (swapped (j+1) K.shift)
    (Bootstrapping.Semiterm.fvar 0) (Bootstrapping.Semiterm.fvar (j+1))
  have hf : Source V ⊢ (emptyAt (Bootstrapping.Semiterm.fvar j)).shift 🡒
      (guard j 0 🡒 tagged j (inner K)).free := by
    rw [gic_open_binding]
    simpa [emptyAt,memTerm] using hc
  rw [gicBodyVal_eq K]
  simpa only [gicBody,inner,Bootstrapping.Semiformula.val_all] using
    guarded_generalize j (inner K) hf

/-- Close one guarded universal while shifting the free marker correctly. -/
theorem close_step {j x : V} (hx : IsSemiformula ℒₛₑₜ 1 x)
    (h : Provable seedTheory (imp ℒₛₑₜ (emptyCode (j+1)) (tagRel (j+1) (free ℒₛₑₜ x)))) :
    Provable seedTheory (imp ℒₛₑₜ (emptyCode j) (tagRel j (^∀x))) := by
  let X : Semiformula V ℒₛₑₜ 1 := ⟨x,by simpa using hx⟩
  let E : Formula V ℒₛₑₜ := emptyAt (Bootstrapping.Semiterm.fvar j)
  have ht : Source V ⊢ E.shift 🡒 (tagged j X).free :=
    tprovable_iff_provable.mpr (by
      simpa only [Bootstrapping.Semiformula.val_imp,Bootstrapping.Semiformula.val_shift,
        Bootstrapping.Semiformula.free_val,tagged_val,tagRel_free j hx,E,empty_binding,shift_empty,X] using h)
  have hweaken : Source V ⊢ E.shift 🡒 (guard j 0 🡒 tagged j X).free := by
    simp only [Bootstrapping.Semiformula.free,Bootstrapping.Semiformula.shift_imp,
      Bootstrapping.Semiformula.substs_imp] at ht ⊢
    cl_prover [ht]
  simpa only [X] using guarded_generalize j X hweaken

/-- The original body is shift-fixed; the marker is not. The induction
motive has only a bounded antecedent and actual Sigma1 proof existence. -/
theorem close_guarded {m b j : V} (hb : IsSemiformula ℒₛₑₜ m b)
    (hbs : shift ℒₛₑₜ b=b)
    (base : Provable seedTheory (imp ℒₛₑₜ (emptyCode (j+m))
      (tagRel (j+m) (subst ℒₛₑₜ (fvarVec m) b)))) :
    Provable seedTheory (imp ℒₛₑₜ (emptyCode j) (tagRel j (qqAlls b m))) := by
  have key : ∀ i : V, i≤m → Provable seedTheory
      (imp ℒₛₑₜ (emptyCode (j+(m-i)))
        (tagRel (j+(m-i)) (subst ℒₛₑₜ (fvarVec (m-i)) (qqAlls b i)))) := by
    intro i
    induction i using ISigma1.sigma1_succ_induction
    · definability
    case zero => intro _; simpa using base
    case succ i ih =>
      intro hi
      obtain ⟨k,rfl⟩ : ∃ k,m=k+(i+1) := ⟨m-(i+1),(tsub_add_cancel_of_le hi).symm⟩
      have e1 : k+(i+1)-i=k+1 := by
        rw [add_comm i 1,←add_assoc,add_tsub_cancel_right]
      have ih' := ih (le_trans (by simp) hi)
      rw [e1,←add_assoc] at ih'
      rw [add_tsub_cancel_right]
      have hB : IsSemiformula ℒₛₑₜ (k+1) (qqAlls b i) :=
        IsSemiformula.qqAlls (by rwa [add_assoc,add_comm 1 i])
      have hBs : shift ℒₛₑₜ (qqAlls b i)=qqAlls b i := by
        rw [NativePeel.shift_qqAlls hb.isUFormula,hbs]
      have hf := ModelCodedBindFree.fvarVec_isTermVec (L := ℒₛₑₜ) (V := V) k
      have hw : IsSemitermVec ℒₛₑₜ (k+1) 1 (qVec ℒₛₑₜ (fvarVec k)) := by simpa using hf.qVec
      rw [qqAlls_succ,substs_all hB.isUFormula]
      apply close_step (hB.subst hw)
      rwa [NativePeel.free_subst_qVec_fvarVec hB hBs]
  have h := key m le_rfl
  rw [tsub_self,add_zero] at h
  have hc : IsSemiformula ℒₛₑₜ 0 (qqAlls b m) := IsSemiformula.qqAlls (by simpa using hb)
  rwa [subst_eq_self hc (ModelCodedBindFree.fvarVec_isTermVec (L := ℒₛₑₜ) 0) (by simp)] at h

/-- Invert the actual recognizer, with arbitrary internal closure length. -/
theorem recognized_gic_image {p : V} (hp : GicR p) (j : V) :
    Provable seedTheory (imp ℒₛₑₜ (emptyCode j) (tagRel j p)) := by
  obtain ⟨m,_,b,_,rfl,hb,hbs,hbv,K,_,hK,hbody⟩ := hp
  apply close_guarded (isSemiformula_iff.mpr ⟨hb,by rw [hbv]⟩) hbs
  rw [hbody]
  exact gic_body_image ⟨K,hK⟩ (j+m)

/-- Turn a guarded tagged implication into the corresponding axiom image. -/
theorem derivable_of_tagged_imp {p j : V} (hp : IsFormula ℒₛₑₜ p)
    (h : Provable seedTheory (imp ℒₛₑₜ (emptyCode j) (tagRel j p))) :
    Derivable seedTheory (insert (tagRel j p) (insert (emptyGuard j) (sideSet j))) := by
  have he : Derivable seedTheory (insert (emptyCode j) (insert (emptyGuard j) (sideSet j))) :=
    Derivable.em (by simp [empty_typed,emptyGuard_typed,sideSet,isFormulaSet_domSet (domain_typed j)])
      (emptyCode j) (by simp) (by simp [emptyGuard])
  exact NativePeel.derivable_mp (tagRel_typed j hp) h he

/-- A concrete component of the actual moving-marker axiom-image contract. -/
theorem axiomImages_gicTheory : AxiomImages gicTheory V := by
  intro p j hp hmem _
  have hrec : GicR p := by
    change V ⊧/![p] gicCh.val at hmem
    simpa using hmem
  exact derivable_of_tagged_imp hp (recognized_gic_image hrec j)

end LeanProofs.ZFCinPA.ValidatorSeedGicImages222
