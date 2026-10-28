import ZFCinPA.ValidatorSourceNegation222
import ZFCinPA.ValidatorSourceQuantifierContext222

set_option autoImplicit false
set_option Elab.async false
noncomputable section

/-! Actual internal Foundation derivations translate to C222 histories under
an explicit theory-axiom image hypothesis. The invariant is Π₂ and the proof
uses IΣ₂ order induction on the internal derivation code. All source typing,
stream safety, enumeration and quantifier rules are retained. No source axiom
image, closed ZFC reduction or HA equation equivalence is asserted. Historical
R2Main was read as a proof guide only; no R2 module is imported. -/
namespace LeanProofs.ZFCinPA.ValidatorSourceDerivation222
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCode254
open ValidatorProvability222 ValidatorFormulaEncoder222 ValidatorRelationalCore222
open ValidatorEnvironmentVacuity222 ValidatorEnvironmentAlpha222
open ValidatorEnvironmentLabels254
open ValidatorEnvironmentStreams222 ValidatorQuantifierRules222
open ValidatorProofContext222 ValidatorSourceNegation222 ValidatorSourceQuantifierContext222
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Removing the first stored free label preserves the same future stream,
including the fallback label 1. No parity or bound on the stream is added. -/
theorem streamFree_tail {s F : V} (h : StreamFree s F) : StreamFree s (tail F) := by
  rcases nil_or_adjoin F with (rfl | ⟨x,F,rfl⟩)
  · simpa using h
  · simp only [ValidatorEnvironmentLabels254.tail_cons]
    intro k
    refine ⟨(h k).1,?_⟩
    intro j hj
    simpa using (h k).2 (j+1) (by simpa using hj)

theorem enum_cons {L S p : V} (hL : Enum L S) : Enum (p∷L) (insert p S) :=
  enum_of_mem fun y => by simp [hL.mem]

theorem enum_shift {L S : V} (hL : Enum L S) :
    Enum (shiftList L) (setShift ℒₛₑₜ S) :=
  enum_of_mem fun y => by simp only [mem_shiftList,mem_setShift_iff,hL.mem]

private abbrev D (G : List V) (p : V) := Kalmar.Der wim CProv G p
private lemma h0 {G : List V} {a : V} : D (a::G) a := .cons_head
private lemma h1 {G : List V} {a b : V} : D (b::a::G) a :=
  .hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..))
private lemma h2 {G : List V} {a b c : V} : D (c::b::a::G) a :=
  .hyp (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
private lemma ded2 {a b p : V} (h : D [b,a] p) : CProv (wim a (wim b p)) :=
  (Kalmar.deduction cProv_classical (Kalmar.deduction cProv_classical h)).sound
    cProv_classical (fun _ hm => absurd hm List.not_mem_nil)

private lemma or_lemma (a b : V) :
    CProv (wim (wim (codeNeg b) (wim (codeNeg a) 1)) (wim (codeNeg a) b)) :=
  ded2 (.mp (.ax (double_neg_elim b))
    (Kalmar.deduction cProv_classical (.mp (.mp h2 h0) h1)))

/-- The remaining theory-specific obligation, not an assumed logical rule. -/
def AxOK (T : SetTheory) [T.Δ₁] (V : Type*)
    [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] : Prop :=
  ∀ p : V, IsFormula ℒₛₑₜ p → p ∈ T.Δ₁Class →
    ∀ F s : V, StreamFree s F → CProv (encode F 0 s p)

def Inv (T : SetTheory) [T.Δ₁] (d : V) : Prop :=
  Derivation T d → ∀ F s L : V,
    StreamFree s F → Enum L (fstIdx d) → CProv (seqC F s L)

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
private lemma sigma1_to_pi2 {k : ℕ} {P : (Fin k→V)→Prop}
    (h : 𝚺₁.Definable P) : (𝚷-[2]).Definable P := by
  rcases h with ⟨φ,hφ⟩
  refine ⟨.mkPi φ.val (φ.sigma_prop.strict_mono 𝚷 (by decide)),?_⟩
  intro v
  simpa only [HierarchySymbol.Semiformula.val_mkPi] using (hφ.iff (v := v))
omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
private lemma pi1_to_sigma2 {k : ℕ} {P : (Fin k→V)→Prop}
    (h : 𝚷₁.Definable P) : (𝚺-[2]).Definable P := by
  rcases h with ⟨φ,hφ⟩
  refine ⟨.mkSigma φ.val (φ.pi_prop.strict_mono 𝚺 (by decide)),?_⟩
  intro v
  simpa only [HierarchySymbol.Semiformula.val_mkSigma] using (hφ.iff (v := v))

private instance avoid_delta : 𝚫₁-Relation[V] Avoid := by unfold Avoid; definability
private instance free_delta : 𝚫₁-Relation[V] FreeAvoid := by unfold FreeAvoid; definability
private instance streamFree_pi1 : 𝚷₁-Relation[V] StreamFree := by unfold StreamFree; definability
private instance streamFree_sigma2 : 𝚺-[2]-Relation[V] StreamFree :=
  pi1_to_sigma2 streamFree_pi1
private instance cProv_pi2 : 𝚷-[2]-Predicate[V] CProv := sigma1_to_pi2 cProv_definable
private instance seqC_sigma1 : 𝚺₁-Function₃[V] seqC := seqC_defined.to_definable
private instance seqC_sigma2 : 𝚺-[2]-Function₃[V] seqC := seqC_sigma1.of_sigmaOne

variable {T : SetTheory} [T.Δ₁]

/-- The actual invariant's hierarchy certificate, before applying induction. -/
theorem inv_pi2 : 𝚷-[2]-Predicate[V] (Inv T) := by
  unfold Inv
  apply HierarchySymbol.Definable.imp
  · definability
  apply HierarchySymbol.Definable.all
  apply HierarchySymbol.Definable.all
  apply HierarchySymbol.Definable.all
  apply HierarchySymbol.Definable.imp
  · definability
  apply HierarchySymbol.Definable.imp
  · definability
  · definability

section Induction
variable [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 2]

/-- Ten-case interpretation of arbitrary internal source derivations.
Every theory-specific axiom image is supplied only through `hAx`. -/
theorem translate (hAx : AxOK T V) : ∀ d : V, Inv T d := by
  apply InductionOnHierarchy.order_induction_sigma 𝚷 2 (P := Inv T) inv_pi2
  intro d ih hd F s0 L hs hL
  have hmem : ∀ A, A ∈ fstIdx d → codeNeg (encode F 0 s0 A) ∈ᵥ negEnc F s0 L :=
    fun A hA => (mem_negEnc F s0 L _).2 ⟨A,hL.mem.2 hA,rfl⟩
  have hform : ∀ A, A ∈ᵥ L → IsFormula ℒₛₑₜ A :=
    fun A hA => hd.isFormulaSet A (hL.mem.1 hA)
  have hsub : ∀ M, (∀ A, A ∈ᵥ M → A ∈ fstIdx d) →
      ∀ y, y ∈ᵥ negEnc F s0 M → y ∈ᵥ negEnc F s0 L := by
    intro M hM y hy
    obtain ⟨A,hA,rfl⟩ := (mem_negEnc F s0 M y).1 hy
    exact hmem A (hM A hA)
  change Der (negEnc F s0 L) 1
  rcases Derivation.case_iff.mp hd with ⟨hds,
      (⟨S,p,rfl,hps,hnps⟩ | ⟨S,rfl,hsv⟩ |
        ⟨S,p,q,dp,dq,rfl,hpq,h₁,h₂⟩ | ⟨S,p,q,d',rfl,hpq,h'⟩ |
        ⟨S,p,d',rfl,hp,h'⟩ | ⟨S,p,t,d',rfl,hp,ht,h'⟩ |
        ⟨S,d',rfl,hsub',hd'⟩ | ⟨S,d',rfl,hsh,hd'⟩ |
        ⟨S,p,d₁,d₂,rfl,h₁,h₂⟩ | ⟨S,p,rfl,hps,hT⟩)⟩
  -- axL: source NNF negation is transported by an actual C222 implication.
  · simp only [fstIdx_axL] at hmem hds
    have hp : IsFormula ℒₛₑₜ p := hds p hps
    have ne := encode_neg hp F 0 s0
    have d1 := der_mem (hmem _ hnps)
    have d2 := der_mp (der_of (contrapose_of ne.2)) d1
    exact der_mp d2 (der_mem (hmem p hps))
  -- verum
  · simp only [fstIdx_verumIntro] at hmem
    have h := hmem _ hsv
    rw [encode_verum] at h
    exact der_mp (der_mem h) (der_of cProv_truth)
  -- conjunction
  · simp only [fstIdx_andIntro] at hmem hds hL
    have hf := hds _ hpq
    simp only [IsSemiformula.and] at hf
    have Hp : Der (negEnc F s0 L) (encode F 0 s0 p) := by
      apply (seqC_cons_iff_der F s0 L p).mp
      exact ih dp (by simp) h₁.2 F s0 (p∷L) hs (by rw [h₁.1]; exact enum_cons hL)
    have Hq : Der (negEnc F s0 L) (encode F 0 s0 q) := by
      apply (seqC_cons_iff_der F s0 L q).mp
      exact ih dq (by simp) h₂.2 F s0 (q∷L) hs (by rw [h₂.1]; exact enum_cons hL)
    have Hpq := der_mp (der_mp (der_of (conj_rule _ _)) Hp) Hq
    have hm := hmem _ hpq
    rw [encode_and F 0 s0 hf.1.isUFormula hf.2.isUFormula] at hm
    exact der_absurd hm Hpq
  -- disjunction
  · simp only [fstIdx_orIntro] at hmem hds hL
    have hf := hds _ hpq
    simp only [IsSemiformula.or] at hf
    have h := ih d' (by simp) h'.2 F s0 (p∷q∷L) hs
      (by rw [h'.1]; exact enum_cons (enum_cons hL))
    simp only [seqC,negEnc_cons] at h
    change Der (codeNeg (encode F 0 s0 p)∷codeNeg (encode F 0 s0 q)∷negEnc F s0 L) 1 at h
    have H := der_mp (der_of (or_lemma (encode F 0 s0 p) (encode F 0 s0 q)))
      (der_ded (der_ded h))
    have hm := hmem _ hpq
    rw [encode_or F 0 s0 hf.1.isUFormula hf.2.isUFormula] at hm
    exact der_absurd hm H
  -- ALL: the original stream stays safe in the eigen-cons environment.
  · simp only [fstIdx_allIntro] at hmem hds hL
    have hp1 : IsSemiformula ℒₛₑₜ 1 p := by simpa using hds _ hp
    have hen : Enum (free ℒₛₑₜ p∷shiftList L) (insert (free ℒₛₑₜ p) (setShift ℒₛₑₜ S)) :=
      enum_cons (enum_shift hL)
    have h := ih d' (by simp) h'.2 (eigen F s0∷F) s0 _
      (fresh_resources F s0 hs).2.2.1 (by rw [h'.1]; exact hen)
    have H := (seqC_cons_iff_der F s0 L (^∀ p)).mp
      (seqC_all hp1 F s0 L hs (fun j hj => hform _ (nth_mem_memVec hj)) h)
    exact der_absurd (hmem _ hp) H
  -- EXS: arbitrary typed internal terms, no free-variable-only reduction.
  · simp only [fstIdx_exsIntro] at hmem hds hL
    have hp1 : IsSemiformula ℒₛₑₜ 1 p := by simpa using hds _ hp
    have h := ih d' (by simp) h'.2 F s0 _ hs (by rw [h'.1]; exact enum_cons hL)
    have H := (seqC_cons_iff_der F s0 L (^∃ p)).mp (seqC_exs hp1 ht F s0 L hs h)
    exact der_absurd (hmem _ hp) H
  -- weakening
  · simp only [fstIdx_wkRule] at hmem hsub
    obtain ⟨M,hM⟩ := exists_enum (fstIdx d')
    have h := ih d' (by simp) hd' F s0 M hs hM
    exact der_sub (hsub M fun A hA => hsub' (hM.mem.1 hA)) h
  -- free shift
  · simp only [fstIdx_shiftRule] at hmem hsub
    obtain ⟨M,hM⟩ := exists_enum (fstIdx d')
    have hMf : ∀ A, A ∈ᵥ M → IsUFormula ℒₛₑₜ A :=
      fun A hA => (hd'.isFormulaSet A (hM.mem.1 hA)).isUFormula
    have h := ih d' (by simp) hd' (tail F) s0 M (streamFree_tail hs) hM
    change Der (negEnc (tail F) s0 M) 1 at h
    rw [← negEnc_shiftList F s0 M hMf] at h
    refine der_sub (hsub (shiftList M) fun A hA => ?_) h
    obtain ⟨B,hB,rfl⟩ := (mem_shiftList M A).1 hA
    rw [hsh]
    exact mem_setShift_iff.mpr ⟨B,hM.mem.1 hB,rfl⟩
  -- cut
  · simp only [fstIdx_cutRule] at hmem hL
    have hp : IsFormula ℒₛₑₜ p := (h₁.isFormulaSet.insert).1
    have H1 : Der (negEnc F s0 L) (encode F 0 s0 p) := by
      apply (seqC_cons_iff_der F s0 L p).mp
      exact ih d₁ (by simp) h₁.2 F s0 (p∷L) hs (by rw [h₁.1]; exact enum_cons hL)
    have H2 : Der (negEnc F s0 L) (encode F 0 s0 (Bootstrapping.neg ℒₛₑₜ p)) := by
      apply (seqC_cons_iff_der F s0 L _).mp
      exact ih d₂ (by simp) h₂.2 F s0 (Bootstrapping.neg ℒₛₑₜ p∷L) hs
        (by rw [h₂.1]; exact enum_cons hL)
    exact der_mp (der_mp (der_of (encode_neg hp F 0 s0).1) H2) H1
  -- actual theory axiom: the explicit modular boundary is used here only.
  · simp only [fstIdx_axm] at hmem hds
    exact der_absurd (hmem p hps) (der_of (hAx p (hds p hps) hT F s0 hs))

/-- Conditional interpretation of an actual internal source refutation. -/
theorem cProv_falsum_of_provable (hAx : AxOK T V)
    (h : Provable T (^⊥ : V)) : CProv (1 : V) := by
  obtain ⟨d,hd⟩ := h
  have hen : Enum ((^⊥ : V)∷0) (fstIdx d) := by
    rw [hd.1]
    exact enum_of_mem fun y => by rw [singleton_eq_insert]; simp
  have hs : StreamFree (2 : V) 0 := streamFree_of_bounds (by simp) (by simp)
  have h := translate hAx d hd.2 0 2 _ hs hen
  simp only [seqC,negEnc_cons,negEnc_nil,imps_cons,imps_nil,encode_falsum] at h
  exact cProv_mp h (ValidatorProofContext222.self_imp 1)

theorem refutation_witness (hAx : AxOK T V) (h : Provable T (^⊥ : V)) :
    ∃ code : V, ArithmeticHistory222.value code = 2 := by
  simpa [CProv] using cProv_falsum_of_provable hAx h

end Induction
end LeanProofs.ZFCinPA.ValidatorSourceDerivation222
