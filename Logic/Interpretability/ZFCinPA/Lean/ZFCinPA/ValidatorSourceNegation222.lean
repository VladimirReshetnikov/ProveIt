import ZFCinPA.ValidatorFormulaEncoder222

set_option autoImplicit false
set_option Elab.async false
noncomputable section

/-! Represented source NNF negation agrees with numeric implication-to-false
under the actual C222 theorem predicate. The proof is uniform over internal
typed syntax and arbitrary encoder states. Its code induction has an explicit
Π₂ invariant and uses IΣ2. No freshness, stack length, primitive equality
identification, source-axiom interpretation or closed consistency reduction
is supplied or asserted. R2Neg is a proof guide only, not an import. -/
namespace LeanProofs.ZFCinPA.ValidatorSourceNegation222
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCode254
open ValidatorProvability222 ValidatorFormulaEncoder222
open ValidatorRelationalCore222 (compose contrapose_of double_neg_intro double_neg_elim all_mono)
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Two actual checker implications, not a semantic equivalence premise. -/
def CodeIff (a b : V) : Prop := CProv (wim a b) ∧ CProv (wim b a)
abbrev codeNeg (a : V) : V := wim a 1

def NegEq (F B s p : V) : Prop :=
  CodeIff (encode F B s (Bootstrapping.neg ℒₛₑₜ p)) (codeNeg (encode F B s p))

private abbrev D (G : List V) (p : V) := Kalmar.Der wim CProv G p
private lemma h0 {G : List V} {a : V} : D (a::G) a := .cons_head
private lemma h1 {G : List V} {a b : V} : D (b::a::G) a :=
  .hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..))
private lemma ofDer {p : V} (h : D [] p) : CProv p :=
  h.sound cProv_classical (fun _ hm => absurd hm List.not_mem_nil)
private lemma ded1 {a p : V} (h : D [a] p) : CProv (wim a p) :=
  ofDer (Kalmar.deduction cProv_classical h)
private lemma ded2 {a b p : V} (h : D [b,a] p) : CProv (wim a (wim b p)) :=
  ofDer (Kalmar.deduction cProv_classical (Kalmar.deduction cProv_classical h))
private lemma self_imp (a : V) : CProv (wim a a) := ded1 h0

theorem codeIff_refl (a : V) : CodeIff a a := ⟨self_imp a, self_imp a⟩
theorem codeIff_symm {a b : V} (h : CodeIff a b) : CodeIff b a := ⟨h.2,h.1⟩
theorem codeIff_trans {a b c : V} (h₁ : CodeIff a b) (h₂ : CodeIff b c) :
    CodeIff a c := ⟨compose h₁.1 h₂.1, compose h₂.2 h₁.2⟩

/-- The antecedent implication is reversed in each direction. -/
theorem codeIff_imp {a a' b b' : V} (ha : CodeIff a a') (hb : CodeIff b b') :
    CodeIff (wim a b) (wim a' b') :=
  ⟨ded2 (.mp (.ax hb.1) (.mp h1 (.mp (.ax ha.2) h0))),
   ded2 (.mp (.ax hb.2) (.mp h1 (.mp (.ax ha.1) h0)))⟩

theorem codeIff_neg {a b : V} (h : CodeIff a b) :
    CodeIff (codeNeg a) (codeNeg b) := ⟨contrapose_of h.2, contrapose_of h.1⟩
theorem codeIff_all (i : V) {a b : V} (h : CodeIff a b) :
    CodeIff (wal i a) (wal i b) := ⟨all_mono i h.1, all_mono i h.2⟩
theorem codeIff_doubleNeg (a : V) : CodeIff a (codeNeg (codeNeg a)) :=
  ⟨double_neg_intro a, double_neg_elim a⟩
theorem codeIff_doubleNeg_right {a b : V} (h : CodeIff a b) :
    CodeIff a (codeNeg (codeNeg b)) := codeIff_trans h (codeIff_doubleNeg b)
theorem codeIff_neg_swap {a b : V} (h : CodeIff a (codeNeg b)) :
    CodeIff (codeNeg a) b :=
  codeIff_trans (codeIff_neg h) (codeIff_symm (codeIff_doubleNeg b))

private theorem and_case {a b p q : V}
    (ha : CodeIff a (codeNeg p)) (hb : CodeIff b (codeNeg q)) :
    CodeIff (wim (codeNeg a) b) (codeNeg (codeNeg (wim p (codeNeg q)))) :=
  codeIff_doubleNeg_right (codeIff_imp (codeIff_neg_swap ha) hb)

private theorem or_case {a b p q : V}
    (ha : CodeIff a (codeNeg p)) (hb : CodeIff b (codeNeg q)) :
    CodeIff (codeNeg (wim a (codeNeg b))) (codeNeg (wim (codeNeg p) q)) :=
  codeIff_neg (codeIff_imp ha (codeIff_neg_swap hb))

/-! The universal encoder-state quantifiers make the induction invariant Π₂.
The level promotions below use actual graph definability, not an assumed
uniform proof-translation predicate. -/
omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
private lemma sigma1_to_pi2 {k : ℕ} {P : (Fin k → V) → Prop}
    (h : 𝚺₁.Definable P) : (𝚷-[2]).Definable P := by
  rcases h with ⟨φ,hφ⟩
  refine ⟨.mkPi φ.val (φ.sigma_prop.strict_mono 𝚷 (by decide)),?_⟩
  intro v
  simpa only [HierarchySymbol.Semiformula.val_mkPi] using (hφ.iff (v := v))

private instance cProv_pi2 : 𝚷-[2]-Predicate[V] CProv := sigma1_to_pi2 cProv_definable
private instance encode_sigma2 : 𝚺-[2]-Function₄[V] encode :=
  (encode_defined.graph_delta.to_definable).of_deltaOne
private instance wim_sigma2 : 𝚺-[2]-Function₂[V] wim := wim_defined.to_definable₀
private instance semiformula_sigma2 : 𝚺-[2]-Relation[V] (IsSemiformula ℒₛₑₜ) :=
  IsSemiformula.definable.of_deltaOne
private instance sourceNeg_sigma2 : 𝚺-[2]-Function₁[V] (Bootstrapping.neg ℒₛₑₜ) :=
  (Bootstrapping.neg.defined.graph_delta.to_definable).of_deltaOne

private theorem negEq_pi2 : 𝚷-[2]-Predicate[V]
    (fun p => ∀ n F B s : V, IsSemiformula ℒₛₑₜ n p → NegEq F B s p) := by
  unfold NegEq CodeIff codeNeg
  apply HierarchySymbol.Definable.all
  apply HierarchySymbol.Definable.all
  apply HierarchySymbol.Definable.all
  apply HierarchySymbol.Definable.all
  apply HierarchySymbol.Definable.imp
  · definability
  · definability

/-- Both actual C222 implications for every typed internal source formula.
The environment and binder state are arbitrary; no freshness or size
constraint on either environment is needed. -/
theorem encode_neg [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 2] {n p : V}
    (hp : IsSemiformula ℒₛₑₜ n p) (F B s : V) : NegEq F B s p := by
  have main : ∀ p : V, ∀ n F B s : V, IsSemiformula ℒₛₑₜ n p → NegEq F B s p := by
    apply InductionOnHierarchy.order_induction_sigma 𝚷 2
      (P := fun p => ∀ n F B s : V, IsSemiformula ℒₛₑₜ n p → NegEq F B s p)
    · exact negEq_pi2
    · intro p ih n F B s htyped
      rcases IsSemiformula.case_iff.mp htyped with
        (⟨k,R,v,hr,hv,rfl⟩ | ⟨k,R,v,hr,hv,rfl⟩ | rfl | rfl |
          ⟨p,q,hp,hq,rfl⟩ | ⟨p,q,hp,hq,rfl⟩ | ⟨p,hp,rfl⟩ | ⟨p,hp,rfl⟩)
      · rw [NegEq, neg_rel hr hv.isUTerm, encode_nrel F B s hr hv.isUTerm,
          encode_rel F B s hr hv.isUTerm]
        exact codeIff_refl _
      · rw [NegEq, neg_nrel hr hv.isUTerm, encode_nrel F B s hr hv.isUTerm,
          encode_rel F B s hr hv.isUTerm]
        exact codeIff_doubleNeg _
      · simp only [NegEq, neg_verum, encode_verum, encode_falsum]
        exact ⟨cProv_ex_falso _, ded1 (.mp h0 (.ax cProv_truth))⟩
      · simp only [NegEq, neg_falsum, encode_verum, encode_falsum]
        exact ⟨cProv_mp (cProv_k _ _) (self_imp 1), cProv_mp (cProv_k _ _) cProv_truth⟩
      · have ihp := ih p (by simp) n F B s hp
        have ihq := ih q (by simp) n F B s hq
        rw [NegEq, neg_and hp.isUFormula hq.isUFormula,
          encode_or F B s hp.isUFormula.neg hq.isUFormula.neg,
          encode_and F B s hp.isUFormula hq.isUFormula]
        exact and_case ihp ihq
      · have ihp := ih p (by simp) n F B s hp
        have ihq := ih q (by simp) n F B s hq
        rw [NegEq, neg_or hp.isUFormula hq.isUFormula,
          encode_and F B s hp.isUFormula.neg hq.isUFormula.neg,
          encode_or F B s hp.isUFormula hq.isUFormula]
        exact or_case ihp ihq
      · have ihp := ih p (by simp) (n+1) F (s∷B) (s+2) hp
        rw [NegEq, neg_all hp.isUFormula, encode_exs F B s hp.isUFormula.neg,
          encode_all F B s hp.isUFormula]
        exact codeIff_neg (codeIff_all s (codeIff_neg_swap ihp))
      · have ihp := ih p (by simp) (n+1) F (s∷B) (s+2) hp
        rw [NegEq, neg_ex hp.isUFormula, encode_all F B s hp.isUFormula.neg,
          encode_exs F B s hp.isUFormula]
        exact codeIff_doubleNeg_right (codeIff_all s ihp)
  exact main p n F B s hp

theorem encode_neg_forward [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 2] {n p : V}
    (hp : IsSemiformula ℒₛₑₜ n p) (F B s : V) :
    CProv (wim (encode F B s (Bootstrapping.neg ℒₛₑₜ p)) (codeNeg (encode F B s p))) :=
  (encode_neg hp F B s).1
theorem encode_neg_backward [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 2] {n p : V}
    (hp : IsSemiformula ℒₛₑₜ n p) (F B s : V) :
    CProv (wim (codeNeg (encode F B s p)) (encode F B s (Bootstrapping.neg ℒₛₑₜ p))) :=
  (encode_neg hp F B s).2

theorem encode_neg_witnesses [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 2] {n p : V}
    (hp : IsSemiformula ℒₛₑₜ n p) (F B s : V) :
    ∃ d e : V,
      ArithmeticHistory222.value d =
        wim (encode F B s (Bootstrapping.neg ℒₛₑₜ p)) (codeNeg (encode F B s p)) + 1 ∧
      ArithmeticHistory222.value e =
        wim (codeNeg (encode F B s p)) (encode F B s (Bootstrapping.neg ℒₛₑₜ p)) + 1 := by
  obtain ⟨⟨d,hd⟩,⟨e,he⟩⟩ := encode_neg hp F B s
  exact ⟨d,e,hd,he⟩

end LeanProofs.ZFCinPA.ValidatorSourceNegation222
