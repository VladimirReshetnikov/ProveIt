import ZFCinPA.ValidatorSourceQuantifierContext222

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace LeanProofs.ZFCinPA.ValidatorSourceQuantifierContext222Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCode254
open ValidatorProvability222 ValidatorRelationalCore222 ValidatorFormulaEncoder222
open ValidatorProofContext222 ValidatorEnvironmentAlpha222 ValidatorQuantifierRules222
open ValidatorEnvironmentSubstitution222 ValidatorSourceQuantifierContext222
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem arbitrary_sequent_head (F s L p : V) :
    CProv (seqC F s (p∷L)) ↔ Der (negEnc F s L) (encode F 0 s p) :=
  seqC_cons_iff_der F s L p

theorem nested_source_shift (F s x p : V) (hp : IsSemiformula ℒₛₑₜ 2 p) :
    negEnc (x∷F) s (shiftList ?[^∀ (^∃ p)]) = negEnc F s ?[^∀ (^∃ p)] := by
  apply shifted_context
  intro j hj
  have he : (?[^∀ (^∃ p)] : V).[j] = ^∀ (^∃ p) := by
    have hm := nth_mem_memVec hj
    simpa using hm
  rw [he]
  simpa [one_add_one_eq_two] using hp

section
variable [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 2]

theorem empty_generalization (i g : V) (h : CProv g) : CProv (wal i g) := by
  have hd : Der (0 : V) g := (der_nil g).mpr h
  simpa only [Der,imps_nil] using der_gen i (G := 0) (by simp) hd

theorem duplicate_generalization (i a g : V) (ha : Vac i a)
    (h : Der (a∷a∷0) g) : Der (a∷a∷0) (wal i g) := by
  apply der_gen i (h := h)
  intro j hj
  have hm := nth_mem_memVec hj
  have he : (a∷a∷0 : V).[j] = a := by simpa using hm
  simpa only [he] using ha

theorem internal_vacuity_witness (F s L j : V) (hs : StreamFree s F)
    (hL : ∀ k < len L, IsFormula ℒₛₑₜ L.[k]) (hj : j < len (negEnc F s L)) :
    ∃ d : V, ArithmeticHistory222.value d =
      wim (negEnc F s L).[j] (wal (eigen F s) (negEnc F s L).[j]) + 1 :=
  negEnc_vacuous F s L hs hL j hj

theorem zero_stream_all {p : V} (hp : IsSemiformula ℒₛₑₜ 1 p)
    (F L : V) (hs : StreamFree 0 F)
    (hL : ∀ j < len L, IsFormula ℒₛₑₜ L.[j])
    (h : CProv (seqC (eigen F 0∷F) 0 (free ℒₛₑₜ p∷shiftList L))) :
    ∃ d : V, ArithmeticHistory222.value d = seqC F 0 ((^∀ p)∷L)+1 :=
  seqC_all hp F 0 L hs hL h

theorem fallback_term_context {p : V} (hp : IsSemiformula ℒₛₑₜ 1 p)
    (index s G : V) (hs : StreamFree s (0 : V))
    (h : Der G (encode 0 (1∷0) s p)) : Der G (encode 0 0 s (^∃ p)) := by
  apply ex_intro_term hp (show IsTerm ℒₛₑₜ (^&index : V) by simp) 0 s G hs
  rw [encode_substs1_fvar hp 0 index s]
  simpa only [ValidatorEnvironmentLabels254.freeLabel_nil] using h

theorem repeated_zero_term_context {p : V} (hp : IsSemiformula ℒₛₑₜ 1 p)
    (s G : V) (hs : StreamFree s (0∷0∷0 : V))
    (h : Der G (encode (0∷0∷0) (0∷0) s p)) :
    Der G (encode (0∷0∷0) 0 s (^∃ p)) := by
  apply ex_intro_term hp (show IsTerm ℒₛₑₜ (^&1 : V) by simp) (0∷0∷0) s G hs
  rw [encode_substs1_fvar hp (0∷0∷0) 1 s]
  have he : ValidatorEnvironmentLabels254.freeLabel (0∷0∷0 : V) 1=0 := by
    simpa using ValidatorEnvironmentLabels254.freeLabel_cons_succ (0 : V) (0∷0) 0
  simpa only [he] using h

theorem nested_exs_context {p t : V} (hp : IsSemiformula ℒₛₑₜ 2 p)
    (ht : IsTerm ℒₛₑₜ t) (F s L : V) (hs : StreamFree s F)
    (h : CProv (seqC F s (substs1 ℒₛₑₜ t (^∀ p)∷L))) :
    ∃ d : V, ArithmeticHistory222.value d = seqC F s ((^∃ (^∀ p))∷L)+1 :=
  seqC_exs (show IsSemiformula ℒₛₑₜ 1 (^∀ p) by
    simpa [one_add_one_eq_two] using hp) ht F s L hs h
end

#print axioms cProv_gen_context
#print axioms der_gen
#print axioms negEnc_vacuous
#print axioms negEnc_member_vacuous
#print axioms cProv_gen_source_context
#print axioms shifted_context
#print axioms all_intro_opened
#print axioms all_intro_shifted
#print axioms ex_intro_term
#print axioms seqC_cons_iff_der
#print axioms seqC_all
#print axioms seqC_exs
#print axioms all_context_witness
#print axioms ex_context_witness
#print axioms nested_source_shift
#print axioms empty_generalization
#print axioms duplicate_generalization
#print axioms internal_vacuity_witness
#print axioms zero_stream_all
#print axioms fallback_term_context
#print axioms repeated_zero_term_context
#print axioms nested_exs_context
end LeanProofs.ZFCinPA.ValidatorSourceQuantifierContext222Checks
