import ZFCinPA.ModelCodedDecoderRho1_254

set_option autoImplicit false

/-!
The two gated atomic-vacuity clauses in the actual numerical bundle. Both
label inequalities remain explicit; the two atomic arguments may coincide.
Finite target generalization uses proved syntactic binder invariance, with
no theory axiom, GEN resource, closed-matrix or standard-code premise.
-/
namespace LeanProofs.ZFCinPA.ModelCodedDecoderAtomicVacuity254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping LO.FirstOrder.SetTheory
open LO.Entailment
open LeanProofs.ZFCinPA.ModelCodedBindOne
open LeanProofs.ZFCinPA.ModelCodedBinderAbsorption
open LeanProofs.ZFCinPA.ModelCodedDecoder254
open LeanProofs.ZFCinPA.ModelCodedDecoderLukasiewicz254
open LeanProofs.ZFCinPA.ModelCodedDecoderRho2_254
open LeanProofs.ZFCinPA.ModelCodedDecoderEquality254
open LeanProofs.ZFCinPA.ModelCodedDecoderRho1_254
open _root_.SetTheory.BusyBeaver.ZFC
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local prefix:max "&'" => Bootstrapping.Semiterm.fvar (V := V) (L := ℒₛₑₜ)

lemma namedBody_memAtom (a b c : V) :
    namedBody a (memAtom (&'b) (&'c)) = memAtom (namedVar a b) (namedVar a c) := by
  classical
  have hr : (ℒₛₑₜ).IsRel (2 : V) 1 := by
    simpa using (isRel_quote_quote (V := V) (L := ℒₛₑₜ) (k := 2) (x := 1)).mpr
      ⟨Language.Set.Rel.mem,rfl⟩
  have hv : IsUTermVec ℒₛₑₜ (2 : V) ?[^&b,^&c] := by simp
  apply Bootstrapping.Semiformula.ext
  change bindOneAt ℒₛₑₜ a 0 (^rel 2 ((1 : Nat) : V) ?[^&b,^&c]) =
    ^rel 2 ((1 : Nat) : V) ?[(namedVar a b).val,(namedVar a c).val]
  rw [Nat.cast_one]
  rw [bindOneAt_rel a 0 hr hv,termBindOneVecAt_pair a 0 _ _ (by simp) (by simp)]
  by_cases hb : b = a <;> by_cases hc : c = a <;>
    simp [namedVar,termBindOneAt_fvar,hb,hc]

lemma namedBody_free_of_bindOne (chosen : V) (p : Formula V ℒₛₑₜ)
    (h : bindOneAt ℒₛₑₜ chosen 0 p.val = p.val) :
    (namedBody chosen p).free = p.shift := by
  apply Bootstrapping.Semiformula.ext
  change free ℒₛₑₜ (bindOneAt ℒₛₑₜ chosen 0 p.val) = shift ℒₛₑₜ p.val
  rw [h]
  exact free_formula p.isSemiformula

noncomputable def namedFormula_vacuous_of_bindOne (T : InternalTheory V ℒₛₑₜ)
    (chosen : V) (p : Formula V ℒₛₑₜ)
    (h : bindOneAt ℒₛₑₜ chosen 0 p.val = p.val) :
    T ⊢! p 🡒 namedFormula chosen p := by
  apply TProof.generalizeAux
  rw [namedBody_free_of_bindOne chosen p h]
  exact C_id

lemma bindOneAt_eqAtom_of_ne (a b c : V) (hca : c ≠ a) (hcb : c ≠ b) :
    bindOneAt ℒₛₑₜ c 0 (eqAtom (&'a) (&'b) : Formula V ℒₛₑₜ).val =
      (eqAtom (&'a) (&'b) : Formula V ℒₛₑₜ).val := by
  have h := congrArg Bootstrapping.Semiformula.val (namedBody_eqAtom c a b)
  simpa [namedBody,namedVar,Ne.symm hca,Ne.symm hcb,eqAtom] using h

lemma bindOneAt_memAtom_of_ne (a b c : V) (hca : c ≠ a) (hcb : c ≠ b) :
    bindOneAt ℒₛₑₜ c 0 (memAtom (&'a) (&'b) : Formula V ℒₛₑₜ).val =
      (memAtom (&'a) (&'b) : Formula V ℒₛₑₜ).val := by
  have h := congrArg Bootstrapping.Semiformula.val (namedBody_memAtom c a b)
  simpa [namedBody,namedVar,Ne.symm hca,Ne.symm hcb,memAtom] using h

noncomputable def namedFormula_eq_vacuous (T : InternalTheory V ℒₛₑₜ)
    (a b c : V) (hca : c ≠ a) (hcb : c ≠ b) :
    T ⊢! eqAtom (&'a) (&'b) 🡒 namedFormula c (eqAtom (&'a) (&'b)) :=
  namedFormula_vacuous_of_bindOne T c _ (bindOneAt_eqAtom_of_ne a b c hca hcb)

noncomputable def namedFormula_mem_vacuous (T : InternalTheory V ℒₛₑₜ)
    (a b c : V) (hca : c ≠ a) (hcb : c ≠ b) :
    T ⊢! memAtom (&'a) (&'b) 🡒 namedFormula c (memAtom (&'a) (&'b)) :=
  namedFormula_vacuous_of_bindOne T c _ (bindOneAt_memAtom_of_ne a b c hca hcb)

theorem decoded_vacuity_of_bindOne (T : SetTheory) [T.Δ₁] (chosen n : V)
    (h : bindOneAt ℒₛₑₜ chosen 0 (decode n) = decode n) :
    Provable T (decode (ArithmeticCode254.wim n (ArithmeticCode254.wal chosen n))) := by
  apply (tprovable_iff_provable (σ := decoded _)).mp
  have he : T.internalize V ⊢
      decoded (ArithmeticCode254.wim n (ArithmeticCode254.wal chosen n)) 🡘
        (decoded n 🡒 namedFormula chosen (decoded n)) := by
    rw [ArithmeticCode254.wim,ArithmeticCode254.tagged,add_zero]
    apply decoded_imp_congr
    · exact ⟨E_Id⟩
    · rw [namedFormula_decoded]
      exact ⟨E_Id⟩
  exact (iff_of_E! he).mpr ⟨namedFormula_vacuous_of_bindOne (T.internalize V) chosen (decoded n) h⟩

theorem decoded_weq_vacuity (T : SetTheory) [T.Δ₁]
    (a b c : V) (hca : c ≠ a) (hcb : c ≠ b) :
    Provable T (decode (ArithmeticCode254.wim (ArithmeticCode254.weq a b)
      (ArithmeticCode254.wal c (ArithmeticCode254.weq a b)))) := by
  apply decoded_vacuity_of_bindOne T c
  change bindOneAt ℒₛₑₜ c 0 (decoded (ArithmeticCode254.weq a b)).val =
    (decoded (ArithmeticCode254.weq a b)).val
  rw [decoded_weq]
  exact bindOneAt_eqAtom_of_ne a b c hca hcb

theorem decoded_wel_vacuity (T : SetTheory) [T.Δ₁]
    (a b c : V) (hca : c ≠ a) (hcb : c ≠ b) :
    Provable T (decode (ArithmeticCode254.wim (ArithmeticCode254.wel a b)
      (ArithmeticCode254.wal c (ArithmeticCode254.wel a b)))) := by
  apply decoded_vacuity_of_bindOne T c
  change bindOneAt ℒₛₑₜ c 0 (decoded (ArithmeticCode254.wel a b)).val =
    (decoded (ArithmeticCode254.wel a b)).val
  rw [decoded_wel]
  exact bindOneAt_memAtom_of_ne a b c hca hcb

end LeanProofs.ZFCinPA.ModelCodedDecoderAtomicVacuity254
