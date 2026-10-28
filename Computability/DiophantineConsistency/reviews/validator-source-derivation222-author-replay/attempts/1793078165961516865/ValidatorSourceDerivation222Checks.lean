import ZFCinPA.ValidatorSourceDerivation222

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace LeanProofs.ZFCinPA.ValidatorSourceDerivation222Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCode254
open ValidatorProvability222 ValidatorFormulaEncoder222 ValidatorProofContext222
open ValidatorEnvironmentAlpha222 ValidatorEnvironmentStreams222
open ValidatorEnvironmentLabels254
open ValidatorSourceDerivation222
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem tail_twice (s F : V) (hs : StreamFree s F) :
    StreamFree s (tail (tail F)) := streamFree_tail (streamFree_tail hs)

theorem repeated_label_tail (s x F : V) (hs : StreamFree s (x∷x∷F)) :
    StreamFree s F := by
  simpa only [ValidatorEnvironmentLabels254.tail_cons] using tail_twice s (x∷x∷F) hs

theorem fallback_one_excluded : ¬StreamFree (1 : V) 0 := by
  intro h
  have hne := (h 0).1
  simp at hne

theorem initial_stream : StreamFree (2 : V) 0 := streamFree_of_bounds (by simp) (by simp)

theorem duplicate_enumeration {L S : V} (hL : Enum L S) (p : V) :
    Enum (p∷p∷L) (insert p S) := by
  have h := enum_cons (p := p) (enum_cons (p := p) hL)
  simpa using h

theorem twice_shifted_enumeration {L S : V} (hL : Enum L S) :
    Enum (shiftList (shiftList L)) (setShift ℒₛₑₜ (setShift ℒₛₑₜ S)) :=
  enum_shift (enum_shift hL)

variable {T : SetTheory} [T.Δ₁] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 2]

/-- The actual axiom-image boundary remains an argument of the whole client. -/
theorem internally_sized_witness (hAx : AxOK T V) (d F s L : V)
    (hd : Derivation T d) (hs : StreamFree s F) (hL : Enum L (fstIdx d)) :
    ∃ code : V, ArithmeticHistory222.value code = seqC F s L + 1 :=
  translate hAx d hd F s L hs hL

theorem reenumerate_derivation (hAx : AxOK T V) (d F s L K : V)
    (hd : Derivation T d) (hs : StreamFree s F)
    (hL : Enum L (fstIdx d)) (hK : Enum K (fstIdx d)) :
    CProv (seqC F s K) :=
  (seqC_enum_iff F s hL hK).mp (translate hAx d hd F s L hs hL)

theorem arbitrary_term_source_child (hAx : AxOK T V) (d p t S F s L : V)
    (hd : DerivationOf T d (insert (substs1 ℒₛₑₜ t p) S))
    (hp : IsSemiformula ℒₛₑₜ 1 p) (ht : IsTerm ℒₛₑₜ t)
    (hs : StreamFree s F) (hL : Enum L S) :
    CProv (seqC F s ((^∃ p)∷L)) := by
  have he : Enum (substs1 ℒₛₑₜ t p∷L) (fstIdx d) := by
    rw [hd.1]
    exact enum_cons hL
  exact ValidatorSourceQuantifierContext222.seqC_exs hp ht F s L hs
    (translate hAx d hd.2 F s _ hs he)

theorem internal_proof_value_two (hAx : AxOK T V) {d : V}
    (hd : Proof T d (^⊥ : V)) :
    ∃ code : V, ArithmeticHistory222.value code = 2 :=
  refutation_witness hAx ⟨d,hd⟩

#print axioms streamFree_tail
#print axioms enum_cons
#print axioms enum_shift
#print axioms inv_pi2
#print axioms translate
#print axioms cProv_falsum_of_provable
#print axioms refutation_witness
#print axioms tail_twice
#print axioms repeated_label_tail
#print axioms fallback_one_excluded
#print axioms initial_stream
#print axioms duplicate_enumeration
#print axioms twice_shifted_enumeration
#print axioms internally_sized_witness
#print axioms reenumerate_derivation
#print axioms arbitrary_term_source_child
#print axioms internal_proof_value_two
end LeanProofs.ZFCinPA.ValidatorSourceDerivation222Checks
