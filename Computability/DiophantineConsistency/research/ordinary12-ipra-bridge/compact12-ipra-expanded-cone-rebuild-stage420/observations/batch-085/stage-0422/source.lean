import DiophantineConsistency.ArithmeticCheckerMachine215
import DiophantineConsistency.FoundationHAConsistencyNormalization
import ZFCinPA.ValidatorConsistency222

/-! # Assembly of the HA equivalence for the maintained current equation

The arithmetic chain from the literal no-zero sentence to Foundation's ZFC
consistency sentence has three links in every model `V` of `𝗜𝚺₁`:

* the **polynomial bridge**: the literal no-zero sentence holds in `V` iff the
  represented decimal215 run never halts in `V`;
* the closed **checker/machine theorem** (`ArithmeticCheckerMachine215`): an
  internal History222 refutation exists iff that run halts;
* the **source bridge**: Foundation's ZFC consistency sentence holds in `V` iff no
  internal History222 refutation exists.

The middle link is already a theorem. This module proves that the two outer
links, stated as explicit all-model propositions, yield an actual `𝗜𝚺₁` (hence `𝗜𝚺₂` and PA)
proof of the source equivalence, and then an actual HA derivation of the
literal unsolvability sentence's equivalence with the ordinary negated ZFC
refutation predicate. The two bridge propositions are premises here; they
are supplied by separate modules. No standard-model truth is promoted to
provability: completeness ranges over every Type0 model of `𝗜𝚺₁`.
-/
set_option autoImplicit false
set_option Elab.async false

namespace DiophantineConsistency.HACurrentAssembly2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC ArithmeticCantor
open HA FoundationPAHFSyntax FoundationZFCConsistencyNat FoundationHADeltaZeroGG

/-- The internal polynomial bridge, at every Type0 model of `𝗜𝚺₁`. -/
def PolynomialBridge : Prop :=
  ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],
    FoundationHACurrentNoZero2011.classicalSentence.Evalb (M := V) ![] ↔
      ¬∃ time : V, first (ArithmeticMachineRun215.run time) = 0

/-- The internal source bridge, at every Type0 model of `𝗜𝚺₁`. -/
def SourceBridge : Prop :=
  ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],
    sourceSentence.Evalb (M := V) ![] ↔
      ¬∃ proof : V, ArithmeticHistory222.checkDef.val.Evalb ![proof, 1]

/-- **The source bridge holds**: in every model of `𝗜𝚺₁`, Foundation's ZFC
consistency sentence is equivalent to the absence of an actual C222 refutation
(`ZFCinPA.ValidatorConsistency222`: accepted refutations decode to internal
ZF refutations, and internal ZFC refutations are interpreted, through ZF, the
quotient-interface theory and the moving-marker seed interpretation, as actual
C222 refutations). -/
theorem sourceBridge : SourceBridge := by
  intro V _ _
  refine (LeanProofs.ZFCinPA.ValidatorConsistency222.consistent_iff_no_refutation222).trans
    (not_congr (exists_congr fun proof => ?_))
  have h := (ArithmeticHistory222.check_defined (V := V)).df ![proof, 1]
  change ArithmeticHistory222.checkDef.val.Evalb ![proof, (1 : V)] ↔
    ArithmeticHistory222.value proof = (1 : V) + 1 at h
  rw [h, one_add_one_eq_two]

/-- The two bridges and the closed checker/machine theorem give the source
equivalence in every model of `𝗜𝚺₁`, hence an actual `𝗜𝚺₁` proof by
completeness. By Parsons' theorem (`𝗜𝚺₁` is Π₂-conservative over PRA) the
equivalence of these two Π₁ sentences is then also provable in primitive
recursive arithmetic. -/
theorem isigma1_proves_current_iff_consistency
    (hp : PolynomialBridge) (hs : SourceBridge) :
    𝗜𝚺₁ ⊢ FoundationHACurrentNoZero2011.classicalSentence 🡘 sourceSentence := by
  apply LO.FirstOrder.Arithmetic.complete.{0} 𝗜𝚺₁ _
  intro M _ hM
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := hM
  have h1 := hp M
  have h2 := hs M
  have h3 := ArithmeticCheckerMachine215.refutation_iff_blank_halts (V := M)
  have hiff : FoundationHACurrentNoZero2011.classicalSentence.Evalb (M := M) ![] ↔
      sourceSentence.Evalb (M := M) ![] :=
    h1.trans ((not_congr h3).symm.trans h2.symm)
  simp only [LogicalConnective.iff, Semantics.And.models_and, Semantics.Imp.models_imply,
    models_iff]
  exact ⟨hiff.1, hiff.2⟩

theorem isigma2_proves_current_iff_consistency
    (hp : PolynomialBridge) (hs : SourceBridge) :
    𝗜𝚺 2 ⊢ FoundationHACurrentNoZero2011.classicalSentence 🡘 sourceSentence :=
  Entailment.weakening (ISigma_weakerThan_of_le (by decide) : 𝗜𝚺₁ ⪯ 𝗜𝚺 2)
    (isigma1_proves_current_iff_consistency hp hs)

theorem peano_proves_current_iff_consistency
    (hp : PolynomialBridge) (hs : SourceBridge) :
    Peano ⊢ FoundationHACurrentNoZero2011.classicalSentence 🡘 sourceSentence :=
  Entailment.weakening (inferInstance : 𝗜𝚺₁ ⪯ Peano)
    (isigma1_proves_current_iff_consistency hp hs)

/-- **The HA endpoint, from the two bridges.** An actual HA derivation of the
equivalence between the literal current unsolvability sentence and the
ordinary negation of the actual positive ZFC refutation predicate. -/
theorem ha_current_iff_consistency
    (hp : PolynomialBridge) (hs : SourceBridge) :
    ProofEquiv ArithmeticCurrentEquation2011.unsolvabilitySentence
      FoundationHAConsistencyNormalization.ordinaryConsistency := by
  have h := FoundationHACurrentTransfer.current_iff_translated
    (peano_proves_current_iff_consistency hp hs)
  have hn := FoundationHAConsistencyNormalization.equivalence
  change ProofEquiv ArithmeticCurrentEquation2011.unsolvabilitySentence ggConsistency at h
  exact (h.and_left.imp_trans hn.and_left).and_intro (hn.and_right.imp_trans h.and_right)

/-- **The HA endpoint, from the polynomial bridge alone.** -/
theorem ha_current_iff_consistency_of_polynomial (hp : PolynomialBridge) :
    ProofEquiv ArithmeticCurrentEquation2011.unsolvabilitySentence
      FoundationHAConsistencyNormalization.ordinaryConsistency :=
  ha_current_iff_consistency hp sourceBridge

end DiophantineConsistency.HACurrentAssembly2011
