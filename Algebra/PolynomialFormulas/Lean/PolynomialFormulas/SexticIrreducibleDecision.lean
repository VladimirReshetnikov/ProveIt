import PolynomialFormulas.SexticFactorSearch

/-!
# A total recursive decision for irreducible monic sextics

The collision-free parameter enumeration is guarded by the executable
reducibility test.  Consequently the unbounded search terminates for every
monic sextic, while on irreducible inputs its result is a genuinely separating
pair/triple parameter.
-/

namespace LeanProofs.PolynomialFormulas.SexticIrreducibleDecision

open QuinticRadicalPrimrec
open SexticRadicalDecidability
open SexticRadicalDecidability.MonicSextic
open SexticScalarGaloisBridge
open SexticSeparatingInvariants
open SexticSeparatingSearch
open SexticComputedResolventDecision

def irreducibleB (f : MonicSextic) : Bool :=
  !f.hasBoundedProperFactor

theorem irreducibleB_primrec : Primrec irreducibleB :=
  (Primrec.not.comp
    SexticRadicalDecidability.MonicSextic.hasBoundedProperFactor_primrec).of_eq
      fun _ ↦ rfl

theorem irreducibleB_eq_true (f : MonicSextic) :
    irreducibleB f = true ↔ Irreducible f.ratPolynomial := by
  constructor
  · intro h
    have hfalse : f.hasBoundedProperFactor = false := by
      simpa [irreducibleB] using h
    by_contra hp
    have htrue := f.hasBoundedProperFactor_iff_not_irreducible_map_rat.mpr hp
    rw [htrue] at hfalse
    contradiction
  · intro hp
    have hfalse : f.hasBoundedProperFactor = false := by
      rw [Bool.eq_false_iff]
      intro htrue
      exact f.hasBoundedProperFactor_iff_not_irreducible_map_rat.mp htrue hp
    simp [irreducibleB, hfalse]

noncomputable def pairTotalSearchB (f : MonicSextic) (n : ℕ) : Bool :=
  f.hasBoundedProperFactor || pairSeparatesB f n

noncomputable def tripleTotalSearchB (f : MonicSextic) (n : ℕ) : Bool :=
  f.hasBoundedProperFactor || tripleSeparatesB f n

theorem pairTotalSearchB_computable : Computable₂ pairTotalSearchB := by
  have hred : Computable₂ fun f : MonicSextic ↦ fun _n : ℕ ↦
      f.hasBoundedProperFactor :=
    (hasBoundedProperFactor_primrec.to_comp.comp
      (Computable.fst : Computable (@Prod.fst MonicSextic ℕ))).to₂
  exact (Primrec.or.to_comp.comp hred pairSeparatesB_computable).of_eq
    fun _ ↦ rfl

theorem tripleTotalSearchB_computable : Computable₂ tripleTotalSearchB := by
  have hred : Computable₂ fun f : MonicSextic ↦ fun _n : ℕ ↦
      f.hasBoundedProperFactor :=
    (hasBoundedProperFactor_primrec.to_comp.comp
      (Computable.fst : Computable (@Prod.fst MonicSextic ℕ))).to₂
  exact (Primrec.or.to_comp.comp hred tripleSeparatesB_computable).of_eq
    fun _ ↦ rfl

theorem exists_pairTotalSearchB (f : MonicSextic) :
    ∃ n, pairTotalSearchB f n = true := by
  by_cases hp : Irreducible f.ratPolynomial
  · obtain ⟨n, hn⟩ := exists_pairSeparatesB f hp
    exact ⟨n, by simp [pairTotalSearchB, hn]⟩
  · have hred : f.hasBoundedProperFactor = true :=
      f.hasBoundedProperFactor_iff_not_irreducible_map_rat.mpr hp
    exact ⟨0, by simp [pairTotalSearchB, hred]⟩

theorem exists_tripleTotalSearchB (f : MonicSextic) :
    ∃ n, tripleTotalSearchB f n = true := by
  by_cases hp : Irreducible f.ratPolynomial
  · obtain ⟨n, hn⟩ := exists_tripleSeparatesB f hp
    exact ⟨n, by simp [tripleTotalSearchB, hn]⟩
  · have hred : f.hasBoundedProperFactor = true :=
      f.hasBoundedProperFactor_iff_not_irreducible_map_rat.mpr hp
    exact ⟨0, by simp [tripleTotalSearchB, hred]⟩

noncomputable def pairTotalCode (f : MonicSextic) : ℕ :=
  Nat.find (exists_pairTotalSearchB f)

noncomputable def tripleTotalCode (f : MonicSextic) : ℕ :=
  Nat.find (exists_tripleTotalSearchB f)

theorem pairTotalCode_spec (f : MonicSextic) :
    pairTotalSearchB f (pairTotalCode f) = true :=
  Nat.find_spec (exists_pairTotalSearchB f)

theorem tripleTotalCode_spec (f : MonicSextic) :
    tripleTotalSearchB f (tripleTotalCode f) = true :=
  Nat.find_spec (exists_tripleTotalSearchB f)

theorem pairTotalCode_computable : Computable pairTotalCode := by
  have hpred : ComputablePred fun p : MonicSextic × ℕ ↦
      pairTotalSearchB p.1 p.2 = true :=
    (pairTotalSearchB_computable.of_eq fun p ↦ by
      cases h : pairTotalSearchB p.1 p.2 <;> simp [h]).computablePred
  exact Computable.find hpred exists_pairTotalSearchB

theorem tripleTotalCode_computable : Computable tripleTotalCode := by
  have hpred : ComputablePred fun p : MonicSextic × ℕ ↦
      tripleTotalSearchB p.1 p.2 = true :=
    (tripleTotalSearchB_computable.of_eq fun p ↦ by
      cases h : tripleTotalSearchB p.1 p.2 <;> simp [h]).computablePred
  exact Computable.find hpred exists_tripleTotalSearchB

noncomputable def pairTotalParameter (f : MonicSextic) : Fin 2 → ℕ :=
  parameterAt (pairTotalCode f)

noncomputable def tripleTotalParameter (f : MonicSextic) : Fin 2 → ℕ :=
  parameterAt (tripleTotalCode f)

theorem pairTotalParameter_computable : Computable pairTotalParameter :=
  parameterAt_primrec.to_comp.comp pairTotalCode_computable

theorem tripleTotalParameter_computable : Computable tripleTotalParameter :=
  parameterAt_primrec.to_comp.comp tripleTotalCode_computable

theorem pairTotalParameter_injective (f : MonicSextic)
    (hp : Irreducible f.ratPolynomial) :
    Function.Injective
      (pairDescriptorValue (pairTotalParameter f)
        (rootTuple f.ratPolynomial hp f.ratPolynomial_natDegree)) := by
  rw [← pairCollisionValue_rootTuple_ne_zero_iff f hp]
  apply pairSeparatesB_eq_true f (pairTotalCode f) |>.mp
  have hsearch := pairTotalCode_spec f
  have hred : f.hasBoundedProperFactor = false := by
    rw [Bool.eq_false_iff]
    intro htrue
    exact f.hasBoundedProperFactor_iff_not_irreducible_map_rat.mp htrue hp
  simpa [pairTotalSearchB, pairTotalParameter, hred] using hsearch

theorem tripleTotalParameter_injective (f : MonicSextic)
    (hp : Irreducible f.ratPolynomial) :
    Function.Injective
      (tripleDescriptorValue (tripleTotalParameter f)
        (rootTuple f.ratPolynomial hp f.ratPolynomial_natDegree)) := by
  rw [← tripleCollisionValue_rootTuple_ne_zero_iff f hp]
  apply tripleSeparatesB_eq_true f (tripleTotalCode f) |>.mp
  have hsearch := tripleTotalCode_spec f
  have hred : f.hasBoundedProperFactor = false := by
    rw [Bool.eq_false_iff]
    intro htrue
    exact f.hasBoundedProperFactor_iff_not_irreducible_map_rat.mp htrue hp
  simpa [tripleTotalSearchB, tripleTotalParameter, hred] using hsearch

noncomputable def irreducibleSolvableB (f : MonicSextic) : Bool :=
  resolventSolvableB
    (f, pairTotalParameter f, tripleTotalParameter f)

theorem irreducibleSolvableB_computable : Computable irreducibleSolvableB := by
  exact resolventSolvableB_computable.comp <|
    Computable.pair Computable.id <|
      Computable.pair pairTotalParameter_computable
        tripleTotalParameter_computable

theorem irreducibleSolvableB_correct (f : MonicSextic)
    (hp : Irreducible f.ratPolynomial) :
    irreducibleSolvableB f = true ↔ IsSolvable f.ratPolynomial.Gal := by
  exact resolventSolvableB_correct f hp
    (pairTotalParameter f) (tripleTotalParameter f)
    (pairTotalParameter_injective f hp)
    (tripleTotalParameter_injective f hp)

end LeanProofs.PolynomialFormulas.SexticIrreducibleDecision
