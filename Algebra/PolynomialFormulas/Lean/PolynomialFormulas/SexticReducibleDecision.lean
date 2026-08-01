import PolynomialFormulas.SexticIrreducibleDecision
import PolynomialFormulas.QuinticRadicalDecision

/-!
# Recursive reducible branch for monic sextics

Quadratic and cubic factors leave only factors of degree at most four.  A
linear factor leaves a monic quintic quotient, which is handed to the already
verified quintic decision procedure.
-/

open Polynomial IntermediateField
open Denumerable Encodable Function

namespace LeanProofs.PolynomialFormulas.SexticReducibleDecision

open QuinticRadicalComputability
open QuinticRadicalDecidability
open QuinticRadicalDecision
open QuinticRadicalPrimrec
open FrobeniusDummitResolvent
open QuinticDummitCoefficients
open QuinticScalarGaloisBridge
open QuinticScalarResolventCriterion
open LowDegreeRadicals
open SexticRadicalDecidability
open SexticRadicalDecidability.MonicSextic
open SexticIrreducibleDecision

def linearWitnessB (f : MonicSextic) (n : ℕ) : Bool :=
  decide (n < symmetricCodeBound f.rootBound ∧
    f.linearRemainderZero (ofNat ℤ n))

def linearTotalSearchB (f : MonicSextic) (n : ℕ) : Bool :=
  !f.hasBoundedLinearFactor || linearWitnessB f n

theorem linearWitnessB_primrec : Primrec₂ linearWitnessB := by
  have hbound : Primrec fun f : MonicSextic ↦ symmetricCodeBound f.rootBound :=
    symmetricCodeBound_primrec.comp rootBound_primrec
  have hlt : PrimrecPred fun p : MonicSextic × ℕ ↦
      p.2 < symmetricCodeBound p.1.rootBound :=
    Primrec.nat_lt.comp Primrec.snd (hbound.comp Primrec.fst)
  have hrem : PrimrecPred fun p : MonicSextic × ℕ ↦
      p.1.linearRemainderZero (ofNat ℤ p.2) :=
    MonicSextic.linearRemainderZero_primrec.comp Primrec.fst
      ((Primrec.ofNat ℤ).comp Primrec.snd)
  exact (hlt.and hrem).decide.of_eq fun _ ↦ rfl

theorem linearTotalSearchB_primrec : Primrec₂ linearTotalSearchB := by
  have hnone : Primrec₂ fun f : MonicSextic ↦ fun _n : ℕ ↦
      !f.hasBoundedLinearFactor :=
    (Primrec.not.comp
      (MonicSextic.hasBoundedLinearFactor_primrec.comp Primrec.fst)).to₂
  exact (Primrec.or.comp hnone linearWitnessB_primrec).of_eq fun _ ↦ rfl

theorem exists_linearTotalSearchB (f : MonicSextic) :
    ∃ n, linearTotalSearchB f n = true := by
  by_cases hlin : f.hasBoundedLinearFactor = true
  · have hlinTrue := hlin
    rw [MonicSextic.hasBoundedLinearFactor_iff_dvd] at hlin
    rcases hlin with ⟨c, hc, hdvd⟩
    refine ⟨Equiv.intEquivNat c, ?_⟩
    have hbound :=
      (intEquivNat_lt_iff_mem_symmetricInterval c f.rootBound).mpr hc
    have hrem := (f.linearRemainderZero_iff_dvd c).mpr hdvd
    simp [linearTotalSearchB, linearWitnessB, hlinTrue]
    exact ⟨hbound, by simpa using hrem⟩
  · have hfalse : f.hasBoundedLinearFactor = false := by
      cases h : f.hasBoundedLinearFactor <;> simp_all
    exact ⟨0, by simp [linearTotalSearchB, hfalse]⟩

noncomputable def linearTotalCode (f : MonicSextic) : ℕ :=
  Nat.find (exists_linearTotalSearchB f)

theorem linearTotalCode_spec (f : MonicSextic) :
    linearTotalSearchB f (linearTotalCode f) = true :=
  Nat.find_spec (exists_linearTotalSearchB f)

theorem linearTotalCode_computable : Computable linearTotalCode := by
  have hpred : ComputablePred fun p : MonicSextic × ℕ ↦
      linearTotalSearchB p.1 p.2 = true :=
    (linearTotalSearchB_primrec.to_comp.of_eq fun p ↦ by
      cases h : linearTotalSearchB p.1 p.2 <;> simp [h]).computablePred
  exact Computable.find hpred exists_linearTotalSearchB

noncomputable def selectedLinearCoeff (f : MonicSextic) : ℤ :=
  ofNat ℤ (linearTotalCode f)

theorem selectedLinearCoeff_computable : Computable selectedLinearCoeff :=
  (Primrec.ofNat ℤ).to_comp.comp linearTotalCode_computable

theorem selectedLinearCoeff_spec (f : MonicSextic)
    (hlin : f.hasBoundedLinearFactor = true) :
    f.linearRemainderZero (selectedLinearCoeff f) := by
  have h := linearTotalCode_spec f
  simp [linearTotalSearchB, hlin, linearWitnessB,
    selectedLinearCoeff] at h
  exact h.2

/-- Ascending coefficients of the monic quintic quotient selected by the
first bounded linear factor. -/
def linearQuotientCoefficients
    (p : MonicSextic × ℤ) : QuinticRadicalComputability.Coefficients :=
  fun i ↦ match i with
    | 0 => p.1.linearQ0 p.2
    | 1 => p.1.linearQ1 p.2
    | 2 => p.1.linearQ2 p.2
    | 3 => p.1.linearQ3 p.2
    | 4 => p.1.linearQ4 p.2
    | 5 => 1

theorem linearQuotientCoefficients_apply_primrec (i : Fin 6) :
    Primrec fun p : MonicSextic × ℤ ↦ linearQuotientCoefficients p i := by
  fin_cases i
  · exact MonicSextic.linearQ0_primrec
  · exact MonicSextic.linearQ1_primrec
  · exact MonicSextic.linearQ2_primrec
  · exact MonicSextic.linearQ3_primrec
  · exact MonicSextic.linearQ4_primrec
  · exact Primrec.const 1

theorem linearQuotientCoefficients_primrec :
    Primrec linearQuotientCoefficients := by
  apply Primrec.fin_curry.mpr
  exact (Primrec.fin_curry₁.mpr
    linearQuotientCoefficients_apply_primrec).swap

noncomputable def selectedQuintic
    (f : MonicSextic) : QuinticRadicalComputability.Coefficients :=
  linearQuotientCoefficients (f, selectedLinearCoeff f)

theorem selectedQuintic_computable : Computable selectedQuintic :=
  linearQuotientCoefficients_primrec.to_comp.comp
    (Computable.pair Computable.id selectedLinearCoeff_computable)

@[simp] theorem linearQuotientCoefficients_leading
    (p : MonicSextic × ℤ) : linearQuotientCoefficients p 5 = 1 := rfl

theorem linearQuotientCoefficients_intPolynomial
    (f : MonicSextic) (c : ℤ) :
    QuinticRadicalComputability.intPolynomial
        (linearQuotientCoefficients (f, c)) =
      f.linearQuotient c := by
  simp [QuinticRadicalComputability.intPolynomial,
    IntegerQuintic.polynomial, linearQuotientCoefficients,
    MonicSextic.linearQuotient]

theorem linearQuotientCoefficients_ratPolynomial
    (f : MonicSextic) (c : ℤ) :
    QuinticRadicalComputability.ratPolynomial
        (linearQuotientCoefficients (f, c)) =
      (f.linearQuotient c).map (Int.castRingHom ℚ) := by
  rw [QuinticRadicalComputability.ratPolynomial,
    linearQuotientCoefficients_intPolynomial]

/-! ## A trust-clean recursive quintic subroutine

For the linear-factor branch we use the abstract symmetric-polynomial
coefficients directly.  Their evaluation is proved primitive recursive by
structural induction on the fixed coefficient polynomials.  This avoids
making the final sextic theorem depend on the older, large
`native_decide`-checked sparse-table certificates. -/

theorem dummitCoefficients_hasRationalRoot_iff_gal_isSolvable
    (f : MonicQuintic)
    (hp : Irreducible (monicQuinticRatPolynomial f)) :
    (dummitCoefficients f).HasRationalRoot ↔
      IsSolvable (monicQuinticRatPolynomial f).Gal := by
  let p := monicQuinticRatPolynomial f
  let L := p.SplittingField
  let A := dummitCoefficients f
  let r := rootTuple p hp (monicQuinticRatPolynomial_natDegree f)
  have hmap : A.polynomial.map (Int.castRingHom L) = scalarResolvent r := by
    exact dummitPolynomial_map_eq_scalarResolvent_rootTuple f hp
  have hpolyMap :
      (A.polynomial.map (Int.castRingHom ℚ)).map (algebraMap ℚ L) =
        A.polynomial.map (Int.castRingHom L) := by
    rw [Polynomial.map_map]
    congr 1
  rw [← scalarResolvent_has_rational_root_iff_gal_isSolvable
    p hp (monicQuinticRatPolynomial_natDegree f)]
  constructor
  · rintro ⟨q, hq⟩
    have hq' : (A.polynomial.map (Int.castRingHom ℚ)).IsRoot q := by
      simpa [A, Polynomial.IsRoot, Polynomial.eval_map,
        Polynomial.aeval_def, RingHom.eq_intCast' (algebraMap ℤ ℚ)] using hq
    have hqL := Polynomial.IsRoot.map (f := algebraMap ℚ L) hq'
    rw [hpolyMap, hmap] at hqL
    exact ⟨q, hqL⟩
  · rintro ⟨q, hq⟩
    rw [← hmap, ← hpolyMap] at hq
    have hq' := hq.of_map (algebraMap ℚ L).injective
    refine ⟨q, ?_⟩
    simpa [A, Polynomial.IsRoot, Polynomial.eval_map,
      Polynomial.aeval_def, RingHom.eq_intCast' (algebraMap ℤ ℚ)] using hq'

noncomputable def recursiveDummitCriterion (f : MonicQuintic) : Bool :=
  (dummitCoefficients f).rationalRootSearch

theorem recursiveDummitCriterion_primrec : Primrec recursiveDummitCriterion :=
  IntegerSextic.rationalRootSearch_primrec.comp dummitCoefficients_primrec

theorem recursiveDummitCriterion_correct (f : MonicQuintic)
    (hp : Irreducible (f.polynomial.map (Int.castRingHom ℚ))) :
    recursiveDummitCriterion f = true ↔
      IsSolvable (f.polynomial.map (Int.castRingHom ℚ)).Gal := by
  change (dummitCoefficients f).rationalRootSearch = true ↔
    IsSolvable (monicQuinticRatPolynomial f).Gal
  rw [(dummitCoefficients f).rationalRootSearch_iff_hasRationalRoot (by simp),
    dummitCoefficients_hasRationalRoot_iff_gal_isSolvable f
      (by simpa [monicQuinticRatPolynomial] using hp)]

noncomputable def recursiveQuinticRadicalDecision :
    QuinticRadicalComputability.Coefficients → Bool :=
  decisionWith recursiveDummitCriterion

theorem recursiveQuinticRadicalDecision_primrec :
    Primrec recursiveQuinticRadicalDecision :=
  decisionWith_primrec recursiveDummitCriterion
    recursiveDummitCriterion_primrec

theorem recursiveQuinticRadicalDecision_correct
    (a : QuinticRadicalComputability.Coefficients) :
    recursiveQuinticRadicalDecision a = true ↔
      QuinticRadicalComputability.AllRootsRadical a :=
  decisionWith_correct recursiveDummitCriterion
    recursiveDummitCriterion_correct a

/-! ## Radical semantics of the factor branches -/

theorem completelySolvableByRadicals_mul_of_natDegree_le_four
    {A B : ℚ[X]} (hA0 : A ≠ 0) (hB0 : B ≠ 0)
    (hAdeg : A.natDegree ≤ 4) (hBdeg : B.natDegree ≤ 4) :
    CompletelySolvableByRadicals (A * B) := by
  intro x
  have hx : A.aeval (x : ℂ) * B.aeval (x : ℂ) = 0 := by
    rw [← map_mul]
    exact aeval_eq_zero_of_mem_rootSet x.property
  rcases mul_eq_zero.mp hx with hxA | hxB
  · let y : A.rootSet ℂ := ⟨x, (mem_rootSet_of_ne hA0).2 hxA⟩
    exact root_mem_of_natDegree_le_four hAdeg y
  · let y : B.rootSet ℂ := ⟨x, (mem_rootSet_of_ne hB0).2 hxB⟩
    exact root_mem_of_natDegree_le_four hBdeg y

theorem completelySolvableByRadicals_mul_iff_right
    {A B : ℚ[X]} (hA0 : A ≠ 0) (hB0 : B ≠ 0)
    (hAdeg : A.natDegree ≤ 4) :
    CompletelySolvableByRadicals (A * B) ↔
      CompletelySolvableByRadicals B := by
  constructor
  · intro h x
    let y : (A * B).rootSet ℂ :=
      ⟨x, (mem_rootSet_of_ne (mul_ne_zero hA0 hB0)).2 <| by
        rw [map_mul, aeval_eq_zero_of_mem_rootSet x.property, mul_zero]⟩
    exact h y
  · intro h x
    have hx : A.aeval (x : ℂ) * B.aeval (x : ℂ) = 0 := by
      rw [← map_mul]
      exact aeval_eq_zero_of_mem_rootSet x.property
    rcases mul_eq_zero.mp hx with hxA | hxB
    · let y : A.rootSet ℂ := ⟨x, (mem_rootSet_of_ne hA0).2 hxA⟩
      exact root_mem_of_natDegree_le_four hAdeg y
    · let y : B.rootSet ℂ := ⟨x, (mem_rootSet_of_ne hB0).2 hxB⟩
      exact h y

theorem completelySolvableByRadicals_of_monic_degree_six_of_monic_divisor
    {P A : ℚ[X]} (hPmonic : P.Monic) (hPdeg : P.natDegree = 6)
    (hAmonic : A.Monic) (hAdeg : A.natDegree = 2 ∨ A.natDegree = 3)
    (hdiv : A ∣ P) : CompletelySolvableByRadicals P := by
  obtain ⟨B, hPB⟩ := hdiv
  have hA0 : A ≠ 0 := hAmonic.ne_zero
  have hB0 : B ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hPB
    exact hPmonic.ne_zero hPB
  have hsum : A.natDegree + B.natDegree = 6 := by
    rw [← Polynomial.natDegree_mul hA0 hB0, ← hPB, hPdeg]
  have hAle : A.natDegree ≤ 4 := by rcases hAdeg with h | h <;> omega
  have hBle : B.natDegree ≤ 4 := by rcases hAdeg with h | h <;> omega
  rw [hPB]
  exact completelySolvableByRadicals_mul_of_natDegree_le_four
    hA0 hB0 hAle hBle

theorem nonlinearFactor_implies_radical (f : MonicSextic)
    (h : f.hasBoundedNonlinearFactor = true) :
    CompletelySolvableByRadicals f.ratPolynomial := by
  rw [MonicSextic.hasBoundedNonlinearFactor_iff_dvd] at h
  rcases h with ⟨b, -, c, -, hdvd⟩ | ⟨b, -, c, -, d, -, hdvd⟩
  · let A : ℚ[X] := (quadraticFactor b c).map (Int.castRingHom ℚ)
    have hAmonic : A.Monic := (quadraticFactor_monic b c).map _
    have hAdeg : A.natDegree = 2 := by
      dsimp only [A]
      rw [(quadraticFactor_monic b c).natDegree_map]
      simp only [quadraticFactor]
      compute_degree!
    have hdiv : A ∣ f.ratPolynomial := by
      simpa [A, MonicSextic.ratPolynomial] using
        Polynomial.map_dvd (Int.castRingHom ℚ) hdvd
    exact completelySolvableByRadicals_of_monic_degree_six_of_monic_divisor
      f.ratPolynomial_monic f.ratPolynomial_natDegree hAmonic (Or.inl hAdeg) hdiv
  · let A : ℚ[X] := (cubicFactor b c d).map (Int.castRingHom ℚ)
    have hAmonic : A.Monic := (cubicFactor_monic b c d).map _
    have hAdeg : A.natDegree = 3 := by
      dsimp only [A]
      rw [(cubicFactor_monic b c d).natDegree_map]
      simp only [cubicFactor]
      compute_degree!
    have hdiv : A ∣ f.ratPolynomial := by
      simpa [A, MonicSextic.ratPolynomial] using
        Polynomial.map_dvd (Int.castRingHom ℚ) hdvd
    exact completelySolvableByRadicals_of_monic_degree_six_of_monic_divisor
      f.ratPolynomial_monic f.ratPolynomial_natDegree hAmonic (Or.inr hAdeg) hdiv

theorem linear_factor_radical_iff_quotient (f : MonicSextic) (c : ℤ)
    (hrem : f.linearRemainderZero c) :
    CompletelySolvableByRadicals f.ratPolynomial ↔
      CompletelySolvableByRadicals
        ((f.linearQuotient c).map (Int.castRingHom ℚ)) := by
  let A : ℚ[X] := (linearFactor c).map (Int.castRingHom ℚ)
  let B : ℚ[X] := (f.linearQuotient c).map (Int.castRingHom ℚ)
  have hzero : f 0 - c * f.linearQ0 c = 0 := by
    rw [sub_eq_zero]
    exact hrem
  have hZ := f.linear_division_identity c
  rw [hzero, C_0, add_zero] at hZ
  have hP : f.ratPolynomial = A * B := by
    rw [MonicSextic.ratPolynomial, hZ, Polynomial.map_mul]
  have hAmonic : A.Monic := (linearFactor_monic c).map _
  have hAdeg : A.natDegree ≤ 4 := by
    dsimp only [A]
    rw [(linearFactor_monic c).natDegree_map]
    simp only [linearFactor]
    compute_degree!
  have hB0 : B ≠ 0 := by
    intro hzeroB
    rw [hzeroB, mul_zero] at hP
    exact f.ratPolynomial_monic.ne_zero hP
  rw [hP]
  exact completelySolvableByRadicals_mul_iff_right
    hAmonic.ne_zero hB0 hAdeg

theorem selectedQuinticDecision_correct (f : MonicSextic) :
    recursiveQuinticRadicalDecision (selectedQuintic f) = true ↔
      CompletelySolvableByRadicals
        ((f.linearQuotient (selectedLinearCoeff f)).map
          (Int.castRingHom ℚ)) := by
  rw [recursiveQuinticRadicalDecision_correct]
  change (selectedQuintic f) 5 ≠ 0 ∧
      CompletelySolvableByRadicals
        (QuinticRadicalComputability.ratPolynomial (selectedQuintic f)) ↔ _
  rw [show (selectedQuintic f) 5 = 1 by rfl]
  dsimp only [selectedQuintic]
  rw [linearQuotientCoefficients_ratPolynomial]
  simp

/-! ## Complete monic decision -/

/-- For an irreducible rational sextic, radical solvability of all roots is
equivalent to solvability of its Galois group.  This is the degree-six
instance of the same Abel--Ruffini/Galois argument used for quintics. -/
theorem completelySolvableByRadicals_iff_gal_isSolvable_of_irreducible_sextic
    {p : ℚ[X]} (hp : Irreducible p) (hdeg : p.natDegree = 6) :
    CompletelySolvableByRadicals p ↔ IsSolvable p.Gal := by
  constructor
  · intro hrad
    have hp0 : p ≠ 0 := hp.ne_zero
    have hmap0 : p.map (algebraMap ℚ ℂ) ≠ 0 := map_ne_zero hp0
    have hmapNatDegree : (p.map (algebraMap ℚ ℂ)).natDegree = 6 := by
      rw [Polynomial.natDegree_map_eq_of_injective
        (algebraMap ℚ ℂ).injective p, hdeg]
    have hmapDegree : (p.map (algebraMap ℚ ℂ)).degree ≠ 0 := by
      rw [degree_eq_natDegree hmap0, hmapNatDegree]
      norm_num
    obtain ⟨x, hx⟩ :=
      IsAlgClosed.exists_root (p.map (algebraMap ℚ ℂ)) hmapDegree
    have hxaeval : aeval x p = 0 := by
      simpa [Polynomial.IsRoot, aeval_def] using hx
    have hxset : x ∈ p.rootSet ℂ := (mem_rootSet_of_ne hp0).2 hxaeval
    exact isSolvable_gal_of_irreducible (hrad ⟨x, hxset⟩) hp
      (aeval_eq_zero_of_mem_rootSet hxset)
  · intro hsolv
    let L : IntermediateField ℚ ℂ :=
      IntermediateField.adjoin ℚ (p.rootSet ℂ)
    letI : Fact ((p.map (algebraMap ℚ ℂ)).Splits) :=
      ⟨IsAlgClosed.splits _⟩
    letI : p.IsSplittingField ℚ L :=
      IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
    letI : FiniteDimensional ℚ L := IsSplittingField.finiteDimensional L p
    letI : IsGalois ℚ L :=
      IsGalois.of_separable_splitting_field hp.separable
    let e : Gal(L/ℚ) ≃* p.Gal :=
      (IsSplittingField.algEquiv L p).autCongr
    letI : IsSolvable Gal(L/ℚ) :=
      solvable_of_solvable_injective (f := e.toMonoidHom) e.injective
    have hL : L ≤ solvableByRad ℚ ℂ :=
      solvable_galois_over_rat_le_solvableByRad L
    intro x
    exact hL (IntermediateField.subset_adjoin ℚ (p.rootSet ℂ) x.property)

noncomputable def monicSexticRadicalDecision (f : MonicSextic) : Bool :=
  if f.hasBoundedNonlinearFactor then true
  else if f.hasBoundedLinearFactor then
    recursiveQuinticRadicalDecision (selectedQuintic f)
  else irreducibleSolvableB f

theorem monicSexticRadicalDecision_computable :
    Computable monicSexticRadicalDecision := by
  have hnonlinear : Computable hasBoundedNonlinearFactor :=
    MonicSextic.hasBoundedNonlinearFactor_primrec.to_comp
  have hlinear : Computable hasBoundedLinearFactor :=
    MonicSextic.hasBoundedLinearFactor_primrec.to_comp
  have hquintic : Computable fun f : MonicSextic ↦
      recursiveQuinticRadicalDecision (selectedQuintic f) :=
    recursiveQuinticRadicalDecision_primrec.to_comp.comp
      selectedQuintic_computable
  exact (Computable.cond hnonlinear (Computable.const true)
    (Computable.cond hlinear hquintic irreducibleSolvableB_computable)).of_eq
      fun f ↦ by
        simp only [monicSexticRadicalDecision]
        cases f.hasBoundedNonlinearFactor <;>
          cases f.hasBoundedLinearFactor <;> rfl

/-- The combined Boolean accepts exactly the monic rational sextics whose
complex roots all lie in the radical closure of `ℚ`. -/
theorem monicSexticRadicalDecision_correct (f : MonicSextic) :
    monicSexticRadicalDecision f = true ↔
      CompletelySolvableByRadicals f.ratPolynomial := by
  by_cases hnonlinear : f.hasBoundedNonlinearFactor = true
  · have hrad := nonlinearFactor_implies_radical f hnonlinear
    simp [monicSexticRadicalDecision, hnonlinear, hrad]
  · have hnonlinearFalse : f.hasBoundedNonlinearFactor = false := by
      cases h : f.hasBoundedNonlinearFactor <;> simp_all
    by_cases hlinear : f.hasBoundedLinearFactor = true
    · have hrem := selectedLinearCoeff_spec f hlinear
      simp only [monicSexticRadicalDecision, hnonlinearFalse, hlinear,
        Bool.false_eq_true, ↓reduceIte]
      rw [selectedQuinticDecision_correct,
        ← linear_factor_radical_iff_quotient f (selectedLinearCoeff f) hrem]
    · have hlinearFalse : f.hasBoundedLinearFactor = false := by
        cases h : f.hasBoundedLinearFactor <;> simp_all
      have hproper : f.hasBoundedProperFactor = false := by
        simp [MonicSextic.hasBoundedProperFactor, hlinearFalse,
          hnonlinearFalse]
      have hirr : Irreducible f.ratPolynomial := by
        apply (irreducibleB_eq_true f).mp
        simp [irreducibleB, hproper]
      simp only [monicSexticRadicalDecision, hnonlinearFalse, hlinearFalse,
        Bool.false_eq_true, ↓reduceIte]
      rw [irreducibleSolvableB_correct f hirr,
        completelySolvableByRadicals_iff_gal_isSolvable_of_irreducible_sextic
          hirr f.ratPolynomial_natDegree]

end LeanProofs.PolynomialFormulas.SexticReducibleDecision
