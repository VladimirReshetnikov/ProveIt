import GRHArticle.ProgressionFree.NumberFieldIdeals.FiniteIdealQuotientPresentation
import GRHArticle.ProgressionFree.NumberFieldIdeals.IdealOptimizationTableCorrectness
import GRHArticle.ProgressionFree.NumberFieldIdeals.SquarefreeExterior

/-!
# Deriving a correct ideal table from finite quotient arithmetic

The table uses only bounded finite arithmetic. The smoothness test checks
containment in every exterior prime carrier. Product equality in the
common quotient gives the actual midpoint test.
-/

namespace GRHArticle.ProgressionFree.NumberFieldIdeals.FiniteRing

open NumberField Ideal IsDedekindDomain Finset
open scoped nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]
variable {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]

/-- Prime carriers with index at most the specified bound. -/
def boundedPrimeCarriers (R : Type*) [CommRing R] [Fintype R] [DecidableEq R] (Y : ℕ) : Finset (Finset R) :=
  (idealCarriers R).filter fun A ↦ IsPrimeCarrier A ∧ carrierIndex A ≤ Y

/-- Smooth carriers through the requested norm cutoff. -/
def boundedSmoothCarriers (R : Type*) [CommRing R] [Fintype R] [DecidableEq R]
    (Y H : ℕ) : Finset (Finset R) :=
  (idealCarriers R).filter fun A ↦ carrierIndex A ≤ H ∧
    ∀ P ∈ idealCarriers R, IsPrimeCarrier P → Y < carrierIndex P → ¬ A ⊆ P

/-- The complete quotient-derived table used by the rational evaluator. -/
def idealTable (R : Type*) [CommRing R] [Fintype R] [DecidableEq R] (Y H : ℕ) :
    IdealCutoffTable ↥(boundedSmoothCarriers R Y H) where
  norm a := carrierIndex a.val
  midpoint a b c := decide (carrierProduct a.val c.val = carrierProduct b.val b.val)
  divides a b := decide (b.val ⊆ a.val)

/-- The prime norms in the finite quotient, with multiplicity. -/
def boundedPrimeNorms (R : Type*) [CommRing R] [Fintype R] [DecidableEq R] (Y : ℕ) : Multiset ℕ :=
  (boundedPrimeCarriers R Y).val.map carrierIndex

variable {Y H : ℕ} (Q : FiniteIdealQuotient K R (max Y H))

omit [DecidableEq R] in
private theorem index_eq (A : Finset R) (hA : IsIdealCarrier A) :
    carrierIndex A = absNorm (Q.lift (idealOfCarrier A hA)).val :=
  (carrierIndex_eq_card_quotient hA).trans (Q.absNorm_lift _).symm

omit [DecidableEq R] in
private theorem carrierOfIdeal_index_eq (I : (Ideal (𝓞 K))⁰)
    (hI : absNorm I.val ≤ max Y H) :
    carrierIndex (carrierOfIdeal (I.val.map Q.reduction)) = absNorm I.val := by
  rw [index_eq Q _ (isIdealCarrier_carrierOfIdeal _), idealOfCarrier_carrierOfIdeal,
    Q.lift_map_of_modulus_le (boundedIdealModulus_le _ hI)]

set_option maxHeartbeats 500000 in
private theorem lifted_smooth_iff (A : Finset R) (hA : IsIdealCarrier A) :
    A ∈ boundedSmoothCarriers R Y H ↔
    Q.lift (idealOfCarrier A hA) ∈ idealNormCutoff (Set.range (smoothMultiplier (primesThroughNorm K Y))) H := by
  let J := idealOfCarrier A hA
  let I := Q.lift J
  have hn := index_eq Q A hA
  change A ∈ boundedSmoothCarriers R Y H ↔ I ∈ idealNormCutoff (Set.range (smoothMultiplier (primesThroughNorm K Y))) H
  simp only [boundedSmoothCarriers, mem_filter, (mem_idealCarriers A).mpr hA, true_and]
  constructor
  · rintro ⟨hN,hP⟩
    have hNI : absNorm I.val ≤ H := Eq.trans_le hn.symm hN
    refine ⟨?_,hNI⟩
    apply (smooth_iff_no_exterior_prime_dvd (primesThroughNorm K Y) I).mpr
    intro p hp hd
    have hd' : p.asIdeal ∣ I.val := (nonZeroDivisors_dvd_iff_dvd_coe (a := primeIdeal p) (b := I)).mp hd
    have hle : I.val ≤ p.asIdeal := Ideal.dvd_iff_le.mp hd'
    have hpN := Nat.le_of_dvd (absNorm_pos_of_nonZeroDivisors I) (absNorm_dvd_absNorm_of_le hle)
    have hpH : absNorm p.asIdeal ≤ max Y H := hpN.trans (hNI.trans (le_max_right _ _))
    let C := carrierOfIdeal (p.asIdeal.map Q.reduction)
    have hC := isIdealCarrier_carrierOfIdeal (p.asIdeal.map Q.reduction)
    have hCp : IsPrimeCarrier C := (isPrimeCarrier_iff hC).mpr (by
      rw [idealOfCarrier_carrierOfIdeal]
      exact Q.map_isPrime p hpH)
    have hCn : carrierIndex C = absNorm p.asIdeal := carrierOfIdeal_index_eq Q (primeIdeal p) hpH
    have hCY : Y < carrierIndex C := by
      rw [hCn]
      exact lt_of_not_ge (fun h ↦ hp ((mem_primesThroughNorm p Y).mpr h))
    apply hP C ((mem_idealCarriers C).mpr hC) hCp hCY
    intro r hr
    apply (mem_carrierOfIdeal _ r).mpr
    have hmap := Ideal.map_mono (f := Q.reduction) hle
    change (Q.lift J).val.map Q.reduction ≤ p.asIdeal.map Q.reduction at hmap
    rw [Q.map_lift] at hmap
    exact hmap hr
  · rintro ⟨hs,hN⟩
    refine ⟨hn.trans_le hN,?_⟩
    intro C hC hCp hCY hsub
    have hCl := (mem_idealCarriers C).mp hC
    let L := idealOfCarrier C hCl
    let p := Q.liftPrime L ((isPrimeCarrier_iff hCl).mp hCp)
    have he : carrierIndex C = absNorm p.asIdeal := index_eq Q C hCl
    have hp : p ∉ primesThroughNorm K Y := by
      intro hin
      exact hCY.not_ge (he.symm ▸ (mem_primesThroughNorm p Y).mp hin)
    have hsub' : J ≤ L := hsub
    have hIl : I.val ≤ p.asIdeal := (Q.lift_le_iff (J := J) (L := L)).mpr hsub'
    have hd : p.asIdeal ∣ I.val := Ideal.dvd_iff_le.mpr hIl
    exact (smooth_iff_no_exterior_prime_dvd _ I).mp hs p hp
      ((nonZeroDivisors_dvd_iff_dvd_coe (a := primeIdeal p) (b := I)).mpr hd)

/-- Interpret a computed smooth vertex as a nonzero ideal. -/
def idealTableValue (A : ↥(boundedSmoothCarriers R Y H)) : (Ideal (𝓞 K))⁰ :=
  Q.lift (idealOfCarrier A.val ((mem_idealCarriers _).mp (mem_filter.mp A.property).1))

set_option maxHeartbeats 500000 in
/-- No ideal oracle is needed: reduction, finite arithmetic and exhaustive
carrier enumeration supply a complete exact ideal cutoff table. -/
theorem idealTable_correct :
    (idealTable R Y H).Correct (primesThroughNorm K Y) H (idealTableValue Q) := by
  have hideal (a : ↥(boundedSmoothCarriers R Y H)) :=
    (mem_idealCarriers _).mp (mem_filter.mp a.property).1
  have hnorm (a : ↥(boundedSmoothCarriers R Y H)) : carrierIndex a.val = absNorm (idealTableValue Q a).val :=
    index_eq Q a.val (hideal a)
  have hbound (a : ↥(boundedSmoothCarriers R Y H)) : absNorm (idealTableValue Q a).val ≤ max Y H :=
    ((hnorm a).symm.trans_le (mem_filter.mp a.property).2.1).trans (le_max_right _ _)
  constructor
  · intro a b he
    apply Subtype.ext
    have hie := Q.lift_injective he
    ext x
    change x ∈ idealOfCarrier a.val (hideal a) ↔ x ∈ idealOfCarrier b.val (hideal b)
    rw [hie]
  · ext I
    constructor
    · rintro ⟨A,rfl⟩
      exact (lifted_smooth_iff Q A.val (hideal A)).mp A.property
    · intro hI
      let A := carrierOfIdeal (I.val.map Q.reduction)
      have ha := isIdealCarrier_carrierOfIdeal (I.val.map Q.reduction)
      have he : Q.lift (idealOfCarrier A ha) = I := by
        rw [idealOfCarrier_carrierOfIdeal, Q.lift_map_of_modulus_le (boundedIdealModulus_le _ (hI.2.trans (le_max_right _ _)))]
      have hA := (lifted_smooth_iff Q A ha).mpr (he.symm ▸ hI)
      exact ⟨⟨A,hA⟩,he⟩
  · exact hnorm
  · intro a b c
    simp only [idealTable, decide_eq_true_eq]
    have hprod : carrierProduct a.val c.val = carrierProduct b.val b.val ↔
        idealOfCarrier a.val (hideal a) * idealOfCarrier c.val (hideal c) =
          idealOfCarrier b.val (hideal b) * idealOfCarrier b.val (hideal b) := by
      constructor
      · intro he
        ext x
        rw [← mem_carrierProduct_iff (hideal a) (hideal c),
          ← mem_carrierProduct_iff (hideal b) (hideal b), he]
      · intro he
        ext x
        rw [mem_carrierProduct_iff (hideal a) (hideal c), mem_carrierProduct_iff (hideal b) (hideal b), he]
    rw [hprod]
    have hf := Q.map_eq_iff (boundedIdealModulus_le_mul _ (hbound a) (hbound c))
      (boundedIdealModulus_le_mul _ (hbound b) (hbound b))
    rw [Submonoid.coe_mul, Submonoid.coe_mul, Ideal.map_mul, Ideal.map_mul] at hf
    change ((Q.lift _).val.map Q.reduction) * ((Q.lift _).val.map Q.reduction) =
      ((Q.lift _).val.map Q.reduction) * ((Q.lift _).val.map Q.reduction) ↔ _ at hf
    simp only [Q.map_lift] at hf
    constructor
    · exact fun h ↦ Subtype.ext (hf.mp h)
    · exact fun h ↦ hf.mpr (congrArg Subtype.val h)
  · intro a b
    simp only [idealTable, decide_eq_true_eq, nonZeroDivisors_dvd_iff_dvd_coe, Ideal.dvd_iff_le]
    exact (Q.lift_le_iff (J := idealOfCarrier b.val (hideal b)) (L := idealOfCarrier a.val (hideal a))).symm

set_option maxHeartbeats 500000 in
/-- The quotient-derived prime list gives every small prime ideal exactly
once, preserving repeated absolute norms. -/
theorem boundedPrimeNorms_eq (Q : FiniteIdealQuotient K R (max Y H)) : boundedPrimeNorms R Y =
    (primesThroughNorm K Y).val.map (fun p ↦ absNorm p.asIdeal) := by
  let B := boundedPrimeCarriers R Y
  have hA (a : ↥B) : IsIdealCarrier a.val := (mem_idealCarriers _).mp (mem_filter.mp a.property).1
  let p (a : ↥B) := Q.liftPrime (idealOfCarrier a.val (hA a))
    ((isPrimeCarrier_iff (hA a)).mp (mem_filter.mp a.property).2.1)
  have hnorm (a : ↥B) : carrierIndex a.val = absNorm (p a).asIdeal := index_eq Q a.val (hA a)
  have hinj : Function.Injective p := by
    intro a b he
    have himg : Q.lift (idealOfCarrier a.val (hA a)) = Q.lift (idealOfCarrier b.val (hA b)) :=
      Subtype.ext (congrArg (fun q : HeightOneSpectrum (𝓞 K) ↦ q.asIdeal) he)
    have hei := Q.lift_injective himg
    apply Subtype.ext
    ext x
    change x ∈ idealOfCarrier a.val (hA a) ↔ x ∈ idealOfCarrier b.val (hA b)
    rw [hei]
  let e : ↥B ↪ HeightOneSpectrum (𝓞 K) := ⟨p,hinj⟩
  have hmap : B.attach.map e = primesThroughNorm K Y := by
    ext q
    constructor
    · intro hq
      obtain ⟨a,_,rfl⟩ := mem_map.mp hq
      exact (mem_primesThroughNorm (p a) Y).mpr (hnorm a ▸ (mem_filter.mp a.property).2.2)
    · intro hq
      let J := q.asIdeal.map Q.reduction
      let A := carrierOfIdeal J
      have hY := (mem_primesThroughNorm q Y).mp hq
      have hN := hY.trans (le_max_left Y H)
      have ha : IsIdealCarrier A := isIdealCarrier_carrierOfIdeal J
      have hPrime : IsPrimeCarrier A := (isPrimeCarrier_iff ha).mpr (by
        rw [idealOfCarrier_carrierOfIdeal]
        exact Q.map_isPrime q hN)
      have hIndex : carrierIndex A = absNorm q.asIdeal := carrierOfIdeal_index_eq Q (primeIdeal q) hN
      have hB : A ∈ B := mem_filter.mpr ⟨(mem_idealCarriers A).mpr ha,hPrime,hIndex.trans_le hY⟩
      let a : B := ⟨A,hB⟩
      refine mem_map.mpr ⟨a,mem_attach _ _,?_⟩
      apply HeightOneSpectrum.ext
      change (Q.lift (idealOfCarrier A ha)).val = q.asIdeal
      rw [idealOfCarrier_carrierOfIdeal]
      exact congrArg Subtype.val (Q.lift_map_of_modulus_le (I := primeIdeal q) (boundedIdealModulus_le _ hN))
  change B.val.map carrierIndex = (primesThroughNorm K Y).val.map (fun q ↦ absNorm q.asIdeal)
  rw [← hmap, Finset.map_val, Multiset.map_map]
  change B.val.map carrierIndex = B.val.attach.map (fun a ↦ absNorm (p a).asIdeal)
  rw [← Multiset.attach_map_val' B.val carrierIndex]
  exact Multiset.map_congr rfl (fun a _ ↦ hnorm a)

end GRHArticle.ProgressionFree.NumberFieldIdeals.FiniteRing
