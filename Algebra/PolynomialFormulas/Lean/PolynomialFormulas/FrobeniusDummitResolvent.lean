import PolynomialFormulas.Fin5TransitiveC5
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.RingTheory.Polynomial.Vieta

/-!
# The scalar Frobenius--Dummit resolvent for quintics

This file constructs the classical ten-term quartic invariant whose stabilizer
in `S₅` is the Frobenius group `F₂₀`, its six-element orbit, and the associated
monic scalar sextic resolvent used by Dummit's algorithm.

The coefficients of the universal resolvent are proved symmetric and are then
pulled back, once and for all, to polynomials in the five elementary symmetric
functions.  Consequently specialization at any ordered five-tuple depends
only on its elementary symmetric functions (and hence on the coefficients of
the monic polynomial having that tuple as its roots).
-/

open scoped BigOperators
open Equiv MvPolynomial Polynomial

namespace LeanProofs.PolynomialFormulas.FrobeniusDummitResolvent

open LeanProofs.PolynomialFormulas.Fin5Solvable

abbrev S5 := Equiv.Perm (Fin 5)
abbrev Exponent := Fin 5 → ℕ

/-- The exponent function of `x_i² x_j x_k`. -/
def exponent (i j k : Fin 5) : Exponent := fun n ↦
  if n = i then 2 else if n = j ∨ n = k then 1 else 0

/-- The ten exponent vectors occurring in Dummit's invariant, in the order
used by the displayed scalar formula below. -/
def thetaExponent : Fin 10 → Exponent :=
  ![exponent 0 1 4, exponent 0 2 3,
    exponent 1 0 2, exponent 1 3 4,
    exponent 2 0 4, exponent 2 1 3,
    exponent 3 0 1, exponent 3 2 4,
    exponent 4 0 3, exponent 4 1 2]

theorem thetaExponent_injective : Function.Injective thetaExponent := by
  decide

/-- The support of Dummit's invariant. -/
def thetaSupport : Finset Exponent :=
  Finset.univ.image thetaExponent

/-- Permutation of exponent vectors induced by renaming variables. -/
def actExponent (g : S5) (d : Exponent) : Exponent := fun i ↦ d (g.symm i)

@[simp] theorem actExponent_one (d : Exponent) : actExponent 1 d = d := by
  funext i
  rfl

theorem actExponent_mul (g h : S5) (d : Exponent) :
    actExponent (g * h) d = actExponent g (actExponent h d) := by
  funext i
  rfl

theorem actExponent_injective (g : S5) : Function.Injective (actExponent g) := by
  intro d e h
  funext i
  have hi := congrFun h (g i)
  simpa [actExponent] using hi

def permuteSupport (g : S5) (s : Finset Exponent) : Finset Exponent :=
  s.image (actExponent g)

theorem permuteSupport_mul (g h : S5) (s : Finset Exponent) :
    permuteSupport (g * h) s = permuteSupport g (permuteSupport h s) := by
  rw [permuteSupport, permuteSupport, permuteSupport, Finset.image_image]
  congr 1

/-- Turn a finite collection of exponent functions into a multivariate
polynomial whose displayed monomials all have coefficient one. -/
noncomputable def polynomialOfSupport (s : Finset Exponent) :
    MvPolynomial (Fin 5) ℤ :=
  ∑ d ∈ s, monomial (Finsupp.equivFunOnFinite.symm d) 1

theorem finsupp_actExponent (g : S5) (d : Exponent) :
    (Finsupp.equivFunOnFinite.symm d).mapDomain g =
      Finsupp.equivFunOnFinite.symm (actExponent g d) := by
  ext i
  simp [actExponent]

theorem rename_polynomialOfSupport (g : S5) (s : Finset Exponent) :
    rename g (polynomialOfSupport s) =
      polynomialOfSupport (permuteSupport g s) := by
  classical
  simp only [polynomialOfSupport, map_sum, rename_monomial,
    finsupp_actExponent, permuteSupport]
  rw [Finset.sum_image (actExponent_injective g).injOn]

theorem coeff_polynomialOfSupport (s : Finset Exponent) (d : Exponent) :
    (polynomialOfSupport s).coeff (Finsupp.equivFunOnFinite.symm d) =
      if d ∈ s then 1 else 0 := by
  classical
  simp [polynomialOfSupport, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_monomial]

theorem polynomialOfSupport_injective : Function.Injective polynomialOfSupport := by
  intro s t h
  ext d
  constructor
  · intro hds
    by_contra hdt
    have hc := congrArg
      (MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm d)) h
    simp [coeff_polynomialOfSupport, hds, hdt] at hc
  · intro hdt
    by_contra hds
    have hc := congrArg
      (MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm d)) h
    simp [coeff_polynomialOfSupport, hds, hdt] at hc

/-- Dummit's ten-term quartic invariant. -/
noncomputable def theta : MvPolynomial (Fin 5) ℤ :=
  polynomialOfSupport thetaSupport

/-- The cycle `(012)` in the convention used by `Equiv.Perm`. -/
abbrev threeCycle : S5 := Fin5TransitiveC5.threeCycle

theorem threeCycle_symm : threeCycle.symm =
    Equiv.swap 1 2 * Equiv.swap 0 1 := by
  ext i
  fin_cases i <;> decide

/-- Six representatives for the orbit `S₅ / F₂₀`:
`id, (012), (021), (01), (12), (02)`. -/
abbrev representative : Fin 6 → S5 :=
  Fin5TransitiveC5.representative

/-- The six conjugates of `theta` used as roots of the resolvent. -/
noncomputable def thetaOrbit (i : Fin 6) : MvPolynomial (Fin 5) ℤ :=
  rename (representative i) theta

abbrev c5Elements : Finset S5 :=
  Fin5TransitiveC5.c5Elements

theorem mem_c5Elements_iff (g : S5) :
    g ∈ c5Elements ↔ g ∈ standardC5 := by
  exact Fin5TransitiveC5.mem_c5Elements_iff g

abbrev normalizesC5B (g : S5) : Bool :=
  Fin5TransitiveC5.normalizesC5B g

theorem normalizesC5B_eq_true (g : S5) :
    normalizesC5B g = true ↔ g ∈ standardF20 := by
  exact Fin5TransitiveC5.normalizesC5B_eq_true g

def stabilizesThetaSupportB (g : S5) : Bool :=
  decide (permuteSupport g thetaSupport = thetaSupport)

/-- Multiplication by two on `Z/5Z`.  Together with `fiveCycle` it generates
the standard affine copy of `F₂₀`. -/
def multiplierTwo : S5 where
  toFun := ![0, 2, 4, 1, 3]
  invFun := ![0, 3, 1, 4, 2]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def affineF20 : Subgroup S5 :=
  Subgroup.closure {fiveCycle, multiplierTwo}

theorem fiveCycle_stabilizes_thetaSupport :
    permuteSupport fiveCycle thetaSupport = thetaSupport := by
  decide

theorem multiplierTwo_stabilizes_thetaSupport :
    permuteSupport multiplierTwo thetaSupport = thetaSupport := by
  decide

theorem multiplierTwo_conj_fiveCycle :
    multiplierTwo * fiveCycle * multiplierTwo⁻¹ = fiveCycle ^ 2 := by
  decide

theorem fiveCycle_eq_square_cube : (fiveCycle ^ 2) ^ 3 = fiveCycle := by
  decide

theorem multiplierTwo_mem_standardF20 : multiplierTwo ∈ standardF20 := by
  rw [standardF20, Subgroup.mem_normalizer_iff_map_conj_eq,
    standardC5, MonoidHom.map_zpowers]
  change Subgroup.zpowers (multiplierTwo * fiveCycle * multiplierTwo⁻¹) =
    Subgroup.zpowers fiveCycle
  rw [multiplierTwo_conj_fiveCycle]
  apply le_antisymm
  · exact Subgroup.zpowers_le.mpr
      (Subgroup.npow_mem_zpowers fiveCycle 2)
  · apply Subgroup.zpowers_le.mpr
    have hmem : (fiveCycle ^ 2) ^ 3 ∈ Subgroup.zpowers (fiveCycle ^ 2) :=
      Subgroup.npow_mem_zpowers _ _
    rw [fiveCycle_eq_square_cube] at hmem
    exact hmem

theorem affineF20_le_standardF20 : affineF20 ≤ standardF20 := by
  apply (Subgroup.closure_le standardF20).mpr
  simp only [Set.insert_subset_iff, Set.singleton_subset_iff]
  exact ⟨Subgroup.le_normalizer (Subgroup.mem_zpowers fiveCycle),
    multiplierTwo_mem_standardF20⟩

def affineElement (x : Fin 5 × Fin 4) : S5 :=
  fiveCycle ^ (x.1 : ℕ) * multiplierTwo ^ (x.2 : ℕ)

theorem affineElement_injective : Function.Injective affineElement := by
  decide

theorem affineElement_mem (x : Fin 5 × Fin 4) :
    affineElement x ∈ affineF20 := by
  apply mul_mem
  · exact Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_insert _ _)) _
  · exact Subgroup.pow_mem _
      (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))) _

def affineElementSubtype (x : Fin 5 × Fin 4) : affineF20 :=
  ⟨affineElement x, affineElement_mem x⟩

theorem affineElementSubtype_injective :
    Function.Injective affineElementSubtype := by
  intro x y h
  exact affineElement_injective (congrArg Subtype.val h)

theorem affineF20_eq_standardF20 : affineF20 = standardF20 := by
  apply Subgroup.eq_of_le_of_card_ge affineF20_le_standardF20
  rw [Fin5TransitiveC5.natCard_standardF20]
  have hcard := Nat.card_le_card_of_injective
    affineElementSubtype affineElementSubtype_injective
  simpa [Nat.card_prod] using hcard

/-- The subgroup preserving the ten exponent vectors in `theta`. -/
def thetaSupportStabilizer : Subgroup S5 where
  carrier := {g | permuteSupport g thetaSupport = thetaSupport}
  one_mem' := by
    change permuteSupport 1 thetaSupport = thetaSupport
    have hone : actExponent 1 = id := by
      funext d
      exact actExponent_one d
    simp [permuteSupport, hone]
  mul_mem' := by
    intro g h hg hh
    change permuteSupport g thetaSupport = thetaSupport at hg
    change permuteSupport h thetaSupport = thetaSupport at hh
    change permuteSupport (g * h) thetaSupport = thetaSupport
    rw [permuteSupport_mul, hh, hg]
  inv_mem' := by
    intro g hg
    change permuteSupport g thetaSupport = thetaSupport at hg
    change permuteSupport g⁻¹ thetaSupport = thetaSupport
    calc
      permuteSupport g⁻¹ thetaSupport =
          permuteSupport g⁻¹ (permuteSupport g thetaSupport) :=
        congrArg (permuteSupport g⁻¹) hg.symm
      _ = permuteSupport (g⁻¹ * g) thetaSupport :=
        (permuteSupport_mul _ _ _).symm
      _ = thetaSupport := by
        have hone : actExponent 1 = id := by
          funext d
          exact actExponent_one d
        simp [permuteSupport, hone]

theorem standardF20_le_thetaSupportStabilizer :
    standardF20 ≤ thetaSupportStabilizer := by
  rw [← affineF20_eq_standardF20]
  apply (Subgroup.closure_le thetaSupportStabilizer).mpr
  simp only [Set.insert_subset_iff, Set.singleton_subset_iff]
  exact ⟨fiveCycle_stabilizes_thetaSupport,
    multiplierTwo_stabilizes_thetaSupport⟩

/-- The displayed representatives give six distinct translates of the theta
support. -/
theorem theta_support_orbit_injective : Function.Injective
    (fun i : Fin 6 ↦ permuteSupport (representative i) thetaSupport) := by
  decide

def thetaStabilizerPacking (x : Fin 6 × thetaSupportStabilizer) : S5 :=
  representative x.1 * x.2.1

theorem thetaStabilizerPacking_injective :
    Function.Injective thetaStabilizerPacking := by
  rintro ⟨i, k⟩ ⟨j, l⟩ h
  change representative i * k.1 = representative j * l.1 at h
  have hs : permuteSupport (representative i) thetaSupport =
      permuteSupport (representative j) thetaSupport := by
    calc
      permuteSupport (representative i) thetaSupport =
          permuteSupport (representative i)
            (permuteSupport k.1 thetaSupport) := by rw [k.2]
      _ = permuteSupport (representative i * k.1) thetaSupport :=
        (permuteSupport_mul _ _ _).symm
      _ = permuteSupport (representative j * l.1) thetaSupport :=
        congrArg (fun g ↦ permuteSupport g thetaSupport) h
      _ = permuteSupport (representative j)
            (permuteSupport l.1 thetaSupport) :=
        permuteSupport_mul _ _ _
      _ = permuteSupport (representative j) thetaSupport := by rw [l.2]
  have hij : i = j := theta_support_orbit_injective hs
  subst j
  have hkl : k = l := by
    apply Subtype.ext
    exact mul_left_cancel h
  subst l
  rfl

theorem natCard_thetaSupportStabilizer_le :
    Nat.card thetaSupportStabilizer ≤ 20 := by
  have hpack := Nat.card_le_card_of_injective
    thetaStabilizerPacking thetaStabilizerPacking_injective
  have hS5 : Nat.card S5 = 120 := by
    rw [show Nat.card S5 = Fintype.card S5 by exact Nat.card_eq_fintype_card]
    norm_num [S5, Fintype.card_perm]
  rw [Nat.card_prod, hS5] at hpack
  norm_num at hpack ⊢
  omega

theorem thetaSupportStabilizer_eq_standardF20 :
    thetaSupportStabilizer = standardF20 := by
  apply (Subgroup.eq_of_le_of_card_ge standardF20_le_thetaSupportStabilizer ?_).symm
  rw [Fin5TransitiveC5.natCard_standardF20]
  exact natCard_thetaSupportStabilizer_le

/-- The stabilizer of the actual ten-term invariant is exactly `F₂₀`. -/
theorem stabilizesThetaB_eq_normalizesC5B :
    ∀ g : S5, stabilizesThetaSupportB g = normalizesC5B g := by
  intro g
  apply Bool.eq_iff_iff.mpr
  rw [normalizesC5B_eq_true]
  simp only [stabilizesThetaSupportB, decide_eq_true_eq]
  change g ∈ thetaSupportStabilizer ↔ g ∈ standardF20
  rw [thetaSupportStabilizer_eq_standardF20]

theorem permuteSupport_thetaSupport_eq_iff (g : S5) :
    permuteSupport g thetaSupport = thetaSupport ↔ g ∈ standardF20 := by
  rw [← normalizesC5B_eq_true, ← stabilizesThetaB_eq_normalizesC5B]
  simp [stabilizesThetaSupportB]

/-- The stabilizer of the actual scalar polynomial is exactly `F₂₀`. -/
theorem rename_theta_eq_theta_iff (g : S5) :
    rename g theta = theta ↔ g ∈ standardF20 := by
  rw [theta, rename_polynomialOfSupport]
  constructor
  · intro h
    exact (permuteSupport_thetaSupport_eq_iff g).mp
      (polynomialOfSupport_injective h)
  · intro h
    exact congrArg polynomialOfSupport
      ((permuteSupport_thetaSupport_eq_iff g).mpr h)

/-- The displayed six representatives give the complete orbit at the level
of exponent supports. -/
theorem theta_support_orbit_exhaustive :
    ∀ g : S5, ∃ i : Fin 6,
      permuteSupport g thetaSupport =
        permuteSupport (representative i) thetaSupport := by
  intro g
  obtain ⟨i, hi⟩ :=
    Fin5TransitiveC5.representative_cosets_exhaustive g
  have hrep : Fin5TransitiveC5.representative i = representative i := by
    rfl
  have hmem : g⁻¹ * representative i ∈ standardF20 := by
    rw [← hrep]
    exact QuotientGroup.leftRel_apply.mp (Quotient.exact' hi)
  have hstab :
      permuteSupport (g⁻¹ * representative i) thetaSupport = thetaSupport :=
    (permuteSupport_thetaSupport_eq_iff _).mpr hmem
  refine ⟨i, ?_⟩
  symm
  calc
    permuteSupport (representative i) thetaSupport =
        permuteSupport (g * (g⁻¹ * representative i)) thetaSupport := by group
    _ = permuteSupport g
          (permuteSupport (g⁻¹ * representative i) thetaSupport) :=
      permuteSupport_mul _ _ _
    _ = permuteSupport g thetaSupport := by rw [hstab]

theorem thetaOrbit_eq_polynomialOfSupport (i : Fin 6) :
    thetaOrbit i =
      polynomialOfSupport (permuteSupport (representative i) thetaSupport) := by
  rw [thetaOrbit, theta, rename_polynomialOfSupport]

/-- The standard five-cycle acts on the six theta-orbit representatives by
the same table as its action on `S₅ / F₂₀`. -/
theorem fiveCycle_thetaSupport_table (i : Fin 6) :
    permuteSupport (fiveCycle * representative i) thetaSupport =
      permuteSupport
        (representative
          (Fin5TransitiveC5.fiveCycleOnRepresentatives i)) thetaSupport := by
  fin_cases i <;> decide

theorem rename_fiveCycle_thetaOrbit (i : Fin 6) :
    rename fiveCycle (thetaOrbit i) =
      thetaOrbit (Fin5TransitiveC5.fiveCycleOnRepresentatives i) := by
  calc
    rename fiveCycle (thetaOrbit i) =
        polynomialOfSupport
          (permuteSupport (fiveCycle * representative i) thetaSupport) := by
      rw [thetaOrbit_eq_polynomialOfSupport, rename_polynomialOfSupport,
        ← permuteSupport_mul]
    _ = polynomialOfSupport
          (permuteSupport
            (representative
              (Fin5TransitiveC5.fiveCycleOnRepresentatives i))
            thetaSupport) :=
      congrArg polynomialOfSupport (fiveCycle_thetaSupport_table i)
    _ = thetaOrbit (Fin5TransitiveC5.fiveCycleOnRepresentatives i) :=
      (thetaOrbit_eq_polynomialOfSupport _).symm

/-- The six displayed orbit elements are genuinely different as formal
multivariate polynomials. -/
theorem thetaOrbit_injective : Function.Injective thetaOrbit := by
  intro i j h
  apply theta_support_orbit_injective
  apply polynomialOfSupport_injective
  simpa only [← thetaOrbit_eq_polynomialOfSupport] using h

/-- Every rename of a displayed orbit element is another displayed orbit
element. -/
theorem rename_thetaOrbit_exists (g : S5) (i : Fin 6) :
    ∃ j : Fin 6, rename g (thetaOrbit i) = thetaOrbit j := by
  obtain ⟨j, hj⟩ := theta_support_orbit_exhaustive (g * representative i)
  refine ⟨j, ?_⟩
  calc
    rename g (thetaOrbit i) =
        polynomialOfSupport
          (permuteSupport (g * representative i) thetaSupport) := by
      rw [thetaOrbit_eq_polynomialOfSupport, rename_polynomialOfSupport,
        ← permuteSupport_mul]
    _ = polynomialOfSupport
          (permuteSupport (representative j) thetaSupport) :=
      congrArg polynomialOfSupport hj
    _ = thetaOrbit j := (thetaOrbit_eq_polynomialOfSupport j).symm

/-- The six-element formal orbit, represented without duplicates. -/
noncomputable def thetaOrbitSet : Finset (MvPolynomial (Fin 5) ℤ) :=
  Finset.univ.image thetaOrbit

theorem card_thetaOrbitSet : thetaOrbitSet.card = 6 := by
  rw [thetaOrbitSet, Finset.card_image_of_injective _ thetaOrbit_injective]
  simp

/-- Renaming the five variables permutes the six formal orbit elements. -/
theorem image_rename_thetaOrbitSet (g : S5) :
    thetaOrbitSet.image (rename g) = thetaOrbitSet := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro p hp
    rw [Finset.mem_image] at hp
    obtain ⟨t, ht, rfl⟩ := hp
    rw [thetaOrbitSet, Finset.mem_image] at ht ⊢
    obtain ⟨i, _, rfl⟩ := ht
    obtain ⟨j, hj⟩ := rename_thetaOrbit_exists g i
    exact ⟨j, Finset.mem_univ j, hj.symm⟩
  · rw [Finset.card_image_of_injective _
      (MvPolynomial.rename_injective g g.injective)]

/-- The universal scalar Frobenius--Dummit sextic. -/
noncomputable def universalResolvent : Polynomial (MvPolynomial (Fin 5) ℤ) :=
  ∏ t ∈ thetaOrbitSet, (Polynomial.X - Polynomial.C t)

theorem universalResolvent_monic : universalResolvent.Monic := by
  exact Polynomial.monic_prod_of_monic _ _ (fun _ _ ↦ Polynomial.monic_X_sub_C _)

theorem universalResolvent_natDegree : universalResolvent.natDegree = 6 := by
  rw [universalResolvent, Polynomial.natDegree_finsetProd_X_sub_C_eq_card,
    card_thetaOrbitSet]

/-- Every coefficient of the universal resolvent is invariant under `S₅`. -/
theorem universalResolvent_rename (g : S5) :
    universalResolvent.map (rename g).toRingHom = universalResolvent := by
  classical
  rw [universalResolvent, Polynomial.map_prod]
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  change (∏ t ∈ thetaOrbitSet,
      (Polynomial.X - Polynomial.C (rename g t))) = _
  calc
    (∏ t ∈ thetaOrbitSet,
        (Polynomial.X - Polynomial.C (rename g t))) =
        ∏ t ∈ thetaOrbitSet.image (rename g),
          (Polynomial.X - Polynomial.C t) := by
      exact (Finset.prod_image
        (f := fun t ↦ Polynomial.X - Polynomial.C t)
        (g := rename g)
        (MvPolynomial.rename_injective g g.injective).injOn).symm
    _ = ∏ t ∈ thetaOrbitSet,
          (Polynomial.X - Polynomial.C t) := by
      rw [image_rename_thetaOrbitSet]

theorem universalResolvent_coefficient_isSymmetric (n : ℕ) :
    (universalResolvent.coeff n).IsSymmetric := by
  intro g
  have h := congrArg (fun p : Polynomial (MvPolynomial (Fin 5) ℤ) ↦
    p.coeff n) (universalResolvent_rename g)
  simp only [Polynomial.coeff_map] at h
  change rename g (universalResolvent.coeff n) =
    universalResolvent.coeff n at h
  exact h

/-- A universal resolvent coefficient, regarded as an element of the symmetric
subalgebra. -/
noncomputable def symmetricResolventCoefficient (n : ℕ) :
    MvPolynomial.symmetricSubalgebra (Fin 5) ℤ :=
  ⟨universalResolvent.coeff n, universalResolvent_coefficient_isSymmetric n⟩

/-- The fixed polynomial in the five elementary symmetric functions which
produces the `n`th coefficient of the scalar resolvent. -/
noncomputable def elementaryResolventCoefficient (n : ℕ) :
    MvPolynomial (Fin 5) ℤ :=
  (MvPolynomial.esymmAlgEquiv (Fin 5) ℤ (by simp)).symm
    (symmetricResolventCoefficient n)

theorem esymmAlgEquiv_elementaryResolventCoefficient (n : ℕ) :
    MvPolynomial.esymmAlgEquiv (Fin 5) ℤ (by simp)
        (elementaryResolventCoefficient n) =
      symmetricResolventCoefficient n := by
  exact (MvPolynomial.esymmAlgEquiv (Fin 5) ℤ (by simp)).apply_symm_apply _

/-- Unpacked form of the fundamental theorem of symmetric polynomials for
each universal resolvent coefficient. -/
theorem universalResolvent_coefficient_eq_aeval_esymm (n : ℕ) :
    universalResolvent.coeff n =
      MvPolynomial.aeval
        (fun i : Fin 5 ↦ MvPolynomial.esymm (Fin 5) ℤ (i + 1))
        (elementaryResolventCoefficient n) := by
  have h := congrArg Subtype.val
    (esymmAlgEquiv_elementaryResolventCoefficient n)
  simpa only [MvPolynomial.esymmAlgEquiv_apply,
    MvPolynomial.esymmAlgHom_apply, symmetricResolventCoefficient] using h.symm

/-- The familiar ten-term scalar expression represented by `theta`. -/
def thetaFormula {K : Type*} [CommRing K] (r : Fin 5 → K) : K :=
  r 0 ^ 2 * r 1 * r 4 + r 0 ^ 2 * r 2 * r 3 +
  r 1 ^ 2 * r 0 * r 2 + r 1 ^ 2 * r 3 * r 4 +
  r 2 ^ 2 * r 0 * r 4 + r 2 ^ 2 * r 1 * r 3 +
  r 3 ^ 2 * r 0 * r 1 + r 3 ^ 2 * r 2 * r 4 +
  r 4 ^ 2 * r 0 * r 3 + r 4 ^ 2 * r 1 * r 2

/-- The ten formal monomials of `theta`, in display order. -/
noncomputable def thetaTerm (i : Fin 10) : MvPolynomial (Fin 5) ℤ :=
  ![X 0 ^ 2 * X 1 * X 4, X 0 ^ 2 * X 2 * X 3,
    X 1 ^ 2 * X 0 * X 2, X 1 ^ 2 * X 3 * X 4,
    X 2 ^ 2 * X 0 * X 4, X 2 ^ 2 * X 1 * X 3,
    X 3 ^ 2 * X 0 * X 1, X 3 ^ 2 * X 2 * X 4,
    X 4 ^ 2 * X 0 * X 3, X 4 ^ 2 * X 1 * X 2] i

theorem monomial_thetaExponent_eq_thetaTerm (i : Fin 10) :
    monomial (Finsupp.equivFunOnFinite.symm (thetaExponent i)) 1 =
      thetaTerm i := by
  fin_cases i <;>
    simp [thetaExponent, thetaTerm, MvPolynomial.X,
      MvPolynomial.monomial_pow, MvPolynomial.monomial_mul] <;>
    ext x <;> fin_cases x <;> simp [exponent]

set_option maxHeartbeats 1000000 in
theorem eval₂_theta_eq_thetaFormula {K : Type*} [CommRing K]
    (r : Fin 5 → K) :
    MvPolynomial.eval₂ (Int.castRingHom K) r theta = thetaFormula r := by
  classical
  rw [theta, polynomialOfSupport, thetaSupport,
    Finset.sum_image thetaExponent_injective.injOn]
  simp_rw [monomial_thetaExponent_eq_thetaTerm]
  simp [Fin.sum_univ_succ, thetaTerm, thetaFormula]
  ring

/-- Chapman's first factorization, comparing the `(012)` and `(021)`
conjugates. -/
theorem thetaFormula_threeCycle_sub_inv {K : Type*} [CommRing K]
    (r : Fin 5 → K) :
    thetaFormula (fun i ↦ r (threeCycle i)) -
        thetaFormula (fun i ↦ r (threeCycle.symm i)) =
      (r 0 - r 3) * (r 2 - r 4) *
        ((r 1 - r 0) * (r 1 - r 3) -
          (r 1 - r 2) * (r 1 - r 4)) := by
  rw [threeCycle_symm]
  simp [thetaFormula, threeCycle, Fin5TransitiveC5.threeCycle,
    Equiv.swap_apply_def]
  ring

/-- Chapman's second factorization, comparing the `(01)` and `(12)`
conjugates. -/
theorem thetaFormula_swap_sub_swap {K : Type*} [CommRing K]
    (r : Fin 5 → K) :
    thetaFormula (fun i ↦ r ((Equiv.swap 0 1 : S5) i)) -
        thetaFormula (fun i ↦ r ((Equiv.swap 1 2 : S5) i)) =
      (r 2 - r 3) * (r 0 - r 4) *
        ((r 1 - r 2) * (r 1 - r 3) -
          (r 1 - r 0) * (r 1 - r 4)) := by
  simp [thetaFormula, Equiv.swap_apply_def]
  ring

/-- The algebraic heart of Chapman's no-collision argument.  If the two
pairs of theta-values used in his note collide and the five inputs are
distinct, the distinguished second root is the midpoint of each remaining
pair. -/
theorem chapman_midpoints_of_collisions {K : Type*} [CommRing K] [IsDomain K]
    (r : Fin 5 → K) (hr : Function.Injective r)
    (h23 : thetaFormula (fun i ↦ r (threeCycle i)) =
      thetaFormula (fun i ↦ r (threeCycle.symm i)))
    (h45 : thetaFormula (fun i ↦ r ((Equiv.swap 0 1 : S5) i)) =
      thetaFormula (fun i ↦ r ((Equiv.swap 1 2 : S5) i))) :
    r 1 + r 1 = r 0 + r 2 ∧ r 1 + r 1 = r 3 + r 4 := by
  have h03 : r 0 - r 3 ≠ 0 := sub_ne_zero.mpr (hr.ne (by decide))
  have h24 : r 2 - r 4 ≠ 0 := sub_ne_zero.mpr (hr.ne (by decide))
  have h23' : r 2 - r 3 ≠ 0 := sub_ne_zero.mpr (hr.ne (by decide))
  have h04 : r 0 - r 4 ≠ 0 := sub_ne_zero.mpr (hr.ne (by decide))
  have hA :
      (r 1 - r 0) * (r 1 - r 3) -
          (r 1 - r 2) * (r 1 - r 4) = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left (mul_ne_zero h03 h24)
    rw [← thetaFormula_threeCycle_sub_inv r, h23, sub_self]
  have hB :
      (r 1 - r 2) * (r 1 - r 3) -
          (r 1 - r 0) * (r 1 - r 4) = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left (mul_ne_zero h23' h04)
    rw [← thetaFormula_swap_sub_swap r, h45, sub_self]
  have h20 : r 2 - r 0 ≠ 0 := sub_ne_zero.mpr (hr.ne (by decide))
  have h43 : r 4 - r 3 ≠ 0 := sub_ne_zero.mpr (hr.ne (by decide))
  have hright : (r 1 - r 3) + (r 1 - r 4) = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left h20
    calc
      (r 2 - r 0) * ((r 1 - r 3) + (r 1 - r 4)) =
          ((r 1 - r 0) * (r 1 - r 3) -
            (r 1 - r 2) * (r 1 - r 4)) -
          ((r 1 - r 2) * (r 1 - r 3) -
            (r 1 - r 0) * (r 1 - r 4)) := by ring
      _ = 0 := by rw [hA, hB, sub_self]
  have hleft : (r 1 - r 0) + (r 1 - r 2) = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left h43
    calc
      (r 4 - r 3) * ((r 1 - r 0) + (r 1 - r 2)) =
          ((r 1 - r 0) * (r 1 - r 3) -
            (r 1 - r 2) * (r 1 - r 4)) +
          ((r 1 - r 2) * (r 1 - r 3) -
            (r 1 - r 0) * (r 1 - r 4)) := by ring
      _ = 0 := by rw [hA, hB, zero_add]
  constructor
  · linear_combination hleft
  · linear_combination hright

theorem chapman_five_mul_center {K : Type*} [CommRing K]
    (r : Fin 5 → K)
    (h : r 1 + r 1 = r 0 + r 2 ∧ r 1 + r 1 = r 3 + r 4) :
    5 * r 1 = r 0 + r 1 + r 2 + r 3 + r 4 := by
  rcases h with ⟨hleft, hright⟩
  linear_combination hleft + hright

/-- A collision between two entries of a six-tuple, propagated through the
five-cycle table, contains both pairs used in Chapman's argument. -/
theorem fiveCycle_collision_propagates {α : Type*} (v : Fin 6 → α)
    (hstep : ∀ i j, v i = v j →
      v (Fin5TransitiveC5.fiveCycleOnRepresentatives i) =
        v (Fin5TransitiveC5.fiveCycleOnRepresentatives j))
    {i j : Fin 6} (hne : i ≠ j) (hij : v i = v j) :
    v 1 = v 2 ∧ v 3 = v 4 := by
  have h1 := hstep i j hij
  have h2 := hstep _ _ h1
  have h3 := hstep _ _ h2
  have h4 := hstep _ _ h3
  fin_cases i <;> fin_cases j <;>
    simp_all [Fin5TransitiveC5.fiveCycleOnRepresentatives]

section Specialization

variable {K : Type*} [CommRing K]

/-- Evaluation of the `i`th conjugate of `theta` at an ordered five-tuple. -/
noncomputable def thetaValue (r : Fin 5 → K) (i : Fin 6) : K :=
  MvPolynomial.eval₂ (Int.castRingHom K) r (thetaOrbit i)

theorem thetaValue_eq_thetaFormula (r : Fin 5 → K) (i : Fin 6) :
    thetaValue r i = thetaFormula (fun j ↦ r (representative i j)) := by
  rw [thetaValue, thetaOrbit, MvPolynomial.eval₂_rename,
    eval₂_theta_eq_thetaFormula]
  rfl

/-- Naturality of theta-values: a ring map which relabels a root tuple by
`g` sends an orbit value to the correspondingly renamed orbit value. -/
theorem map_thetaValue_of_maps_roots {L : Type*} [CommRing L]
    (f : K →+* L) (r : Fin 5 → K) (s : Fin 5 → L)
    (g : S5) (i j : Fin 6)
    (hroot : ∀ k, f (r k) = s (g k))
    (horbit : rename g (thetaOrbit i) = thetaOrbit j) :
    f (thetaValue r i) = thetaValue s j := by
  change f ((MvPolynomial.eval₂Hom (Int.castRingHom K) r) (thetaOrbit i)) =
    (MvPolynomial.eval₂Hom (Int.castRingHom L) s) (thetaOrbit j)
  calc
    f ((MvPolynomial.eval₂Hom (Int.castRingHom K) r) (thetaOrbit i)) =
        (MvPolynomial.eval₂Hom
          (f.comp (Int.castRingHom K)) (fun k ↦ f (r k)))
          (thetaOrbit i) :=
      MvPolynomial.map_eval₂Hom (Int.castRingHom K) r f (thetaOrbit i)
    _ = (MvPolynomial.eval₂Hom (Int.castRingHom L)
          (fun k ↦ s (g k))) (thetaOrbit i) := by
      apply MvPolynomial.eval₂Hom_congr
      · exact RingHom.ext_int _ _
      · funext k
        exact hroot k
      · rfl
    _ = (MvPolynomial.eval₂Hom (Int.castRingHom L) s)
          (rename g (thetaOrbit i)) := by
      rw [MvPolynomial.eval₂Hom_rename]
      rfl
    _ = (MvPolynomial.eval₂Hom (Int.castRingHom L) s)
          (thetaOrbit j) := by rw [horbit]

/-- Equivariance of the six scalar theta-values under the standard
five-cycle on an ordered root tuple. -/
theorem map_thetaValue_fiveCycle (r : Fin 5 → K) (σ : K →+* K)
    (hσ : ∀ k, σ (r k) = r (fiveCycle k)) (i : Fin 6) :
    σ (thetaValue r i) =
      thetaValue r (Fin5TransitiveC5.fiveCycleOnRepresentatives i) := by
  exact map_thetaValue_of_maps_roots σ r r fiveCycle i _ hσ
    (rename_fiveCycle_thetaOrbit i)

/-- The scalar sextic obtained by specializing the universal resolvent. -/
noncomputable def scalarResolvent (r : Fin 5 → K) : Polynomial K :=
  universalResolvent.map (MvPolynomial.eval₂Hom (Int.castRingHom K) r)

/-- Relabeling the ordered five-tuple does not change the scalar resolvent. -/
theorem scalarResolvent_permute (r : Fin 5 → K) (g : S5) :
    scalarResolvent (fun i ↦ r (g i)) = scalarResolvent r := by
  let e₁ := MvPolynomial.eval₂Hom (Int.castRingHom K) (fun i ↦ r (g i))
  let e₂ := (MvPolynomial.eval₂Hom (Int.castRingHom K) r).comp
    (rename g).toRingHom
  have heval : e₁ = e₂ := by
    apply MvPolynomial.ringHom_ext
    · intro z
      simp [e₁, e₂]
    · intro i
      simp [e₁, e₂]
  change universalResolvent.map e₁ =
    universalResolvent.map (MvPolynomial.eval₂Hom (Int.castRingHom K) r)
  rw [heval, ← Polynomial.map_map, universalResolvent_rename]

/-- Specialization really has the six scalar theta-values as its roots. -/
theorem scalarResolvent_eq_prod (r : Fin 5 → K) :
    scalarResolvent r =
      ∏ i : Fin 6, (Polynomial.X - Polynomial.C (thetaValue r i)) := by
  classical
  rw [scalarResolvent, universalResolvent, Polynomial.map_prod]
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    thetaOrbitSet, thetaValue]
  rw [Finset.prod_image thetaOrbit_injective.injOn]
  rfl

theorem scalarResolvent_monic (r : Fin 5 → K) :
    (scalarResolvent r).Monic := by
  rw [scalarResolvent_eq_prod]
  exact Polynomial.monic_prod_of_monic _ _ (fun _ _ ↦ Polynomial.monic_X_sub_C _)

theorem scalarResolvent_natDegree [Nontrivial K] (r : Fin 5 → K) :
    (scalarResolvent r).natDegree = 6 := by
  rw [scalarResolvent_eq_prod,
    Polynomial.natDegree_finsetProd_X_sub_C_eq_card]
  simp

theorem scalarResolvent_isRoot_iff [IsDomain K] (r : Fin 5 → K) (x : K) :
    (scalarResolvent r).IsRoot x ↔ ∃ i : Fin 6, thetaValue r i = x := by
  classical
  simp only [Polynomial.IsRoot, scalarResolvent_eq_prod, Polynomial.eval_prod,
    Finset.prod_eq_zero_iff, Finset.mem_univ, true_and, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero]
  constructor <;> rintro ⟨i, hi⟩ <;> exact ⟨i, hi.symm⟩

/-- The specialized coefficients are obtained from the fixed elementary-
symmetric coefficient polynomials. -/
theorem scalarResolvent_coefficient_eq (r : Fin 5 → K) (n : ℕ) :
    (scalarResolvent r).coeff n =
      MvPolynomial.eval₂ (Int.castRingHom K) r
        (MvPolynomial.aeval
          (fun i : Fin 5 ↦ MvPolynomial.esymm (Fin 5) ℤ (i + 1))
          (elementaryResolventCoefficient n)) := by
  rw [scalarResolvent, Polynomial.coeff_map,
    universalResolvent_coefficient_eq_aeval_esymm]
  rfl

/-- Chapman in the indexing of the six scalar resolvent roots. -/
theorem chapman_five_mul_center_of_thetaValue_collisions [IsDomain K]
    (r : Fin 5 → K) (hr : Function.Injective r)
    (h12 : thetaValue r 1 = thetaValue r 2)
    (h34 : thetaValue r 3 = thetaValue r 4) :
    5 * r 1 = r 0 + r 1 + r 2 + r 3 + r 4 := by
  apply chapman_five_mul_center r
  apply chapman_midpoints_of_collisions r hr
  · rw [threeCycle_symm]
    simpa [thetaValue_eq_thetaFormula, representative,
      Fin5TransitiveC5.representative, Fin5TransitiveC5.threeCycle] using h12
  · simpa [thetaValue_eq_thetaFormula, representative,
      Fin5TransitiveC5.representative, Fin5TransitiveC5.threeCycle] using h34

/-- If the sum of the five entries lies in the rational base field, the two
Chapman collisions force the distinguished root itself to be rational. -/
theorem chapman_center_mem_range_of_collisions {L : Type*} [Field L]
    [Algebra ℚ L] (r : Fin 5 → L) (hr : Function.Injective r)
    (h12 : thetaValue r 1 = thetaValue r 2)
    (h34 : thetaValue r 3 = thetaValue r 4)
    (hsum : r 0 + r 1 + r 2 + r 3 + r 4 ∈
      Set.range (algebraMap ℚ L)) :
    r 1 ∈ Set.range (algebraMap ℚ L) := by
  obtain ⟨q, hq⟩ := hsum
  refine ⟨q / 5, ?_⟩
  calc
    algebraMap ℚ L (q / 5) =
        algebraMap ℚ L q / algebraMap ℚ L 5 := by
      simp only [div_eq_mul_inv, _root_.map_mul, _root_.map_inv₀]
    _ = algebraMap ℚ L q / (5 : L) := by norm_num
    _ = r 1 := by
      have h5 : (5 : L) ≠ 0 := by
        intro h
        have h' : algebraMap ℚ L (5 : ℚ) = algebraMap ℚ L 0 := by
          simpa using h
        have := (algebraMap ℚ L).injective h'
        norm_num at this
      apply (div_eq_iff h5).2
      have hc :=
        chapman_five_mul_center_of_thetaValue_collisions r hr h12 h34
      rw [← hq] at hc
      simpa [mul_comm] using hc.symm

/-- The two collisions occurring in Chapman's argument are impossible for
the roots of an irreducible quintic once their sum is rational. -/
theorem not_chapman_collisions_of_irreducible_quintic {L : Type*} [Field L]
    [Algebra ℚ L] (p : Polynomial ℚ) (hp : Irreducible p)
    (hdeg : p.natDegree = 5) (r : Fin 5 → L) (hr : Function.Injective r)
    (hroot : (p.map (algebraMap ℚ L)).IsRoot (r 1))
    (hsum : r 0 + r 1 + r 2 + r 3 + r 4 ∈
      Set.range (algebraMap ℚ L)) :
    ¬(thetaValue r 1 = thetaValue r 2 ∧
      thetaValue r 3 = thetaValue r 4) := by
  rintro ⟨h12, h34⟩
  obtain ⟨q, hq⟩ := chapman_center_mem_range_of_collisions r hr h12 h34 hsum
  apply hp.not_isRoot_of_natDegree_ne_one (by omega : p.natDegree ≠ 1)
  rw [Polynomial.IsRoot]
  have hz : algebraMap ℚ L (p.eval q) = 0 := by
    calc
      algebraMap ℚ L (p.eval q) =
          (p.map (algebraMap ℚ L)).eval (algebraMap ℚ L q) := by
        rw [Polynomial.eval_map]
        exact (Polynomial.eval₂_at_apply (algebraMap ℚ L) q).symm
      _ = (p.map (algebraMap ℚ L)).eval (r 1) := by rw [hq]
      _ = 0 := by simpa [Polynomial.IsRoot] using hroot
  exact (algebraMap ℚ L).injective (by simpa using hz)

/-- Chapman's argument upgrades equivariance under one five-cycle to
pairwise distinctness of all six scalar resolvent roots. -/
theorem thetaValue_injective_of_fiveCycle_action {L : Type*} [Field L]
    [Algebra ℚ L] (p : Polynomial ℚ) (hp : Irreducible p)
    (hdeg : p.natDegree = 5) (r : Fin 5 → L) (hr : Function.Injective r)
    (hroot : (p.map (algebraMap ℚ L)).IsRoot (r 1))
    (hsum : r 0 + r 1 + r 2 + r 3 + r 4 ∈
      Set.range (algebraMap ℚ L))
    (σ : L →+* L) (hσ : ∀ k, σ (r k) = r (fiveCycle k)) :
    Function.Injective (thetaValue r) := by
  intro i j hij
  by_contra hne
  have hstep : ∀ a b,
      thetaValue r a = thetaValue r b →
        thetaValue r (Fin5TransitiveC5.fiveCycleOnRepresentatives a) =
          thetaValue r
            (Fin5TransitiveC5.fiveCycleOnRepresentatives b) := by
    intro a b hab
    have hm := congrArg σ hab
    rw [map_thetaValue_fiveCycle r σ hσ a,
      map_thetaValue_fiveCycle r σ hσ b] at hm
    exact hm
  have hcollisions :=
    fiveCycle_collision_propagates (thetaValue r) hstep hne hij
  exact (not_chapman_collisions_of_irreducible_quintic
    p hp hdeg r hr hroot hsum) hcollisions

end Specialization

end LeanProofs.PolynomialFormulas.FrobeniusDummitResolvent
