import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Group.Arithmetic
import OAI.Combinatorics.Progressions.Linear.AllocatedShortRankWitnessWidth

namespace OAI

section

namespace Erdos3
open scoped Classical

theorem selectedResidueDensityPMF_event_congr_of_density_ne_zero
    {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (D : (K × I → ℤ) → ℝ) (hD0 : ∀ x, 0 ≤ D x)
    (hD : 0 < selectedResidueDensityMass modulus G V D)
    (f g : (K × I → ℤ) → Prop) [DecidablePred f] [DecidablePred g]
    (hfg : ∀ x, D x ≠ 0 → (f x ↔ g x)) :
    (∑' x, (selectedResidueDensityPMF modulus G V hV hZ D hD0 hD x).toReal *
      (if f x then (1 : ℝ) else 0)) =
    ∑' x, (selectedResidueDensityPMF modulus G V hV hZ D hD0 hD x).toReal *
      (if g x then (1 : ℝ) else 0) := by
  apply tsum_congr
  intro x
  by_cases hx : D x = 0
  · rw [selectedResidueDensityPMF_zero_of_density_zero modulus G V hV hZ D hD0 hD x hx]
    simp only [zero_mul]
  · simp only [hfg x hx]

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem largestTestedBadDepth_congr_on_tested {Ω : Type*}
    (A : ℕ → ℕ) (bad other : ℕ → ℕ → Ω → Prop) (p : ℕ) (x : Ω)
    (h : ∀ a, 0 < a → a ≤ A p → (bad p a x ↔ other p a x)) :
    largestTestedBadDepth A bad p x = largestTestedBadDepth A other p x := by
  unfold largestTestedBadDepth
  congr 1
  apply Finset.filter_congr
  intro a ha
  exact h a (Finset.mem_Icc.mp ha).1 (Finset.mem_Icc.mp ha).2

theorem largestBadPrimeProduct_congr_on_tested {Ω : Type*}
    (S : Finset ℕ) (A : ℕ → ℕ) (bad other : ℕ → ℕ → Ω → Prop) (x : Ω)
    (h : ∀ p ∈ S, ∀ a, 0 < a → a ≤ A p → (bad p a x ↔ other p a x)) :
    (∏ p ∈ S, p ^ largestTestedBadDepth A bad p x) =
      ∏ p ∈ S, p ^ largestTestedBadDepth A other p x := by
  apply Finset.prod_congr rfl
  intro p hp
  rw [largestTestedBadDepth_congr_on_tested A bad other p x (h p hp)]

theorem selectedResidueDensityPMF_badProduct_event_congr
    {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (D : (K × I → ℤ) → ℝ) (hD0 : ∀ x, 0 ≤ D x)
    (hD : 0 < selectedResidueDensityMass modulus G V D)
    (S : Finset ℕ) (A : ℕ → ℕ)
    (bad other : ℕ → ℕ → (K × I → ℤ) → Prop) (R : ℕ)
    (heq : ∀ x, D x ≠ 0 → ∀ p ∈ S, ∀ a, 0 < a → a ≤ A p →
      (bad p a x ↔ other p a x)) :
    (∑' x, (selectedResidueDensityPMF modulus G V hV hZ D hD0 hD x).toReal *
      (if R < ∏ p ∈ S, p ^ largestTestedBadDepth A bad p x then (1 : ℝ) else 0)) =
      ∑' x, (selectedResidueDensityPMF modulus G V hV hZ D hD0 hD x).toReal *
        (if R < ∏ p ∈ S, p ^ largestTestedBadDepth A other p x then (1 : ℝ) else 0) := by
  apply selectedResidueDensityPMF_event_congr_of_density_ne_zero
  intro x hx
  rw [largestBadPrimeProduct_congr_on_tested S A bad other x (heq x hx)]

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical

private theorem finite_nat_sup_measurable {Ω ι : Type*} [MeasurableSpace Ω]
    (s : Finset ι) (f : ι → Ω → ℕ) (hf : ∀ i ∈ s, Measurable (f i)) :
    Measurable (fun x => s.sup (fun i => f i x)) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sup_insert]
    exact (hf i (Finset.mem_insert_self _ _)).sup
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem largestTestedBadDepth_measurable {Ω : Type*} [MeasurableSpace Ω]
    (A : ℕ → ℕ) (bad : ℕ → ℕ → Ω → Prop) (p : ℕ)
    (hbad : ∀ a ∈ Finset.Icc 1 (A p), MeasurableSet {x | bad p a x}) :
    Measurable (largestTestedBadDepth A bad p) := by
  unfold largestTestedBadDepth
  have h := finite_nat_sup_measurable (Finset.Icc 1 (A p))
    (fun a x => if bad p a x then a else 0)
    (fun a ha => Measurable.ite (hbad a ha) measurable_const measurable_const)
  convert h using 1
  funext x
  rw [Finset.sup_ite]
  simp only [show (0 : ℕ) = ⊥ from rfl, Finset.sup_bot, sup_bot_eq]
  rfl

theorem largestBadPrimeProduct_measurable {Ω : Type*} [MeasurableSpace Ω]
    (P : Finset ℕ) (A : ℕ → ℕ) (bad : ℕ → ℕ → Ω → Prop)
    (hbad : ∀ p ∈ P, ∀ a ∈ Finset.Icc 1 (A p), MeasurableSet {x | bad p a x}) :
    Measurable (fun x => ∏ p ∈ P, p ^ largestTestedBadDepth A bad p x) := by
  apply Finset.measurable_prod
  intro p hp
  exact (measurable_of_countable (fun a : ℕ => p ^ a)).comp
    (largestTestedBadDepth_measurable A bad p (hbad p hp))

theorem largestBadPrimeProduct_tail_measurableSet {Ω : Type*} [MeasurableSpace Ω]
    (P : Finset ℕ) (A : ℕ → ℕ) (bad : ℕ → ℕ → Ω → Prop)
    (hbad : ∀ p ∈ P, ∀ a ∈ Finset.Icc 1 (A p), MeasurableSet {x | bad p a x})
    (cutoff : ℕ) :
    MeasurableSet {x | cutoff < ∏ p ∈ P, p ^ largestTestedBadDepth A bad p x} :=
  measurableSet_lt measurable_const (largestBadPrimeProduct_measurable P A bad hbad)

theorem density_mul_badPrimeProduct_indicator_measurable {Ω : Type*} [MeasurableSpace Ω]
    (D : Ω → ℝ) (hD : Measurable D)
    (P : Finset ℕ) (A : ℕ → ℕ) (bad test : ℕ → ℕ → Ω → Prop)
    (htest : ∀ p ∈ P, ∀ a ∈ Finset.Icc 1 (A p), MeasurableSet {x | test p a x})
    (heq : ∀ x, D x ≠ 0 → ∀ p ∈ P, ∀ a, 0 < a → a ≤ A p →
      (bad p a x ↔ test p a x)) (cutoff : ℕ) :
    Measurable (fun x => D x *
      (if cutoff < ∏ p ∈ P, p ^ largestTestedBadDepth A bad p x then (1 : ℝ) else 0)) := by
  have he (x : Ω) : D x *
      (if cutoff < ∏ p ∈ P, p ^ largestTestedBadDepth A bad p x then (1 : ℝ) else 0) =
      D x * (if cutoff < ∏ p ∈ P, p ^ largestTestedBadDepth A test p x then (1 : ℝ) else 0) := by
    by_cases hx : D x = 0
    · simp only [hx, zero_mul]
    · rw [largestBadPrimeProduct_congr_on_tested P A bad test x (heq x hx)]
  simp_rw [he]
  exact hD.mul (Measurable.ite (largestBadPrimeProduct_tail_measurableSet P A test htest cutoff)
    measurable_const measurable_const)

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped Classical

variable {K : Type*} {m : ℕ} {J I E : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

theorem exists_coefficientDeck_integer_lift (c : CoefficientArray (K := K) U)
    (x : CoefficientSamplerArrays (K := K) I n)
    (hx : canonicalCoefficientSample U b hb o x =
      QuotientAddGroup.mk' (coefficientIntegerLattice U) c) :
    ∃ w : ∀ j : Fin m, BoundedCoefficientExponent K (j.val + 1) → E j → ℤ,
      ∀ (q : ℕ) (hq : 0 < q),
      canonicalCoefficientDeckSample U bW b hb o q hq x
          (fun j e => integerResidueMap (E j) q (w j e)) =
        QuotientAddGroup.mk' (coefficientIntegerLattice U) ((q : ℝ)⁻¹ • c) := by
  have hp (j : Fin m) (e : BoundedCoefficientExponent K (j.val + 1)) :
      QuotientAddGroup.mk' _ ((euclideanSubspaceArrayEquiv (U j)).symm (fun _ => c ⟨j, e⟩)) =
        normalizedLatticeQuotient (euclideanSubspace (U j)) (b j) (hb j)
          (orthonormalMixedChart (o j) (mixedArrayRegroup _ _ _ (x j) e)) := by
    have h := congrArg (fun y => euclideanCoefficientEquiv U y j e) hx
    simpa only [canonicalCoefficientSample, AddEquiv.apply_symm_apply,
      euclideanCoefficientEquiv_mk, mixedArrayQuotient] using h.symm
  choose w hw using fun (j : Fin m) (e : BoundedCoefficientExponent K (j.val + 1)) =>
    exists_normalized_representative_offset (euclideanSubspace (U j)) (bW j) (b j) (hb j)
      ((euclideanSubspaceArrayEquiv (U j)).symm (fun _ => c ⟨j, e⟩))
      (orthonormalMixedChart (o j) (mixedArrayRegroup _ _ _ (x j) e)) (hp j e)
  refine ⟨w, ?_⟩
  intro q hq
  apply (euclideanCoefficientEquiv U).injective
  funext j e
  rw [canonicalCoefficientDeckSample_coordinate, normalizedCoverLift_add_deck, hw,
    euclideanCoefficientEquiv_mk]
  congr 1

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule

variable {K : Type*} {m : ℕ} {J I E : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

theorem exists_coefficientDeck_integer_event_read
    (c : CoefficientArray (K := K) U) (x : CoefficientSamplerArrays (K := K) I n)
    (hx : canonicalCoefficientSample U b hb o x = QuotientAddGroup.mk' (coefficientIntegerLattice U) c)
    (hsmall : ∀ a, |coefficientSamplerAmbientPoint U b o x a| < 1/2) :
    ∃ w : ∀ j, BoundedCoefficientExponent K (j.val + 1) → E j → ℤ,
      ∀ (q : ℕ) (hq : 0 < q), letI : NeZero q := ⟨hq.ne'⟩
        ∀ event : CoefficientChartResidues K n E q → Prop,
          coefficientDeckChartEvent U bW b hb o q event
            (QuotientAddGroup.mk' (coefficientIntegerLattice U) ((q : ℝ)⁻¹ • c)) ↔
          event (coefficientSamplerChartResidues q x
            (fun j e => integerResidueMap (E j) q (w j e))) := by
  obtain ⟨w, hw⟩ := exists_coefficientDeck_integer_lift U bW b hb o c x hx
  refine ⟨w, ?_⟩
  intro q hq
  let : NeZero q := ⟨hq.ne'⟩
  intro event
  rw [← hw q (NeZero.pos q)]
  exact coefficientDeckChartEvent_sample_iff U bW b hb o q event x hsmall _

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped Classical

variable {m : ℕ} {G X : Type*} {J I E : Fin m → Type*} {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

theorem exists_allocatedCoefficient_integer_event_read
    (c : CoefficientArray (K := LayerSamplerVariables G I n B) U)
    (x : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (hx : canonicalCoefficientSample U b hb o x = QuotientAddGroup.mk' (coefficientIntegerLattice U) c)
    (hsmall : ∀ a, |coefficientSamplerAmbientPoint U b o x a| < 1/2)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ) :
    ∃ f : AllocatedActualCoefficientIndex G X I E n B → ℤ,
      allocatedReadNoise f = noise ∧
      (∀ (j : Fin m) (i : Fin (n j))
        (e : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)),
        allocatedReadProjection f ⟨j, Sum.inr i⟩ e = (x j).2 i e) ∧
      ∀ (q : ℕ) (hq : 0 < q), letI : NeZero q := ⟨hq.ne'⟩
        ∀ event : CoefficientChartResidues (LayerSamplerVariables G I n B) n E q → Prop,
          coefficientDeckChartEvent U bW b hb o q event
            (QuotientAddGroup.mk' (coefficientIntegerLattice U) ((q : ℝ)⁻¹ • c)) ↔
          event (allocatedReadCoefficientChartResidues (fun i => (f i : ZMod q))) := by
  obtain ⟨w, hw⟩ := exists_coefficientDeck_integer_event_read U bW b hb o c x hx hsmall
  let f : AllocatedActualCoefficientIndex G X I E n B → ℤ :=
    allocatedMixedFullArray (Sum.elim noise (fun ⟨j,e,i⟩ => (x j).2 i e))
      (fun ⟨j,e,i⟩ => w j e i) (fun _ => 0)
  have hi (j : Fin m) (i : Fin (n j))
      (e : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) :
      allocatedReadProjection f ⟨j, Sum.inr i⟩ e = (x j).2 i e := rfl
  refine ⟨f, rfl, hi, ?_⟩
  intro q hq
  let : NeZero q := ⟨hq.ne'⟩
  intro event
  rw [allocatedReadCoefficientChartResidues_sampler q f x hi]
  exact hw q hq event

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped Classical

variable {m : ℕ} {G X : Type*} [Fintype G] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)

theorem exists_allocatedPhysical_integer_coefficient_read :
    ∃ read : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
        AllocatedActualCoefficientIndex G X I E n B → ℤ,
      ∀ z, allocatedReadNoise (read z) = z ∧
        (allocatedCoefficientDensity B U b hb o hR hσ S
          (affineSampleCoefficientTorus U poly hm (fun k x => (z (k,x) : ℝ))) ≠ 0 →
        ∀ (q : ℕ) (hq : 0 < q), letI : NeZero q := ⟨hq.ne'⟩
          ∀ event : CoefficientChartResidues (LayerSamplerVariables G I n B) n E q → Prop,
            coefficientDeckChartEvent U bW b hb o q event
              (affineCoefficientCoverSample U poly hm q (fun k x => (z (k,x) : ℝ))) ↔
            event (allocatedReadCoefficientChartResidues (fun i => (read z i : ZMod q)))) := by
  have hex (z : Option (LayerSamplerVariables G I n B) × X → ℤ) :
      ∃ f : AllocatedActualCoefficientIndex G X I E n B → ℤ,
        allocatedReadNoise f = z ∧
        (allocatedCoefficientDensity B U b hb o hR hσ S
          (affineSampleCoefficientTorus U poly hm (fun k x => (z (k,x) : ℝ))) ≠ 0 →
        ∀ (q : ℕ) (hq : 0 < q), letI : NeZero q := ⟨hq.ne'⟩
          ∀ event : CoefficientChartResidues (LayerSamplerVariables G I n B) n E q → Prop,
            coefficientDeckChartEvent U bW b hb o q event
              (affineCoefficientCoverSample U poly hm q (fun k x => (z (k,x) : ℝ))) ↔
            event (allocatedReadCoefficientChartResidues (fun i => (f i : ZMod q)))) := by
    by_cases hz : allocatedCoefficientDensity B U b hb o hR hσ S
        (affineSampleCoefficientTorus U poly hm (fun k x => (z (k,x) : ℝ))) = 0
    · refine ⟨allocatedMixedFullArray (Sum.elim z (fun _ => 0)) (fun _ => 0) (fun _ => 0), rfl, ?_⟩
      intro h
      exact (h hz).elim
    · obtain ⟨x, hx, _⟩ := canonicalCoefficientDensity_recover_unique U b hb o
        (allocatedLayerCenters B U b S) (allocatedLayerWidths B U b S)
        (allocatedLayerIntegerPMFs B U b hR hσ S) hz
      have hsmall : ∀ a, |coefficientSamplerAmbientPoint U b o x a| < 1/2 := by
        intro a
        exact (hx.2 a.1.1).1 a.1.2 a.2
      obtain ⟨f, hfnoise, _hfint, hfevent⟩ := exists_allocatedCoefficient_integer_event_read
        U bW b hb o (affineSampleCoefficientArray U poly hm (fun k x => (z (k,x) : ℝ)))
        x hx.1 hsmall z
      refine ⟨f, hfnoise, ?_⟩
      intro _ q hq
      exact hfevent q hq
  choose read hread using hex
  exact ⟨read, hread⟩

variable [Fintype X]

theorem exists_allocatedPhysical_integer_rank_read
    (inactive : LayerSamplerAxis I n → Prop) {L : ℕ} (spatial : Fin L ↪ G)
    (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j,a.val⟩)
    (C : ℝ) :
    ∃ read : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
        AllocatedActualCoefficientIndex G X I E n B → ℤ,
      ∀ z, allocatedReadNoise (read z) = z ∧
        (allocatedCoefficientDensity B U b hb o hR hσ S
          (affineSampleCoefficientTorus U poly hm (fun k x => (z (k,x) : ℝ))) ≠ 0 →
        ∀ (P : Finset ℕ) (hP : ∀ p : P, NeZero p.val), letI := hP
          ∀ (A : ℕ → ℕ) (M : ℕ) (hM : 0 < M), letI : NeZero M := ⟨hM.ne'⟩
            ∀ hdiv : ∀ p : P, p.val ^ A p.val ∣ M,
              coefficientDeckChartEvent U bW b hb o M
                (allocatedChartResiduePrimePowerWitness inactive C P A M hdiv
                  (fun v => (z v : ZMod M)))
                (affineCoefficientCoverSample U poly hm M (fun k x => (z (k,x) : ℝ))) ↔
              ∀ p : P, allocatedActualModulusBad inactive spatial kernel block C
                (p.val ^ A p.val) (read z)) := by
  obtain ⟨read, hread⟩ := exists_allocatedPhysical_integer_coefficient_read
    B U bW b hb o S hR hσ poly hm
  refine ⟨read, ?_⟩
  intro z
  refine ⟨(hread z).1, ?_⟩
  intro hz P hP
  let := hP
  intro A M hM
  let : NeZero M := ⟨hM.ne'⟩
  intro hdiv
  have he := (hread z).2 hz M hM
    (allocatedChartResiduePrimePowerWitness inactive C P A M hdiv
      (fun v => (z v : ZMod M)))
  apply he.trans
  have hn : allocatedReadNoise (fun i => (read z i : ZMod M)) =
      fun v => (z v : ZMod M) := by
    funext v
    change ((allocatedReadNoise (read z) v : ℤ) : ZMod M) = _
    rw [(hread z).1]
  rw [← hn]
  exact allocatedChartResiduePrimePowerWitness_iff_actual
    inactive spatial kernel block C P A M hdiv (read z)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)

local notation "Dphysical" => (fun z : Option (LayerSamplerVariables G I n B) × X → ℤ =>
  allocatedCoefficientDensity B U b hb o hR hσ S
    (affineSampleCoefficientTorus U poly hm (fun k x => (z (k,x) : ℝ))))

theorem exists_allocatedPhysical_integer_rank_law
    (inactive : LayerSamplerAxis I n → Prop) {L : ℕ} (spatial : Fin L ↪ G)
    (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j,a.val⟩)
    (C : ℝ) (stride : X → ℕ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
    (width : Option (LayerSamplerVariables G I n B) × X → ℝ) (hwidth : ∀ z, 0 < width z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells width z)
    (hD0 : ∀ z, 0 ≤ Dphysical z)
    (hDpos : 0 < selectedResidueDensityMass stride cells width Dphysical) :
    ∃ read : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
        AllocatedActualCoefficientIndex G X I E n B → ℤ,
      (∀ z, allocatedReadNoise (read z) = z) ∧
      ∀ (P : Finset ℕ) (hP : ∀ p : P, NeZero p.val), letI := hP
        ∀ (A : ℕ → ℕ) (M : ℕ) (hM : 0 < M), letI : NeZero M := ⟨hM.ne'⟩
          ∀ hdiv : ∀ p : P, p.val ^ A p.val ∣ M,
            (∑' z, (selectedResidueDensityPMF stride cells width hwidth hZ Dphysical hD0 hDpos z).toReal *
              (if coefficientDeckChartEvent U bW b hb o M
                (allocatedChartResiduePrimePowerWitness inactive C P A M hdiv
                  (fun v => (z v : ZMod M)))
                (affineCoefficientCoverSample U poly hm M (fun k x => (z (k,x) : ℝ))) then (1 : ℝ) else 0)) =
            ∑' z, (selectedResidueDensityPMF stride cells width hwidth hZ Dphysical hD0 hDpos z).toReal *
              (if ∀ p : P, allocatedActualModulusBad inactive spatial kernel block C
                (p.val ^ A p.val) (read z) then (1 : ℝ) else 0) := by
  obtain ⟨read, hread⟩ := exists_allocatedPhysical_integer_rank_read
    B U bW b hb o S hR hσ poly hm inactive spatial kernel block C
  refine ⟨read, fun z => (hread z).1, ?_⟩
  intro P hP
  let := hP
  intro A M hM
  let : NeZero M := ⟨hM.ne'⟩
  intro hdiv
  apply selectedResidueDensityPMF_event_congr_of_density_ne_zero
  intro z hz
  exact (hread z).2 hz P hP A M hM hdiv

end Erdos3.VectorPolynomial

end

end OAI
