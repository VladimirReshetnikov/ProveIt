import OAI.Combinatorics.Progressions.Polynomial.CRTPolynomialInputStepLaw
import OAI.Combinatorics.Progressions.Sampling.AllocatedPeriodicGridQuadrature

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem integerBox_residue_fiberLaw_l1
    {I : Type*} [Fintype I] [DecidableEq I]
    (lo hi : I → ℤ) (hlen : ∀ i, lo i < hi i) (q : ℕ) [NeZero q]
    (hsmall : (∑ i, (q : ℝ) / ((hi i - lo i : ℤ) : ℝ)) ≤ 1 / 2) :
    (∑ r : I → ZMod q,
      |((integerBoxUniformWeights lo hi hlen).fiberLaw
        (fun x => integerVectorResidue q (fun i => (x i).val))).weight r -
        (FiniteProbabilityWeights.uniform (I → ZMod q)).weight r|) ≤
      2 * ∑ i, (q : ℝ) / ((hi i - lo i : ℤ) : ℝ) := by
  let E := 2 * ∑ i, (q : ℝ) / ((hi i - lo i : ℤ) : ℝ)
  let μ := (integerBoxUniformWeights lo hi hlen).fiberLaw
    (fun x => integerVectorResidue q (fun i => (x i).val))
  let u := FiniteProbabilityWeights.uniform (I → ZMod q)
  have hc : (0 : ℝ) < (q : ℝ) ^ Fintype.card I := pow_pos (by exact_mod_cast NeZero.pos q) _
  have hw (r : I → ZMod q) : |μ.weight r - u.weight r| ≤ E * u.weight r := by
    have h := integerBox_residue_fiberLaw_relative_error lo hi hlen q r hsmall
    change |(q : ℝ) ^ Fintype.card I * μ.weight r - 1| ≤ E at h
    have hu : u.weight r = ((q : ℝ) ^ Fintype.card I)⁻¹ := by
      simp only [u, FiniteProbabilityWeights.uniform, Fintype.card_fun, ZMod.card, Nat.cast_pow]
    rw [hu]
    have heq : μ.weight r - ((q : ℝ) ^ Fintype.card I)⁻¹ =
        ((q : ℝ) ^ Fintype.card I * μ.weight r - 1) * ((q : ℝ) ^ Fintype.card I)⁻¹ := by
      field_simp
    rw [heq, abs_mul, abs_of_pos (inv_pos.mpr hc)]
    exact mul_le_mul_of_nonneg_right h (inv_nonneg.mpr hc.le)
  calc
    _ ≤ ∑ r, E * u.weight r := Finset.sum_le_sum (fun r _ => hw r)
    _ = E := by rw [← Finset.mul_sum, u.total, mul_one]

theorem integerBox_affine_residue_complexMean_error
    {I Y : Type*} [Fintype I] [DecidableEq I]
    (lo hi : I → ℤ) (hlen : ∀ i, lo i < hi i) (q : ℕ) [NeZero q]
    (origin stride : I → ℤ) (F : (I → ZMod q) → Y) (f : Y → ℂ)
    (hf : ∀ y, ‖f y‖ ≤ 1)
    (hsmall : (∑ i, (q : ℝ) / ((hi i - lo i : ℤ) : ℝ)) ≤ 1 / 2) :
    ‖(integerBoxUniformWeights lo hi hlen).complexMean
        (fun x => f (F (fun i => ((origin i + stride i * (x i).val : ℤ) : ZMod q)))) -
      (FiniteProbabilityWeights.uniform (I → ZMod q)).complexMean
        (fun r => f (F (fun i => (origin i : ZMod q) + (stride i : ZMod q) * r i)))‖ ≤
      2 * ∑ i, (q : ℝ) / ((hi i - lo i : ℤ) : ℝ) := by
  let μ := (integerBoxUniformWeights lo hi hlen).fiberLaw
    (fun x => integerVectorResidue q (fun i => (x i).val))
  let g := fun r : I → ZMod q => f (F (fun i => (origin i : ZMod q) + (stride i : ZMod q) * r i))
  have h := (FiniteProbabilityWeights.norm_complexMean_sub_le_weight_l1 μ
    (FiniteProbabilityWeights.uniform (I → ZMod q)) g (fun r => hf _)).trans
      (integerBox_residue_fiberLaw_l1 lo hi hlen q hsmall)
  dsimp only [μ] at h
  rw [FiniteProbabilityWeights.fiberLaw_complexMean] at h
  simpa only [g, integerVectorResidue, Int.cast_add, Int.cast_mul] using h

theorem integerBox_affine_residue_complexMean_error_unconditional
    {I Y : Type*} [Fintype I] [DecidableEq I]
    (lo hi : I → ℤ) (hlen : ∀ i, lo i < hi i) (q : ℕ) [NeZero q]
    (origin stride : I → ℤ) (F : (I → ZMod q) → Y) (f : Y → ℂ)
    (hf : ∀ y, ‖f y‖ ≤ 1) :
    ‖(integerBoxUniformWeights lo hi hlen).complexMean
        (fun x => f (F (fun i => ((origin i + stride i * (x i).val : ℤ) : ZMod q)))) -
      (FiniteProbabilityWeights.uniform (I → ZMod q)).complexMean
        (fun r => f (F (fun i => (origin i : ZMod q) + (stride i : ZMod q) * r i)))‖ ≤
      4 * ∑ i, (q : ℝ) / ((hi i - lo i : ℤ) : ℝ) := by
  by_cases hsmall : (∑ i, (q : ℝ) / ((hi i - lo i : ℤ) : ℝ)) ≤ 1 / 2
  · apply (integerBox_affine_residue_complexMean_error lo hi hlen q origin stride F f hf hsmall).trans
    have hn : 0 ≤ ∑ i, (q : ℝ) / ((hi i - lo i : ℤ) : ℝ) :=
      Finset.sum_nonneg (fun i _ => div_nonneg (Nat.cast_nonneg _)
        (by exact_mod_cast (sub_pos.mpr (hlen i)).le))
    linarith
  · have h1 := (integerBoxUniformWeights lo hi hlen).norm_complexMean_le_mean_norm
      (fun x => f (F (fun i => ((origin i + stride i * (x i).val : ℤ) : ZMod q))))
    have h2 := (FiniteProbabilityWeights.uniform (I → ZMod q)).norm_complexMean_le_mean_norm
      (fun r => f (F (fun i => (origin i : ZMod q) + (stride i : ZMod q) * r i)))
    have hb1 := (integerBoxUniformWeights lo hi hlen).mean_mono (fun x => hf
      (F (fun i => ((origin i + stride i * (x i).val : ℤ) : ZMod q))))
    have hb2 := (FiniteProbabilityWeights.uniform (I → ZMod q)).mean_mono (fun r => hf
      (F (fun i => (origin i : ZMod q) + (stride i : ZMod q) * r i)))
    rw [FiniteProbabilityWeights.mean_const] at hb1 hb2
    have ht := norm_sub_le
      ((integerBoxUniformWeights lo hi hlen).complexMean
        (fun x => f (F (fun i => ((origin i + stride i * (x i).val : ℤ) : ZMod q)))))
      ((FiniteProbabilityWeights.uniform (I → ZMod q)).complexMean
        (fun r => f (F (fun i => (origin i : ZMod q) + (stride i : ZMod q) * r i))))
    linarith

theorem originalActiveCube_affine_residue_complexMean_error
    {I Y : Type*} [Fintype I] [DecidableEq I]
    (L : I → ℕ) (hL : ∀ i, 0 < L i) (q : ℕ) [NeZero q]
    (origin stride : I → ℤ) (F : (I → ZMod q) → Y) (f : Y → ℂ)
    (hf : ∀ y, ‖f y‖ ≤ 1) :
    ‖(FiniteProbabilityWeights.pi (fun i => integerScalarCubeWeights Empty (L i) (hL i))).complexMean
        (fun x => f (F (fun i => ((origin i + stride i * (x i none : ℤ) : ℤ) : ZMod q)))) -
      (FiniteProbabilityWeights.uniform (I → ZMod q)).complexMean
        (fun r => f (F (fun i => (origin i : ZMod q) + (stride i : ZMod q) * r i)))‖ ≤
      4 * ∑ i, (q : ℝ) / L i := by
  have he := FiniteProbabilityWeights.complexMean_pi_transport_fintype
    (fun i => integerScalarCubeWeights Empty (L i) (hL i))
    (fun i => intervalUniformWeights 0 (L i : ℤ) (by exact_mod_cast hL i))
    (fun _ x => (x none : ℤ)) (fun _ x => (x : ℤ))
    (fun i g => integerScalarCubeWeights_zero_complexMean Empty (L i) (hL i) g)
    (fun z : I → ℤ => f (F (fun i => ((origin i + stride i * z i : ℤ) : ZMod q))))
  rw [he]
  simpa only [integerBoxUniformWeights, sub_zero, Int.cast_natCast] using
    integerBox_affine_residue_complexMean_error_unconditional (fun _ => 0)
      (fun i => (L i : ℤ)) (fun i => by exact_mod_cast hL i) q origin stride F f hf

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical
variable {L V : Type*} [Fintype L] [Fintype V]
local instance activeCRTModulusNeZero (p A : L → ℕ) [∀ l, NeZero (p l)] :
    NeZero (∏ l, p l ^ A l) :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun l _ => pow_ne_zero _ (NeZero.ne (p l)))⟩

theorem originalActiveCube_crt_input_comparison
    (length : V → ℕ) (hlength : ∀ v, 0 < length v)
    (p A e : L → ℕ) [∀ l, NeZero (p l)]
    (hp : ∀ l, (p l).Prime) (hinj : Function.Injective p)
    (hq : Pairwise (fun l k => (p l ^ A l).Coprime (p k ^ A k)))
    (origin : ∀ l, V → ZMod (p l ^ A l))
    {q : ℕ} [NeZero q] (hdiv : q ∣ ∏ l, p l ^ A l)
    (f : (V → ZMod q) → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    let c : V → ℤ := fun v => (crtInput (fun l => p l ^ A l) hq origin v).val
    let step : ℤ := (∏ l, p l ^ e l : ℕ)
    ‖(FiniteProbabilityWeights.pi (fun v => integerScalarCubeWeights Empty (length v) (hlength v))).complexMean
        (fun x => f (fun v => ((c v + step * (x v none : ℤ) : ℤ) : ZMod q))) -
      (crtPolynomialInputLaw p A e hq origin).complexMean
        (fun x => f (tupleResidueReduction hdiv x))‖ ≤
      4 * ∑ v, (q : ℝ) / length v := by
  intro c step
  rw [crtPolynomialInputLaw_divisor_integerOrigin_complexMean p A e hp hinj hq origin hdiv f]
  simpa only [c, step, Int.cast_natCast, id_eq] using
    originalActiveCube_affine_residue_complexMean_error length hlength q c (fun _ => step) id f hf

theorem crtPolynomialInputLaw_unrestricted_divisor_complexMean
    (p A : L → ℕ) [∀ l, NeZero (p l)]
    (hp : ∀ l, (p l).Prime) (hinj : Function.Injective p)
    (hq : Pairwise (fun l k => (p l ^ A l).Coprime (p k ^ A k)))
    (origin : ∀ l, V → ZMod (p l ^ A l))
    {q : ℕ} [NeZero q] (hdiv : q ∣ ∏ l, p l ^ A l)
    (f : (V → ZMod q) → ℂ) :
    (crtPolynomialInputLaw p A (fun _ => 0) hq origin).complexMean
        (fun x => f (tupleResidueReduction hdiv x)) =
      (FiniteProbabilityWeights.uniform (V → ZMod q)).complexMean f := by
  rw [crtPolynomialInputLaw_divisor_complexMean p A (fun _ => 0) hp hinj hq origin hdiv f]
  simp only [pow_zero, Finset.prod_const_one, Nat.cast_one, one_mul]
  rw [FiniteProbabilityWeights.uniform_complexMean, FiniteProbabilityWeights.uniform_complexMean]
  exact Fintype.expect_equiv
    (Equiv.addLeft (tupleResidueReduction hdiv (crtInput (fun l => p l ^ A l) hq origin)))
    _ _ (fun _ => rfl)

theorem originalActiveCube_crt_unrestricted_input_comparison
    (length : V → ℕ) (hlength : ∀ v, 0 < length v)
    (p A : L → ℕ) [∀ l, NeZero (p l)]
    (hp : ∀ l, (p l).Prime) (hinj : Function.Injective p)
    (hq : Pairwise (fun l k => (p l ^ A l).Coprime (p k ^ A k)))
    (origin : ∀ l, V → ZMod (p l ^ A l))
    {q : ℕ} [NeZero q] (hdiv : q ∣ ∏ l, p l ^ A l)
    (f : (V → ZMod q) → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    ‖(FiniteProbabilityWeights.pi (fun v => integerScalarCubeWeights Empty (length v) (hlength v))).complexMean
        (fun x => f (fun v => ((x v none : ℤ) : ZMod q))) -
      (crtPolynomialInputLaw p A (fun _ => 0) hq origin).complexMean
        (fun x => f (tupleResidueReduction hdiv x))‖ ≤
      4 * ∑ v, (q : ℝ) / length v := by
  rw [crtPolynomialInputLaw_unrestricted_divisor_complexMean p A hp hinj hq origin hdiv f]
  simpa only [zero_add, one_mul, Int.cast_one, Int.cast_zero, id_eq] using
    originalActiveCube_affine_residue_complexMean_error length hlength q (fun _ => 0)
      (fun _ => 1) id f hf

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {L A I J : Type*} [Fintype L] [Fintype A] [Fintype J] [DecidableEq J]

local instance unrestrictedForecastModulusNeZero (p e : L → ℕ) [∀ l, NeZero (p l)] :
    NeZero (∏ l, p l ^ e l) :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun l _ => pow_ne_zero _ (NeZero.ne (p l)))⟩

theorem rationalPolynomialForecast_unrestrictedCRT_marginal
    (p e : L → ℕ) [∀ l, NeZero (p l)]
    (hp : ∀ l, (p l).Prime) (hinj : Function.Injective p)
    (hcoprime : Pairwise (fun l k => (p l ^ e l).Coprime (p k ^ e k)))
    (origin : ∀ l, A → ZMod (p l ^ e l))
    (poly : J → MvPolynomial (A ⊕ I) ℤ) (inactive : I → ℤ)
    {q : ℕ} [NeZero q] (hdiv : q ∣ ∏ l, p l ^ e l)
    (test : (J → ZMod q) → ℂ) :
    (𝔼 b : J → ZMod (∏ l, p l ^ e l),
      (rationalOutputDensity (crtPolynomialInputLaw p e (fun _ => 0) hcoprime origin)
        (integerLongPolynomialOutput poly inactive (∏ l, p l ^ e l))
        (∏ l, p l ^ e l) b : ℂ) *
        test (fun j => ZMod.castHom hdiv (ZMod q) (b j))) =
      𝔼 t : A → ZMod q, test (fun j => MvPolynomial.eval₂ (Int.castRingHom (ZMod q))
        (Sum.elim t (fun i => (inactive i : ZMod q))) (poly j)) := by
  rw [rationalOutputDensity_divisor_test _ _ hdiv]
  simp_rw [integerLongPolynomialOutput_reduce poly inactive hdiv]
  exact (crtPolynomialInputLaw_unrestricted_divisor_complexMean p e hp hinj hcoprime origin hdiv
    (fun t => test (fun j => MvPolynomial.eval₂ (Int.castRingHom (ZMod q))
      (Sum.elim t (fun i => (inactive i : ZMod q))) (poly j)))).trans
        (FiniteProbabilityWeights.uniform_complexMean _)

theorem rationalInactivePolynomialForecast_conditionalUnrestrictedCRT_tsum_marginal
    {Ω Z : Type*} [Fintype Ω]
    (inactive : FiniteProbabilityWeights Ω) (gridPoint : Ω → Z)
    (p e : L → ℕ) [∀ l, NeZero (p l)]
    (hp : ∀ l, (p l).Prime) (hinj : Function.Injective p)
    (hcoprime : Pairwise (fun l k => (p l ^ e l).Coprime (p k ^ e k)))
    (origin : Ω → ∀ l, A → ZMod (p l ^ e l))
    (poly : J → MvPolynomial (A ⊕ I) ℤ) (inactiveCoord : Ω → I → ℤ)
    {q : ℕ} [NeZero q] (hdiv : q ∣ ∏ l, p l ^ e l)
    {gridVolume : ℝ} (hV : gridVolume ≠ 0) (test : Z → (J → ZMod q) → ℂ) :
    (∑' z, 𝔼 b : J → ZMod (∏ l, p l ^ e l),
      ((rationalInactiveForecast inactive
        (fun i => crtPolynomialInputLaw p e (fun _ => 0) hcoprime (origin i)) gridPoint
        (fun i => integerLongPolynomialOutput poly (inactiveCoord i) (∏ l, p l ^ e l))
        (∏ l, p l ^ e l) gridVolume z b / gridVolume : ℝ) : ℂ) *
          test z (fun j => ZMod.castHom hdiv (ZMod q) (b j))) =
      inactive.complexMean (fun i => 𝔼 t : A → ZMod q,
        test (gridPoint i) (fun j => MvPolynomial.eval₂ (Int.castRingHom (ZMod q))
          (Sum.elim t (fun a => (inactiveCoord i a : ZMod q))) (poly j))) := by
  rw [rationalInactiveForecast_divisor_tsum_test _ _ _ _ hdiv hV]
  congr 1
  funext i
  simp_rw [integerLongPolynomialOutput_reduce poly (inactiveCoord i) hdiv]
  exact (crtPolynomialInputLaw_unrestricted_divisor_complexMean p e hp hinj hcoprime (origin i) hdiv
    (fun t => test (gridPoint i) (fun j => MvPolynomial.eval₂ (Int.castRingHom (ZMod q))
      (Sum.elim t (fun a => (inactiveCoord i a : ZMod q))) (poly j)))).trans
        (FiniteProbabilityWeights.uniform_complexMean _)

theorem rationalInactivePolynomialForecast_unrestrictedCRT_tsum_marginal
    {Ω Z : Type*} [Fintype Ω]
    (inactive : FiniteProbabilityWeights Ω) (gridPoint : Ω → Z)
    (p e : L → ℕ) [∀ l, NeZero (p l)]
    (hp : ∀ l, (p l).Prime) (hinj : Function.Injective p)
    (hcoprime : Pairwise (fun l k => (p l ^ e l).Coprime (p k ^ e k)))
    (origin : ∀ l, A → ZMod (p l ^ e l))
    (poly : J → MvPolynomial (A ⊕ I) ℤ) (inactiveCoord : Ω → I → ℤ)
    {q : ℕ} [NeZero q] (hdiv : q ∣ ∏ l, p l ^ e l)
    {gridVolume : ℝ} (hV : gridVolume ≠ 0) (test : Z → (J → ZMod q) → ℂ) :
    (∑' z, 𝔼 b : J → ZMod (∏ l, p l ^ e l),
      ((rationalInactiveForecast inactive
        (fun _ => crtPolynomialInputLaw p e (fun _ => 0) hcoprime origin) gridPoint
        (fun i => integerLongPolynomialOutput poly (inactiveCoord i) (∏ l, p l ^ e l))
        (∏ l, p l ^ e l) gridVolume z b / gridVolume : ℝ) : ℂ) *
          test z (fun j => ZMod.castHom hdiv (ZMod q) (b j))) =
      inactive.complexMean (fun i => 𝔼 t : A → ZMod q,
        test (gridPoint i) (fun j => MvPolynomial.eval₂ (Int.castRingHom (ZMod q))
          (Sum.elim t (fun a => (inactiveCoord i a : ZMod q))) (poly j))) :=
  rationalInactivePolynomialForecast_conditionalUnrestrictedCRT_tsum_marginal
    inactive gridPoint p e hp hinj hcoprime (fun _ => origin) poly inactiveCoord hdiv hV test

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "degree" => layerSamplerDegree I n
local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "hSides" => allocatedPrincipalSides_pos B U basis S
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "activeB" => (fun a : Active => B (Subtype.val a))
local notation "activeDegree" => (fun a : Active => degree (Subtype.val a))
local notation "ActiveInput" => PrincipalTupleIndex activeB activeDegree
local notation "activeLength" => principalAxisLength (fun a => ¬short a) sides
local notation "activePos" => (fun j : ActiveInput => hSides (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j)))
local notation "Original" => PrincipalIntegerTuples B degree Empty sides

variable (q : ℕ)
variable (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := Empty) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

noncomputable def allocatedShortPrincipalResidueLaw :=
  principalSupportedAxisWeights B degree sides hSides q r hcell short

noncomputable def allocatedActivePrincipalResidueLaw :=
  principalSupportedAxisWeights B degree sides hSides q r hcell (fun a => ¬short a)

theorem allocatedPrincipalResidue_partition (f : Original → ℂ) :
    ((principalTupleWeights (α := Empty) B degree sides hSides).condition
      (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell).complexMean f =
      (allocatedShortPrincipalResidueLaw B U basis S q r hcell).complexMean (fun u =>
        (allocatedActivePrincipalResidueLaw B U basis S q r hcell).complexMean
          (fun v => f (principalAxisJoin short u v))) :=
  principalSupportedResidueWeights_partition B degree sides hSides q r hcell short f

theorem allocatedActivePrincipalResidue_length (j : ActiveInput) : activeLength j = S.value :=
  allocatedPrincipalSides_long_of_not_short B U basis S j.1.val j.1.property j.2.1 j.2.2

theorem allocatedActivePrincipalResidueLaw_eq (hq : 0 < q) (hsize : q ≤ S.value) :
    allocatedActivePrincipalResidueLaw B U basis S q r hcell =
      principalResidueWeights activeB activeDegree activeLength activePos q hq
        (fun j => r ⟨j.1.val, j.2⟩)
        (fun j => by simpa only [Fintype.card_empty, zero_add, one_mul,
          allocatedActivePrincipalResidue_length B U basis S] using hsize) := by
  exact principalSupportedAxisWeights_eq_residueWeights B degree sides hSides q r hcell
    (fun a => ¬short a) hq _

theorem allocatedPrincipalResidue_partition_mul
    (φ : PrincipalAxisTuples (α := Empty) short sides → ℂ)
    (ψ : PrincipalAxisTuples (α := Empty) (fun a => ¬short a) sides → ℂ) :
    ((principalTupleWeights (α := Empty) B degree sides hSides).condition
      (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell).complexMean
        (fun y => φ (principalAxisRestrict short y) *
          ψ (principalAxisRestrict (fun a => ¬short a) y)) =
      (allocatedShortPrincipalResidueLaw B U basis S q r hcell).complexMean φ *
        (allocatedActivePrincipalResidueLaw B U basis S q r hcell).complexMean ψ :=
  principalSupportedResidueWeights_partition_mul B degree sides hSides q r hcell short φ ψ

private theorem scalarResidueIntegerMean_congr
    (L₁ L₂ q : ℕ) (hL₁ : 0 < L₁) (hL₂ : 0 < L₂) (hq : 0 < q)
    (r : Option Empty → ZMod q) (hsize₁ : (Fintype.card Empty + 1) * q ≤ L₁)
    (hsize₂ : (Fintype.card Empty + 1) * q ≤ L₂) (he : L₁ = L₂) (f : ℤ → ℂ) :
    (scalarCubeResidueWeights Empty L₁ q hL₁ (fun _ => q) r
      (fun _ => hq) (fun _ => le_rfl) hsize₁).complexMean (fun z => f (z none : ℤ)) =
      (scalarCubeResidueWeights Empty L₂ q hL₂ (fun _ => q) r
        (fun _ => hq) (fun _ => le_rfl) hsize₂).complexMean (fun z => f (z none : ℤ)) := by
  subst L₂
  rfl

theorem allocatedActivePrincipalResidueLaw_integer_mean (hq : 0 < q) (hsize : q ≤ S.value)
    (f : (ActiveInput → ℤ) → ℂ) :
    (allocatedActivePrincipalResidueLaw B U basis S q r hcell).complexMean
        (fun y => f (fun j => (y j none : ℤ))) =
      (principalResidueWeights activeB activeDegree (fun _ => S.value) (fun _ => S.positive)
        q hq (fun j => r ⟨j.1.val, j.2⟩)
        (fun _ => by simpa only [Fintype.card_empty, zero_add, one_mul] using hsize)).complexMean
          (fun y => f (fun j => (y j none : ℤ))) := by
  rw [allocatedActivePrincipalResidueLaw_eq B U basis S q r hcell hq hsize]
  exact FiniteProbabilityWeights.complexMean_pi_transport_fintype
    (fun j => scalarCubeResidueWeights Empty (activeLength j) q (activePos j)
      (fun _ => q) (r ⟨j.1.val, j.2⟩) (fun _ => hq) (fun _ => le_rfl)
      (by simpa only [Fintype.card_empty, zero_add, one_mul,
        allocatedActivePrincipalResidue_length B U basis S] using hsize))
    (fun j => scalarCubeResidueWeights Empty S.value q S.positive
      (fun _ => q) (r ⟨j.1.val, j.2⟩) (fun _ => hq) (fun _ => le_rfl)
      (by simpa only [Fintype.card_empty, zero_add, one_mul] using hsize))
    (fun _ z => (z none : ℤ)) (fun _ z => (z none : ℤ))
    (fun j g => scalarResidueIntegerMean_congr (activeLength j) S.value q (activePos j)
      S.positive hq (r ⟨j.1.val, j.2⟩) _ _
      (allocatedActivePrincipalResidue_length B U basis S j) g) f

theorem allocatedPrincipalResidue_integer_partition (hq : 0 < q) (hsize : q ≤ S.value)
    (f : PrincipalAxisTuples (α := Empty) short sides → (ActiveInput → ℤ) → ℂ) :
    ((principalTupleWeights (α := Empty) B degree sides hSides).condition
      (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell).complexMean
        (fun y => f (principalAxisRestrict short y)
          (fun j => ((principalAxisRestrict (fun a => ¬short a) y) j none : ℤ))) =
      (allocatedShortPrincipalResidueLaw B U basis S q r hcell).complexMean (fun u =>
        (principalResidueWeights activeB activeDegree (fun _ => S.value) (fun _ => S.positive)
          q hq (fun j => r ⟨j.1.val, j.2⟩)
          (fun _ => by simpa only [Fintype.card_empty, zero_add, one_mul] using hsize)).complexMean
            (fun v => f u (fun j => (v j none : ℤ)))) := by
  rw [allocatedPrincipalResidue_partition B U basis S q r hcell]
  simp only [principalAxisRestrict_join_left, principalAxisRestrict_join_right]
  congr 1
  funext u
  exact allocatedActivePrincipalResidueLaw_integer_mean B U basis S q r hcell hq hsize (f u)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical
variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "AB" => (fun a : Active => B (Subtype.val a))
local notation "Ah" => (fun a : Active => layerSamplerDegree I n (Subtype.val a))
local notation "AI" => PrincipalTupleIndex AB Ah
local notation "L" => principalAxisLength (fun a => ¬short a) (allocatedPrincipalSides B U basis S)
local notation "hL" => (fun j : AI => allocatedPrincipalSides_pos B U basis S (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j)))

theorem allocatedActive_affine_residue_comparison
    {Y : Type*} (q : ℕ) [NeZero q] (origin stride : AI → ℤ)
    (F : (AI → ZMod q) → Y) (f : Y → ℂ) (hf : ∀ y, ‖f y‖ ≤ 1) :
    ‖(principalTupleWeights (α := Empty) AB Ah L hL).complexMean
        (fun x => f (F (fun i => ((origin i + stride i * (x i none : ℤ) : ℤ) : ZMod q)))) -
      (FiniteProbabilityWeights.uniform (AI → ZMod q)).complexMean
        (fun r => f (F (fun i => (origin i : ZMod q) + (stride i : ZMod q) * r i)))‖ ≤
      4 * Fintype.card AI * ((q : ℝ) / S.value) := by
  classical
  have he := originalActiveCube_affine_residue_complexMean_error L hL q origin stride F f hf
  have hs : (∑ i : AI, (q : ℝ) / L i) = Fintype.card AI * ((q : ℝ) / S.value) := by
    simp only [allocatedActivePrincipalResidue_length B U basis S, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
  rw [hs] at he
  exact he.trans_eq (by ring)

end Erdos3.VectorPolynomial

end

end OAI
