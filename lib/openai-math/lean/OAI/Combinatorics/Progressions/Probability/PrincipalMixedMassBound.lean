/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Geometry.PrincipalSpatialMixedComparison
import OAI.Combinatorics.Progressions.Lattices.SpatialResidueMass

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem pmf_sum_toReal_le_one {X : Type*} (p : PMF X) (s : Finset X) :
    (∑ x ∈ s, (p x).toReal) ≤ 1 := by
  have h : (∑ x ∈ s, p x) ≤ 1 := (ENNReal.sum_le_tsum s).trans_eq p.tsum_coe
  have hr := ENNReal.toReal_mono ENNReal.one_ne_top h
  simpa only [ENNReal.toReal_sum (fun x _ => p.apply_ne_top x), ENNReal.toReal_one] using hr

theorem scaledPMF_expect_le {X : Type*} (p : PMF X) (s : Finset X)
    {S : ℝ} (hS : 0 ≤ S) : (𝔼 x ∈ s, S*(p x).toReal) ≤ S/s.card := by
  rw [Finset.expect_eq_sum_div_card, ← Finset.mul_sum]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (pmf_sum_toReal_le_one p s) hS

theorem scaledPMF_expect_le_one {X : Type*} (p : PMF X) (s : Finset X)
    {S : ℝ} (hS : 0 ≤ S) (hcard : S ≤ s.card) : (𝔼 x ∈ s, S*(p x).toReal) ≤ 1 := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  · exact (scaledPMF_expect_le p s hS).trans ((div_le_one (by exact_mod_cast hs.card_pos)).mpr hcard)

theorem scaledPMF_product_expect_le_one {X Y : Type*} (p : PMF Y) (s : Finset X) (t : Finset Y)
    {S : ℝ} (hS : 0 ≤ S) (hcard : S ≤ t.card) :
    (𝔼 v ∈ s ×ˢ t, S*(p v.2).toReal) ≤ 1 := by
  rw [Finset.expect_product]
  exact finite_expect_le_of_nonneg_bound s _ zero_le_one (fun _ _ => scaledPMF_expect_le_one p t hS hcard)

theorem scaledPMF_product_mean_le_one {Ω X Y : Type*} [Fintype Ω]
    (q : FiniteProbabilityWeights Ω) (p : Ω → PMF Y) (s : Finset X) (t : Finset Y)
    {S : ℝ} (hS : 0 ≤ S) (hcard : S ≤ t.card) :
    q.mean (fun y => 𝔼 v ∈ s ×ˢ t, S*(p y v.2).toReal) ≤ 1 :=
  finiteMean_le_of_support q _ (fun y _ => scaledPMF_product_expect_le_one (p y) s t hS hcard)

theorem jointCoefficientWindow_card {Q : Type*} [Fintype Q] [DecidableEq Q]
    {I : Q → Type*} [∀ q, Fintype (I q)] [∀ q, DecidableEq (I q)]
    (H : Q → ℝ) (T : ∀ q, I q → ℕ) (hH : ∀ q, 0 ≤ H q)
    (hT : ∀ q i, H q ≤ 2*(T q i : ℝ)+1) :
    (∏ q, H q^Fintype.card (I q)) ≤
      (Fintype.piFinset (fun q => centeredIntegerBox (T q))).card := by
  simp only [Fintype.card_piFinset, card_centeredIntegerBox, Nat.cast_prod, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat, Nat.cast_one]
  apply Finset.prod_le_prod₀ (fun q _ => pow_nonneg (hH q) _)
  intro q _
  calc
    _ = ∏ _i : I q, H q := by simp
    _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => hH q) (fun i _ => hT q i)

theorem jointCoefficientWindow_mass {Q : Type*} [Fintype Q] [DecidableEq Q]
    {I : Q → Type*} [∀ q, Fintype (I q)] [∀ q, DecidableEq (I q)]
    (p : PMF (∀ q, I q → ℤ)) (H : Q → ℝ) (T : ∀ q, I q → ℕ) (hH : ∀ q, 0 ≤ H q)
    (hT : ∀ q i, H q ≤ 2*(T q i : ℝ)+1) :
    (𝔼 v ∈ Fintype.piFinset (fun q => centeredIntegerBox (T q)),
      (∏ q, H q^Fintype.card (I q))*(p v).toReal) ≤ 1 :=
  scaledPMF_expect_le_one p _ (Finset.prod_nonneg (fun q _ => pow_nonneg (hH q) _))
    (jointCoefficientWindow_card H T hH hT)

theorem jointCoefficientWindow_scaled_mass {Q : Type*} [Fintype Q] [DecidableEq Q]
    {I : Q → Type*} [∀ q, Fintype (I q)] [∀ q, DecidableEq (I q)]
    (p : PMF (∀ q, I q → ℤ)) (H R : Q → ℝ) (hH : ∀ q, 0 ≤ H q) (hR : ∀ q, 1 ≤ R q) :
    (𝔼 v ∈ Fintype.piFinset (fun q => centeredIntegerBox (fun _ : I q => ⌈R q*H q⌉₊)),
      (∏ q, H q^Fintype.card (I q))*(p v).toReal) ≤ 1 := by
  apply jointCoefficientWindow_mass p H _ hH
  intro q _
  have hc := Nat.le_ceil (R q*H q)
  have hmul := mul_le_mul_of_nonneg_right (hR q) (hH q)
  nlinarith [Nat.cast_nonneg (α := ℝ) ⌈R q*H q⌉₊]

theorem jointCoefficientWindow_contains {Q : Type*} [Fintype Q] [DecidableEq Q]
    {I : Q → Type*} [∀ q, Fintype (I q)] [∀ q, DecidableEq (I q)]
    (H R : Q → ℝ) (v : ∀ q, I q → ℤ) (hv : ∀ q i, |(v q i : ℝ)| ≤ R q*H q) :
    v ∈ Fintype.piFinset (fun q => centeredIntegerBox (fun _ : I q => ⌈R q*H q⌉₊)) := by
  apply Fintype.mem_piFinset.mpr
  intro q
  apply (mem_centeredIntegerBox _ _).mpr
  intro i
  have hc := (hv q i).trans (Nat.le_ceil (R q*H q))
  exact_mod_cast hc

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem norm_nonneg_finite_test_le_mass {V : Type*} (s : Finset V)
    (c : V → ℝ) (φ : V → ℂ) (hc : ∀ v ∈ s, 0 ≤ c v)
    (hφ : ∀ v ∈ s, ‖φ v‖ ≤ 1) :
    ‖∑ v ∈ s, (c v : ℂ) * φ v‖ ≤ ∑ v ∈ s, c v := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro v hv
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hc v hv)]
  exact (mul_le_mul_of_nonneg_left (hφ v hv) (hc v hv)).trans_eq (mul_one _)

theorem pmf_proxy_norm_mass {V : Type*} (p : PMF V) (s : Finset V)
    (b : V → ℂ) {δ : ℝ}
    (he : ∀ v ∈ s, ‖((p v).toReal : ℂ) - b v‖ ≤ δ) :
    (∑ v ∈ s, ‖b v‖) ≤ 1 + δ * s.card := by
  have hb (v) (hv : v ∈ s) : ‖b v‖ ≤ (p v).toReal + δ := by
    have ht := norm_add_le (b v - ((p v).toReal : ℂ)) ((p v).toReal : ℂ)
    rw [sub_add_cancel, norm_sub_rev, Complex.norm_real,
      Real.norm_of_nonneg ENNReal.toReal_nonneg] at ht
    linarith [he v hv]
  calc
    _ ≤ ∑ v ∈ s, ((p v).toReal + δ) := Finset.sum_le_sum hb
    _ = (∑ v ∈ s, (p v).toReal) + δ * s.card := by
      rw [Finset.sum_add_distrib]
      simp [mul_comm]
    _ ≤ 1 + δ * s.card := add_le_add (pmf_sum_toReal_le_one p s) le_rfl

theorem FiniteProbabilityWeights.complexMean_finset_sum {X V : Type*} [Fintype X]
    (p : FiniteProbabilityWeights X) (s : Finset V) (f : V → X → ℂ) :
    p.complexMean (fun x => ∑ v ∈ s, f v x) = ∑ v ∈ s, p.complexMean (f v) := by
  simp only [FiniteProbabilityWeights.complexMean, Finset.mul_sum]
  exact Finset.sum_comm

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

theorem norm_reference_density_error_normalized {Ω V : Type*} [Fintype Ω] [Fintype V]
    (p : FiniteProbabilityWeights Ω) (source : Ω → ℂ) (factor : V → ℂ)
    (g : Ω → V → ℝ) (proxy error : V → ℝ) {δ Z : ℝ} (hZ : 0 < Z)
    (hfirst : ∀ w, p.weight w ≠ 0 →
      ‖source w / (Z : ℂ) - (∑ v, factor v * (g w v : ℂ)) / (Z : ℂ)‖ ≤ δ)
    (hcoeff : ∀ v, |p.mean (fun w => g w v) - proxy v| ≤ error v) :
    ‖p.complexMean source / (Z : ℂ) - (∑ v, factor v * (proxy v : ℂ)) / (Z : ℂ)‖ ≤
      δ + (∑ v, ‖factor v‖ * error v) / Z := by
  have hdiv (f : Ω → ℂ) : p.complexMean (fun w => f w / (Z : ℂ)) =
      p.complexMean f / (Z : ℂ) := by
    simp only [complexMean, mul_div_assoc, Finset.sum_div]
  have h₁ := p.norm_complexMean_sub_le (fun w => source w / (Z : ℂ))
    (fun w => (∑ v, factor v * (g w v : ℂ)) / (Z : ℂ)) (fun _ => δ) hfirst
  rw [hdiv, hdiv, p.mean_const] at h₁
  have heq : p.complexMean (fun w => ∑ v, factor v * (g w v : ℂ)) =
      ∑ v, factor v * (p.mean (fun w => g w v) : ℂ) := by
    rw [p.complexMean_finset_sum]
    simp_rw [p.complexMean_mul_left, p.complexMean_ofReal]
  have h₂ : ‖p.complexMean (fun w => ∑ v, factor v * (g w v : ℂ)) / (Z : ℂ) -
      (∑ v, factor v * (proxy v : ℂ)) / (Z : ℂ)‖ ≤
      (∑ v, ‖factor v‖ * error v) / Z := by
    rw [heq, ← sub_div, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hZ]
    apply div_le_div_of_nonneg_right _ hZ.le
    rw [← Finset.sum_sub_distrib]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro v _
    rw [← mul_sub, ← Complex.ofReal_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hcoeff v) (norm_nonneg _)
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add h₁ h₂)

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

theorem norm_reference_density_variable_error_normalized {Ω V : Type*} [Fintype Ω] [Fintype V]
    (p : FiniteProbabilityWeights Ω) (source : Ω → ℂ) (factor : V → ℂ)
    (g : Ω → V → ℝ) (proxy error : V → ℝ) (δ : Ω → ℝ) {Z : ℝ} (hZ : 0 < Z)
    (hfirst : ∀ w, p.weight w ≠ 0 →
      ‖source w / (Z : ℂ) - (∑ v, factor v * (g w v : ℂ)) / (Z : ℂ)‖ ≤ δ w)
    (hcoeff : ∀ v, |p.mean (fun w => g w v) - proxy v| ≤ error v) :
    ‖p.complexMean source / (Z : ℂ) - (∑ v, factor v * (proxy v : ℂ)) / (Z : ℂ)‖ ≤
      p.mean δ + (∑ v, ‖factor v‖ * error v) / Z := by
  have hdiv (f : Ω → ℂ) : p.complexMean (fun w => f w / (Z : ℂ)) =
      p.complexMean f / (Z : ℂ) := by
    simp only [complexMean, mul_div_assoc, Finset.sum_div]
  have h₁ := p.norm_complexMean_sub_le (fun w => source w / (Z : ℂ))
    (fun w => (∑ v, factor v * (g w v : ℂ)) / (Z : ℂ)) δ hfirst
  rw [hdiv, hdiv] at h₁
  have h₂ := p.norm_reference_density_error_normalized
    (fun w => ∑ v, factor v * (g w v : ℂ)) factor g proxy error (δ := 0) hZ
    (by intro w _; simp only [sub_self, norm_zero, le_refl]) hcoeff
  simp only [zero_add] at h₂
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add h₁ h₂)

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators

theorem principalSpatial_mixed_mass_bound {D A α J N V W : Type*}
    [Fintype D] [DecidableEq D] [Fintype A] [Fintype α] [DecidableEq α]
    [Fintype J] [DecidableEq J] [Fintype N] [DecidableEq N]
    (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
    (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j)
    {ℓ M : ℕ} {ρ ξ r ε S : ℝ} (s : α ↪ J)
    (x : J → IntegerScalarCubeBox α ℓ) (root : J → ℤ)
    (hM : 0 < M) (hℓ : 0 < ℓ) (hx : GoodScalarKernelTuple s (1/(M : ℝ)) M x)
    (hroot : ∀ j, |root j| ≤ (ℓ : ℤ)) (m : ℕ) [NeZero m] (hm : 0 < m)
    (hsize : ∀ j, (Fintype.card α+1)*m ≤ L j)
    (hp : integerScalarLattice (Unit ⊕ α) (m : ℤ) ≤
      pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) s)
        (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) s))
    (c : A → N → ℤ) (index : A → N → PrincipalTupleIndex B h)
    (H : A → ℝ) (Q : A → N → ℝ) (hH : ∀ a, 0 < H a) (hQ : ∀ a n, 0 < Q a n)
    (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (hwidth : ∀ a n, ((|c a n| : ℤ)+(L (index a n) : ℤ) : ℝ)*Q a n ≤ ξ*H a)
    (hρ : 0 < ρ) (hscale : ∀ a, ρ ≤ H a/ℓ) (hscaleQ : ∀ a n, ρ ≤ Q a n)
    (hlarge : smoothSpatialMeshThreshold α J N ℓ ≤ ρ) (hr : 0 < r) (hε : 0 ≤ ε)
    (tv : Finset V) (tw : Finset W) (out : V → A → (Unit ⊕ α) → ℤ)
    (coefficient : PrincipalIntegerTuples B h α L → PMF W) (hS : 0 ≤ S) (hcard : S ≤ tw.card)
    (target : (PrincipalTupleIndex B h → Option α → ZMod m) → W → ℝ) (φ : V × W → ℂ)
    (hφ : ∀ v ∈ tv ×ˢ tw, ‖φ v‖ ≤ 1)
    (hbox : ∀ v ∈ tv, ∀ a i, |((spatialStar (out v a) i : ℤ) : ℝ)/H a| ≤ 1)
    (hcoeff : ∀ rr w, w ∈ tw →
      |(principalResidueWeights B h L hL m hm rr hsize).mean
        (fun y => S*(coefficient y w).toReal)-target rr w| ≤ ε) :
    let P := selectedSpatialPivot root (scalarCubeDifferenceMatrix x) s
    let F := selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) s
    let hP := goodScalarKernelTuple_spatial_det_ne_zero s x root
      (one_div_pos.mpr (by exact_mod_cast hM)) hx
    let f := fun a => smoothSpatialKernelDensity s root (scalarCubeDifferenceMatrix x) hP
      (H a) ℓ (hH a) (by exact_mod_cast hℓ)
    let G := (m : ℝ)^Fintype.card (Unit ⊕ α)
    let E := smoothSpatialError N s M ℓ ρ ξ
    let source := principalTupleWeights (α := α) B h L hL
    let residues := source.fiberLaw (principalResidueLabel m)
    let site := fun rr v => ∏ a, spatialSiteApprox P
      (Matrix.fromCols F (liftResidueMatrix (principalSpatialResidueColumns m (c a) (index a) rr)))
      m (f a) (H a) 1 r (out v a)
    ‖source.complexMean (fun y => 𝔼 v ∈ tv ×ˢ tw, ((S*(coefficient y v.2).toReal : ℝ) : ℂ)*
        (((∏ a, ∏ _i : Unit ⊕ α, H a)*
          (smoothVectorSpatialOutputLaw root (scalarCubeDifferenceMatrix x)
            (fun a => principalSpatialColumns (c a) (index a) y) H ℓ Q hH
            (by exact_mod_cast hℓ) hQ (out v.1)).toReal : ℝ) : ℂ)*φ v) -
      (∑ rr, 𝔼 v ∈ tv ×ˢ tw, ((residues.weight rr*target rr v.2 : ℝ) : ℂ)*site rr v.1*φ v)‖ ≤
      Fintype.card A*(E+4*G*smoothSpatialDensityLip s M*r)*(1+G*smoothSpatialDensityCap s M+E)^Fintype.card A +
        ε*(G*smoothSpatialDensityCap s M)^Fintype.card A := by
  dsimp only
  have hbox' (v : V × W) (hv : v ∈ tv ×ˢ tw) := hbox v.1 (Finset.mem_product.mp hv).1
  have he := principalSpatial_mixed_comparison B h L hL s x root hM hℓ hx hroot m hm hsize hp
    c index H Q hH hQ hξ0 hξ1 hwidth hρ hscale hscaleQ hlarge hr (tv ×ˢ tw) (fun v => out v.1)
    (fun y v => S*(coefficient y v.2).toReal) (fun rr v => target rr v.2) φ
    (fun _ _ _ _ => mul_nonneg hS ENNReal.toReal_nonneg) hφ hbox'
    (fun rr v hv => hcoeff rr v.2 (Finset.mem_product.mp hv).2)
  have hmass := scaledPMF_product_mean_le_one (principalTupleWeights (α := α) B h L hL)
    coefficient tv tw hS hcard
  have hsite := smoothSpatialSite_mean_norm_le s x root hM hℓ hx hroot m hp H hH zero_lt_one hr
    ((principalTupleWeights (α := α) B h L hL).fiberLaw (principalResidueLabel m)) (tv ×ˢ tw)
    (fun v => out v.1) (fun rr a => principalSpatialResidueColumns m (c a) (index a) rr) hbox'
  have hE := smoothSpatialError_nonneg N s M ℓ hρ.le hξ0
  have hC := smoothSpatialDensityCap_nonneg s M
  have hK := smoothSpatialDensityLip_nonneg s M
  apply he.trans
  calc
    _ ≤ _*1+ε*((m : ℝ)^Fintype.card (Unit ⊕ α)*smoothSpatialDensityCap s M)^Fintype.card A :=
      add_le_add (mul_le_mul_of_nonneg_left hmass (by positivity)) (mul_le_mul_of_nonneg_left hsite hε)
    _ = _ := by rw [mul_one]

end Erdos3

end

end OAI
