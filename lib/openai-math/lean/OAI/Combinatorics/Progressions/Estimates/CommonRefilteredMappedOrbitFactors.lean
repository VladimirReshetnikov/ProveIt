/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Linear.AnchoredKernelInvariance
import OAI.Combinatorics.Progressions.Polynomial.ControlledPolynomialGroupMapBounds

namespace OAI

section

namespace Erdos3

open Module

theorem exists_weighted_common_positive_nat {Ω : Type*} [Fintype Ω]
    (outer : FiniteProbabilityWeights Ω) (S : Finset Ω) (hS : 0 < outer.mass S)
    (n : Ω → ℕ) {p : ℝ} (hn : ∀ a ∈ S, 0 < n a ∧ (n a : ℝ) ≤ Real.exp p) :
    ∃ a₀ ∈ S, ∃ T : Finset Ω, T ⊆ S ∧ a₀ ∈ T ∧ (∀ a ∈ T, n a = n a₀) ∧
      Real.exp (-p) * outer.mass S ≤ outer.mass T := by
  let A := Finset.Icc 1 ⌊Real.exp p⌋₊
  have hA : ((A : Set ℕ).ncard : ℝ) ≤ Real.exp p := by
    simpa only [A, Set.ncard_coe_finset, Nat.card_Icc, Nat.add_sub_cancel] using
      (Nat.floor_le (Real.exp_nonneg p))
  obtain ⟨k, _, T, hTS, hT, hk, hlarge⟩ := exists_weighted_exponential_constant_fiber
    outer S hS n (A : Set ℕ) A.finite_toSet
    (fun a ha => Finset.mem_Icc.mpr ⟨(hn a ha).1, Nat.le_floor (hn a ha).2⟩) hA
  obtain ⟨a₀, ha₀⟩ := hT
  exact ⟨a₀, hTS ha₀, T, hTS, ha₀,
    fun a ha => (hk a ha).trans (hk a₀ ha₀).symm, hlarge⟩

theorem exists_weighted_common_fast_subalgebra
    {Ω ι L : Type*} [Fintype Ω] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
    (e : Basis ι ℚ L) (outer : FiniteProbabilityWeights Ω)
    (S : Finset Ω) (hS : 0 < outer.mass S)
    (K : Ω → LieSubalgebra ℚ L) (m : ℕ) {p : ℝ}
    (hp : 0 ≤ p) (hm : (m : ℝ) ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p)
    (hK : ∀ a ∈ S, ∃ v : Fin m → L,
      Submodule.span ℚ (Set.range v) = (K a).toSubmodule ∧
        ∀ i j, rationalLogHeight (e.repr (v i) j) ≤ p) :
    ∃ a₀ ∈ S, ∃ T : Finset Ω, T ⊆ S ∧ a₀ ∈ T ∧ (∀ a ∈ T, K a = K a₀) ∧
      Real.exp (-((p + 2) ^ 5)) * outer.mass S ≤ outer.mass T := by
  have hmem : ∀ a ∈ S, K a ∈ heightBoundedLieSubalgebras e m ⌈Real.exp p⌉₊ := by
    intro a ha
    obtain ⟨v, hv, hh⟩ := hK a ha
    exact (mem_heightBoundedSubspaces e m ⌈Real.exp p⌉₊ (K a).toSubmodule).mpr
      ⟨v, hv, fun i j => rationalHeightLE_ceil_exp (hh i j)⟩
  have hcount : ((heightBoundedLieSubalgebras e m ⌈Real.exp p⌉₊).ncard : ℝ) ≤
      Real.exp ((p + 2) ^ 5) :=
    (heightBoundedLieSubalgebras_ncard_exp_bound e m hp).trans
      (Real.exp_le_exp.mpr (common_subalgebra_cost_le_budget m (Fintype.card ι)
        hp hm hd hp le_rfl))
  obtain ⟨U, _, T, hTS, hT, hU, hlarge⟩ := exists_weighted_exponential_constant_fiber
    outer S hS K (heightBoundedLieSubalgebras e m ⌈Real.exp p⌉₊)
    (finite_card_heightBoundedLieSubalgebras e m ⌈Real.exp p⌉₊).1 hmem hcount
  obtain ⟨a₀, ha₀⟩ := hT
  exact ⟨a₀, hTS ha₀, T, hTS, ha₀,
    fun a ha => (hU a ha).trans (hU a₀ ha₀).symm, hlarge⟩

theorem exists_weighted_common_fast_subalgebra_and_denominator
    {Ω ι L : Type*} [Fintype Ω] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
    (e : Basis ι ℚ L) (outer : FiniteProbabilityWeights Ω)
    (S : Finset Ω) (hS : 0 < outer.mass S)
    (K : Ω → LieSubalgebra ℚ L) (n : Ω → ℕ) (m : ℕ) {p : ℝ}
    (hp : 0 ≤ p) (hm : (m : ℝ) ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p)
    (hK : ∀ a ∈ S, ∃ v : Fin m → L,
      Submodule.span ℚ (Set.range v) = (K a).toSubmodule ∧
        ∀ i j, rationalLogHeight (e.repr (v i) j) ≤ p)
    (hn : ∀ a ∈ S, 0 < n a ∧ (n a : ℝ) ≤ Real.exp p) :
    ∃ a₀ ∈ S, ∃ T : Finset Ω, T ⊆ S ∧ a₀ ∈ T ∧
      (∀ a ∈ T, K a = K a₀ ∧ n a = n a₀) ∧
      Real.exp (-((p + 2) ^ 5 + p)) * outer.mass S ≤ outer.mass T := by
  obtain ⟨b, _, U, hUS, hbU, hKsame, hUlarge⟩ :=
    exists_weighted_common_fast_subalgebra e outer S hS K m hp hm hd hK
  have hUpos : 0 < outer.mass U := (mul_pos (Real.exp_pos _) hS).trans_le hUlarge
  obtain ⟨a₀, haU, T, hTU, haT, hnsame, hTlarge⟩ :=
    exists_weighted_common_positive_nat outer U hUpos n (fun a ha => hn a (hUS ha))
  refine ⟨a₀, hUS haU, T, hTU.trans hUS, haT, ?_, ?_⟩
  · intro a ha
    exact ⟨(hKsame a (hTU ha)).trans (hKsame a₀ haU).symm, hnsame a ha⟩
  · calc
      Real.exp (-((p + 2) ^ 5 + p)) * outer.mass S =
          Real.exp (-p) * (Real.exp (-((p + 2) ^ 5)) * outer.mass S) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-p) * outer.mass U :=
        mul_le_mul_of_nonneg_left hUlarge (Real.exp_pos _).le
      _ ≤ outer.mass T := hTlarge

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration VectorPolynomial
open scoped TensorProduct

variable {ι J σ : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)) (a : ι)

def HasFixedProductOrbitFactors
    (g : ∀ i, (D i).filtration.realification.PolynomialOrbit (fun _ : σ => 1))
    (eta : J → L a →ₗ[ℚ] ℚ) (side : σ → ℝ) (p : ℝ) (m : ℕ)
    (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded) : Prop :=
  ∃ freq : J → ∀ i, L i →ₗ[ℚ] ℚ,
    (∀ j, freq j a = eta j) ∧
    (∀ j x, x ∈ (pi D).filtration.realGradedRefiltrationLayer W s →
      realifyFunctional (piFrequency (freq j)) x = 0) ∧
    ∃ (κ : (pi D).RealGroup)
      (slow middle rat : ((pi D).filtration.realification.adaptedPolynomialFiltration
        (fun _ : σ => 1)).Group),
      κ ∈ (pi D).realLattice ∧
      slow * middle * rat * (pi D).filtration.realification.adaptedConstantGroupHom
        (fun _ : σ => 1) κ =
          ⟨⟨(piRealOrbit (fun i => (D i).filtration) g).log,
            (piRealOrbit (fun i => (D i).filtration) g).property⟩⟩ ∧
      (pi D).filtration.PolynomialSlowBound (pi D).basis (fun _ : σ => 1)
        side (Real.exp p) slow ∧
      (pi D).filtration.PolynomialRationalGrid (pi D).basis (fun _ : σ => 1) m rat ∧
      coefficients (middle.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (∀ i, L i))) 0 = 0 ∧
      coefficients (rat.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (∀ i, L i))) 0 = 0 ∧
      (∀ α, coefficients (middle.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (∀ i, L i))) α ∈
        (pi D).filtration.realGradedRefiltrationLayer W (Finsupp.weight (fun _ => 1) α)) ∧
      (∀ t : σ → ℝ, eval₂ t (middle.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (∀ i, L i))) ∈
        realificationLieSubalgebra ((pi D).filtration.gradedRefiltrationSubalgebra W))

theorem HasFixedProductOrbitFactors.mono
    {g : ∀ i, (D i).filtration.realification.PolynomialOrbit (fun _ : σ => 1)}
    {eta : J → L a →ₗ[ℚ] ℚ} {side : σ → ℝ} {p q : ℝ} {m : ℕ}
    {W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded}
    (h : HasFixedProductOrbitFactors D a g eta side p m W)
    (hpq : p ≤ q) (hside : ∀ i, 0 < side i) :
    HasFixedProductOrbitFactors D a g eta side q m W := by
  obtain ⟨freq, hf, hv, κ, slow, middle, rat, hκ, heq, hs, hr, hm0, hr0, hc, ht⟩ := h
  exact ⟨freq, hf, hv, κ, slow, middle, rat, hκ, heq,
    (pi D).filtration.polynomialSlowBound_mono (pi D).basis (fun _ => 1) side hside
      (Real.exp_le_exp.mpr hpq) slow hs, hr, hm0, hr0, hc, ht⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration
open scoped TensorProduct

variable {G ι J σ : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)) (a : ι)

theorem exists_common_product_orbit_factors
    (weight : ∀ i, Fin (d i) → ℕ)
    (hFlayers : ∀ i j, (D i).filtration.layer j =
      Submodule.span ℚ ((D i).basis '' {k | j ≤ weight i k}))
    (H : Finset G) (hH : H.Nonempty)
    (g : G → ∀ i, (D i).filtration.realification.PolynomialOrbit (fun _ : σ => 1))
    (eta : G → J → L a →ₗ[ℚ] ℚ) (side : σ → ℝ) {p : ℝ} (hp : 0 ≤ p)
    (hd : (Fintype.card (Σ i, Fin (d i)) : ℝ) ≤ p)
    (hdata : ∀ h ∈ H,
      ∃ (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded)
        (v : Fin (Fintype.card (Σ i, Fin (d i))) → (pi D).filtration.AssociatedGraded) (m : ℕ),
        Submodule.span ℚ (Set.range v) = W.toSubmodule ∧
        BasisGradedSubmodule ((pi D).filtration.associatedGradedBasis (pi D).basis
          (productBasisWeight weight) (pi_layer_span D weight hFlayers))
          (productBasisWeight weight) W.toSubmodule ∧
        (∀ i j, rationalLogHeight
          (((pi D).filtration.associatedGradedBasis (pi D).basis
            (productBasisWeight weight) (pi_layer_span D weight hFlayers)).repr (v i) j) ≤ p) ∧
        0 < m ∧ (m : ℝ) ≤ Real.exp p ∧
        HasFixedProductOrbitFactors D a (g h) (eta h) side p m W) :
    ∃ (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded)
      (v : Fin (Fintype.card (Σ i, Fin (d i))) → (pi D).filtration.AssociatedGraded)
      (m : ℕ) (H' : Finset G),
      H' ⊆ H ∧ H'.Nonempty ∧
      Real.exp (-((p + 2) ^ 5 + p)) * H.card ≤ (H'.card : ℝ) ∧
      Submodule.span ℚ (Set.range v) = W.toSubmodule ∧
      BasisGradedSubmodule ((pi D).filtration.associatedGradedBasis (pi D).basis
        (productBasisWeight weight) (pi_layer_span D weight hFlayers))
        (productBasisWeight weight) W.toSubmodule ∧
      (∀ i j, rationalLogHeight
        (((pi D).filtration.associatedGradedBasis (pi D).basis
          (productBasisWeight weight) (pi_layer_span D weight hFlayers)).repr (v i) j) ≤ p) ∧
      0 < m ∧ (m : ℝ) ≤ Real.exp p ∧
      ∀ h ∈ H', HasFixedProductOrbitFactors D a (g h) (eta h) side p m W := by
  classical
  obtain ⟨h₀, hh₀⟩ := hH
  let pick (h : G) := if h ∈ H then h else h₀
  have hpick (h) : pick h ∈ H := by
    dsimp only [pick]
    split_ifs with hh
    · exact hh
    · exact hh₀
  choose W v m hv hW hheight hm hmp hfactor using fun h => hdata (pick h) (hpick h)
  let e := (pi D).filtration.associatedGradedBasis (pi D).basis
    (productBasisWeight weight) (pi_layer_span D weight hFlayers)
  obtain ⟨h₁, _, H', hsub, hh₁, hsame, hlarge⟩ :=
    exists_common_fast_subalgebra_and_denominator e H ⟨h₀, hh₀⟩ W m
      (Fintype.card (Σ i, Fin (d i))) hp hd (by simpa only [Fintype.card_fin] using hd)
      (fun h _ => ⟨v h, hv h, hheight h⟩) (fun h _ => ⟨hm h, hmp h⟩)
  refine ⟨W h₁, v h₁, m h₁, H', hsub, ⟨h₁, hh₁⟩, hlarge,
    hv h₁, hW h₁, hheight h₁, hm h₁, hmp h₁, ?_⟩
  intro h hh
  have hpickh : pick h = h := ite_eq_left (hsub hh)
  simpa only [hpickh, (hsame h hh).1, (hsame h hh).2] using hfactor h

theorem exists_common_product_frequency_family
    (H : Finset G)
    (g : G → ∀ i, (D i).filtration.realification.PolynomialOrbit (fun _ : σ => 1))
    (eta : G → J → L a →ₗ[ℚ] ℚ) (side : σ → ℝ) (p : ℝ) (m : ℕ)
    (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded)
    (hdata : ∀ h ∈ H, HasFixedProductOrbitFactors D a (g h) (eta h) side p m W)
    (S : G → (D a).Space → ℂ)
    (hinvariant : ∀ h ∈ H, ∀ z, z ∈ (D a).filtration.realification.subgroup s →
      (∀ j, realifyFunctional (eta h j) z.coord = 0) → ∀ x, S h (z • x) = S h x) :
    ∃ freq : ({h // h ∈ H} × J) → ∀ i, L i →ₗ[ℚ] ℚ,
      (∀ j x, x ∈ (pi D).filtration.realGradedRefiltrationLayer W s →
        realifyFunctional (piFrequency (freq j)) x = 0) ∧
      (∀ h ∈ H, ∀ z, z ∈ (D a).filtration.realification.subgroup s →
        (∀ j, realifyFunctional (freq j a) z.coord = 0) → ∀ x, S h (z • x) = S h x) := by
  classical
  let freq₀ := fun h : {h // h ∈ H} => Classical.choose (hdata h.val h.property)
  have hfreq₀ (h : {h // h ∈ H}) := Classical.choose_spec (hdata h.val h.property)
  refine ⟨fun j => freq₀ j.1 j.2, ?_, ?_⟩
  · intro j x hx
    exact (hfreq₀ j.1).2.1 j.2 x hx
  · intro h hh z hz hf x
    apply hinvariant h hh z hz _ x
    intro j
    have hj := hf (⟨h, hh⟩, j)
    change realifyFunctional (freq₀ ⟨h, hh⟩ j a) z.coord = 0 at hj
    have hident : freq₀ ⟨h, hh⟩ j a = eta h j := (hfreq₀ ⟨h, hh⟩).1 j
    rwa [hident] at hj

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration
open scoped TensorProduct

variable {G ι J σ : Type*} [Fintype G] [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)) (a : ι)

theorem exists_weighted_common_product_orbit_factors
    (weight : ∀ i, Fin (d i) → ℕ)
    (hFlayers : ∀ i j, (D i).filtration.layer j =
      Submodule.span ℚ ((D i).basis '' {k | j ≤ weight i k}))
    (outer : FiniteProbabilityWeights G) (H : Finset G) (hH : 0 < outer.mass H)
    (g : G → ∀ i, (D i).filtration.realification.PolynomialOrbit (fun _ : σ => 1))
    (eta : G → J → L a →ₗ[ℚ] ℚ) (side : σ → ℝ) {p : ℝ} (hp : 0 ≤ p)
    (hd : (Fintype.card (Σ i, Fin (d i)) : ℝ) ≤ p)
    (hdata : ∀ h ∈ H,
      ∃ (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded)
        (v : Fin (Fintype.card (Σ i, Fin (d i))) → (pi D).filtration.AssociatedGraded) (m : ℕ),
        Submodule.span ℚ (Set.range v) = W.toSubmodule ∧
        BasisGradedSubmodule ((pi D).filtration.associatedGradedBasis (pi D).basis
          (productBasisWeight weight) (pi_layer_span D weight hFlayers))
          (productBasisWeight weight) W.toSubmodule ∧
        (∀ i j, rationalLogHeight
          (((pi D).filtration.associatedGradedBasis (pi D).basis
            (productBasisWeight weight) (pi_layer_span D weight hFlayers)).repr (v i) j) ≤ p) ∧
        0 < m ∧ (m : ℝ) ≤ Real.exp p ∧
        HasFixedProductOrbitFactors D a (g h) (eta h) side p m W) :
    ∃ (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded)
      (v : Fin (Fintype.card (Σ i, Fin (d i))) → (pi D).filtration.AssociatedGraded)
      (m : ℕ) (H' : Finset G),
      H' ⊆ H ∧ 0 < outer.mass H' ∧
      Real.exp (-((p + 2) ^ 5 + p)) * outer.mass H ≤ outer.mass H' ∧
      Submodule.span ℚ (Set.range v) = W.toSubmodule ∧
      BasisGradedSubmodule ((pi D).filtration.associatedGradedBasis (pi D).basis
        (productBasisWeight weight) (pi_layer_span D weight hFlayers))
        (productBasisWeight weight) W.toSubmodule ∧
      (∀ i j, rationalLogHeight
        (((pi D).filtration.associatedGradedBasis (pi D).basis
          (productBasisWeight weight) (pi_layer_span D weight hFlayers)).repr (v i) j) ≤ p) ∧
      0 < m ∧ (m : ℝ) ≤ Real.exp p ∧
      ∀ h ∈ H', HasFixedProductOrbitFactors D a (g h) (eta h) side p m W := by
  classical
  have hHne : H.Nonempty := by
    by_contra hn
    have he : H = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp only [he, FiniteProbabilityWeights.mass, Finset.sum_empty, lt_self_iff_false] at hH
  obtain ⟨h₀, hh₀⟩ := hHne
  let pick (h : G) := if h ∈ H then h else h₀
  have hpick (h) : pick h ∈ H := by
    dsimp only [pick]
    split_ifs with hh
    · exact hh
    · exact hh₀
  choose W v m hv hW hheight hm hmp hfactor using fun h => hdata (pick h) (hpick h)
  let e := (pi D).filtration.associatedGradedBasis (pi D).basis
    (productBasisWeight weight) (pi_layer_span D weight hFlayers)
  obtain ⟨h₁, _, H', hsub, hh₁, hsame, hlarge⟩ :=
    exists_weighted_common_fast_subalgebra_and_denominator e outer H hH W m
      (Fintype.card (Σ i, Fin (d i))) hp hd (by simpa only [Fintype.card_fin] using hd)
      (fun h _ => ⟨v h, hv h, hheight h⟩) (fun h _ => ⟨hm h, hmp h⟩)
  refine ⟨W h₁, v h₁, m h₁, H', hsub,
    (mul_pos (Real.exp_pos _) hH).trans_le hlarge, hlarge,
    hv h₁, hW h₁, hheight h₁, hm h₁, hmp h₁, ?_⟩
  intro h hh
  have hpickh : pick h = h := ite_eq_left (hsub hh)
  simpa only [hpickh, (hsame h hh).1, (hsame h hh).2] using hfactor h

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι J Ω L : Type*} [Fintype σ] [Fintype ι] [Fintype J] [Fintype Ω]
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

def HasCommonRefilteredOrbitFactors
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))
    (side : σ → ℝ) (q : ℝ) (m : ℕ)
    (W : LieSubalgebra ℚ F.AssociatedGraded)
    (g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group) : Prop :=
  ∃ e middle r : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group,
    e * middle * r = g ∧
    (∀ t : σ → ℝ, eval₂ t (F.realGradedSymbolPolynomial b w hF (fun _ => 1)
      (F.realPolynomialSymbolHom b w hF (fun _ => 1) middle).coord) ∈
        realificationLieSubalgebra W) ∧
    F.PolynomialSlowBound b (fun _ => 1) side (Real.exp q) e ∧
    F.PolynomialRationalGrid b (fun _ => 1) m r ∧
    coefficients (e.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
    coefficients (r.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
    coefficients (middle.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 =
      coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0

theorem exists_weighted_common_refiltered_orbit_factors (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι J Ω L : Type*} [Fintype σ] [Fintype ι] [Fintype J] [Fintype Ω]
      [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))
      (eta : J → L →ₗ[ℚ] ℚ) {p : ℝ}, 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (Fintype.card J : ℝ) ≤ p →
      (∀ i j k, rationalLogHeight (b.repr ⁅b i, b j⁆ k) ≤ p) →
      ∀ side : σ → ℝ, (∀ i, Real.exp ((p + 2) ^ C) ≤ side i) →
      ∀ (outer : FiniteProbabilityWeights Ω) (H : Finset Ω), 0 < outer.mass H →
      ∀ g : Ω → (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group,
      (∀ a ∈ H, ∀ j, F.ControlledSymbolFactorization b w hF (eta j) side
        (F.realPolynomialSymbolHom b w hF (fun _ => 1) (g a)) p) →
      let q := (p + 2) ^ C + (((p + 2) ^ 2 + 2) ^ 63 + 1) + p + 1
      ∃ (W : LieSubalgebra ℚ F.AssociatedGraded)
        (v : Fin (Fintype.card ι) → F.AssociatedGraded) (m : ℕ) (H' : Finset Ω),
        H' ⊆ H ∧ 0 < outer.mass H' ∧
        Real.exp (-((q + 2) ^ 5 + q)) * outer.mass H ≤ outer.mass H' ∧
        Submodule.span ℚ (Set.range v) = W.toSubmodule ∧
        BasisGradedSubmodule (F.associatedGradedBasis b w hF) w W.toSubmodule ∧
        (∀ i k, rationalLogHeight ((F.associatedGradedBasis b w hF).repr (v i) k) ≤ q) ∧
        (∀ j x, x ∈ F.realGradedRefiltrationLayer W s → realifyFunctional (eta j) x = 0) ∧
        0 < m ∧ (m : ℝ) ≤ Real.exp q ∧
        ∀ a ∈ H', F.HasCommonRefilteredOrbitFactors b w hF side q m W (g a) := by
  obtain ⟨C, hC, hcommon⟩ := exists_common_refiltered_factorization s
  refine ⟨C, hC, ?_⟩
  intro σ ι J Ω L _ _ _ _ _ _ F b w hF eta p hp hι hσ hJ hstructure
    side hside outer H hH g hfactor
  classical
  let q := (p + 2) ^ C + (((p + 2) ^ 2 + 2) ^ 63 + 1) + p + 1
  have hpC : 0 ≤ (p + 2) ^ C := by positivity
  have hpheight : 0 ≤ ((p + 2) ^ 2 + 2) ^ 63 := by positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hq : 0 ≤ q := hp.trans hpq
  have hcq : (p + 2) ^ C ≤ q := by dsimp [q]; linarith
  have hvq : ((p + 2) ^ 2 + 2) ^ 63 + 1 ≤ q := by dsimp [q]; linarith
  have hsidepos (i) : 0 < side i := (Real.exp_pos _).trans_le (hside i)
  have hHne : H.Nonempty := by
    by_contra hn
    have he : H = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp only [he, FiniteProbabilityWeights.mass, Finset.sum_empty, lt_self_iff_false] at hH
  obtain ⟨a₀, ha₀⟩ := hHne
  let pick (a : Ω) := if a ∈ H then a else a₀
  have hpick (a) : pick a ∈ H := by
    dsimp only [pick]
    split_ifs with ha
    · exact ha
    · exact ha₀
  choose W v m e middle r hv hW hheight hfreq hm hmp hprod hmid he hr he0 hr0 hmiddle0 hanchor
    using fun a => hcommon F b w hF eta p hp hι hσ hJ hstructure side hside
      (g (pick a)) (hfactor (pick a) (hpick a))
  obtain ⟨a₁, _, H', hsub, _, hsame, hmass⟩ :=
    exists_weighted_common_fast_subalgebra_and_denominator
      (F.associatedGradedBasis b w hF) outer H hH W m (Fintype.card ι) hq
      (hι.trans hpq) (hι.trans hpq)
      (fun a _ => ⟨v a, hv a, fun i k => (hheight a i k).trans hvq⟩)
      (fun a _ => ⟨hm a, (hmp a).trans (Real.exp_le_exp.mpr hcq)⟩)
  refine ⟨W a₁, v a₁, m a₁, H', hsub,
    (mul_pos (Real.exp_pos _) hH).trans_le hmass, hmass, hv a₁, hW a₁,
    fun i k => (hheight a₁ i k).trans hvq, hfreq a₁, hm a₁,
    (hmp a₁).trans (Real.exp_le_exp.mpr hcq), ?_⟩
  intro a ha
  have hpa : pick a = a := ite_eq_left (hsub ha)
  have hout : F.HasCommonRefilteredOrbitFactors b w hF side q (m a) (W a) (g (pick a)) := by
    refine ⟨e a, middle a, r a, hprod a, hmid a, ?_, hr a, he0 a, hr0 a, hmiddle0 a⟩
    exact F.polynomialSlowBound_mono b (fun _ => 1) side hsidepos
      (Real.exp_le_exp.mpr hcq) (e a) (he a)
  simpa only [hpa, (hsame a ha).1, (hsame a ha).2] using hout

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem PolynomialSlowBound.to_symbol (w : σ → ℕ) (T : σ → ℝ) (M : ℝ)
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (hg : F.PolynomialSlowBound b w T M g) :
    F.SymbolSlowBound b ω hF w T M (F.realPolynomialSymbolHom b ω hF w g) := by
  intro z
  change |((F.polynomialSymbolBasis b ω hF w).baseChange ℝ).repr
    (F.realSymbolOfPolynomial b ω hF w g.coord) z| ≤ _
  rw [F.realSymbolOfPolynomial_coordinate]
  exact hg z.val.1 z.val.2

theorem PolynomialRationalGrid.to_symbol (w : σ → ℕ) (l : ℕ)
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (hg : F.PolynomialRationalGrid b w l g) :
    F.SymbolRationalGrid b ω hF w l (F.realPolynomialSymbolHom b ω hF w g) := by
  obtain ⟨a, ha⟩ := hg
  refine ⟨fun z => a z.val, ?_⟩
  funext z
  change (a z.val : ℝ) = (l : ℝ) *
    ((F.polynomialSymbolBasis b ω hF w).baseChange ℝ).repr
      (F.realSymbolOfPolynomial b ω hF w g.coord) z
  rw [F.realSymbolOfPolynomial_coordinate]
  exact congrFun ha z.val

theorem HasCommonRefilteredOrbitFactors.symbolFactors [Fintype σ] [Fintype ι]
    (T : σ → ℝ) (q : ℝ) (l : ℕ) (W : LieSubalgebra ℚ F.AssociatedGraded)
    (g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
    (h : F.HasCommonRefilteredOrbitFactors b ω hF T q l W g) :
    ∃ El Pl Rl : F.RealPolynomialSymbolGroup (fun _ : σ => 1),
      El * Pl * Rl = F.realPolynomialSymbolHom b ω hF (fun _ => 1) g ∧
      Pl.coord ∈ realificationLieSubalgebra
        (F.symbolPointwiseSubalgebra b ω hF (fun _ => 1) W) ∧
      F.SymbolSlowBound b ω hF (fun _ => 1) T (Real.exp q) El ∧
      F.SymbolRationalGrid b ω hF (fun _ => 1) l Rl := by
  obtain ⟨e, p, r, hprod, hmid, he, hr, _, _, _⟩ := h
  refine ⟨F.realPolynomialSymbolHom b ω hF (fun _ => 1) e,
    F.realPolynomialSymbolHom b ω hF (fun _ => 1) p,
    F.realPolynomialSymbolHom b ω hF (fun _ => 1) r, ?_, ?_, ?_, ?_⟩
  · simpa only [map_mul] using congrArg (F.realPolynomialSymbolHom b ω hF (fun _ => 1)) hprod
  · exact (F.mem_real_symbolPointwiseSubalgebra_iff_values b ω hF (fun _ => 1) W _).mpr hmid
  · exact he.to_symbol F b ω hF (fun _ => 1) T (Real.exp q) e
  · exact hr.to_symbol F b ω hF (fun _ => 1) l r

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι κ L M : Type*} [Fintype ι] [Fintype κ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ M) (ν : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

theorem realPolynomialGroupMap_coefficient (w : σ → ℕ)
    (g : (F.realification.adaptedPolynomialFiltration w).Group) (α : σ →₀ ℕ) :
    coefficients ((F.realPolynomialGroupMap G φ hφ w g).coord :
      VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)) α =
      realificationLieHom φ (coefficients
        (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α) := by
  rw [F.realPolynomialGroupMap_log, coefficients_map]
  rfl

omit [Fintype ι] [Fintype κ] in

theorem realPolynomialGroupMap_middle_mem (w : σ → ℕ)
    (W : LieSubalgebra ℚ F.AssociatedGraded)
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (hg : ∀ z : σ → ℝ, eval₂ z (F.realGradedSymbolPolynomial b ω hF w
      (F.realPolynomialSymbolHom b ω hF w g).coord) ∈ realificationLieSubalgebra W) :
    ∀ z : σ → ℝ, eval₂ z (G.realGradedSymbolPolynomial c ν hG w
      (G.realPolynomialSymbolHom c ν hG w
        (F.realPolynomialGroupMap G φ hφ w g)).coord) ∈
      realificationLieSubalgebra (W.map (F.associatedGradedMap G φ hφ)) := by
  have hmem := (F.mem_real_symbolPointwiseSubalgebra_iff_values b ω hF w W _).mpr hg
  have hmap := F.real_symbolPointwiseSubalgebra_map_mem G b ω hF c ν hG φ hφ w W
    (F.realPolynomialSymbolHom b ω hF w g).coord hmem
  have hsymbol : realificationLieHom (F.filteredPolynomialSymbolMap G φ hφ w)
      (F.realPolynomialSymbolHom b ω hF w g).coord =
      (G.realPolynomialSymbolHom c ν hG w
        (F.realPolynomialGroupMap G φ hφ w g)).coord :=
    F.realFilteredPolynomialSymbolMap_polynomial G φ hφ b ω hF c ν hG w g.coord
  rw [hsymbol] at hmap
  exact (G.mem_real_symbolPointwiseSubalgebra_iff_values c ν hG w _ _).mp hmap

theorem exists_common_refiltered_mapped_orbit_factors
    {H : ℕ} (hentries : ∀ i j, RationalHeightLE (c.repr (φ (b j)) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hsource : (Fintype.card ι : ℝ) ≤ p)
    (htarget : (Fintype.card κ : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p)
    (l : ℕ) (hl : 0 < l) (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 4) ∧ l ∣ m ∧
      ∀ (side : σ → ℝ), (∀ i, 0 < side i) →
      ∀ (q : ℝ) (W : LieSubalgebra ℚ F.AssociatedGraded)
        (g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group),
      F.HasCommonRefilteredOrbitFactors b ω hF side q l W g →
      G.HasCommonRefilteredOrbitFactors c ν hG side ((p + 2) ^ 3 + q) m
        (W.map (F.associatedGradedMap G φ hφ))
        (F.realPolynomialGroupMap G φ hφ (fun _ : σ => 1) g) := by
  obtain ⟨m, hm, hmp, hlm, hgrid⟩ :=
    F.exists_realPolynomialGroupMap_grid G b c φ hφ (fun _ : σ => 1)
      hentries hp hsource htarget hHp l hl hlp
  refine ⟨m, hm, hmp, hlm, ?_⟩
  intro side hside q W g hfactor
  obtain ⟨e, middle, r, hprod, hmid, he, hr, he0, hr0, hmiddle0⟩ := hfactor
  let π := F.realPolynomialGroupMap G φ hφ (fun _ : σ => 1)
  refine ⟨π e, π middle, π r, ?_, ?_, ?_, hgrid r hr, ?_, ?_, ?_⟩
  · rw [← map_mul, ← map_mul, hprod]
  · exact F.realPolynomialGroupMap_middle_mem G b ω hF c ν hG φ hφ
      (fun _ : σ => 1) W middle hmid
  · have hslow := F.realPolynomialGroupMap_slow_exp G b c φ hφ
      (fun _ : σ => 1) hentries hp hsource hHp side hside (Real.exp_nonneg q) e he
    simpa only [Real.exp_add] using hslow
  · change coefficients ((F.realPolynomialGroupMap G φ hφ (fun _ : σ => 1) e).coord :
      VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)) 0 = 0
    rw [F.realPolynomialGroupMap_coefficient, he0, map_zero]
  · change coefficients ((F.realPolynomialGroupMap G φ hφ (fun _ : σ => 1) r).coord :
      VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)) 0 = 0
    rw [F.realPolynomialGroupMap_coefficient, hr0, map_zero]
  · change coefficients ((F.realPolynomialGroupMap G φ hφ (fun _ : σ => 1) middle).coord :
        VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)) 0 =
      coefficients ((F.realPolynomialGroupMap G φ hφ (fun _ : σ => 1) g).coord :
        VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)) 0
    rw [F.realPolynomialGroupMap_coefficient, F.realPolynomialGroupMap_coefficient, hmiddle0]

end Erdos3.NilpotentLieFiltration

end

end OAI
