import New.UpperBound.Divisibility.MarkedPrimes
import New.UpperBound.Kernels.ThetaLiftGauge

/-!
# p-adic gauge bounds for chains of theta lifts and restrictions to `Y_m`

This file proves that the value of a chain of theta lifts is a sum over classes. It deduces a
general p-adic gauge bound for the chain. It then gives gauge and norm bounds for the restriction
`New.Data.restrictToY` to `Y_m`, and describes the values of source forms. `New.weylGauge` is the
gauge of a vector at a finite point `g`: a maximum of p-adic absolute values read through the
embedding ι of `[PadicPlace p]`. `New.GaugeLe d c φ` says that `φ g` has gauge at most `c` at
`g * d` for all `g`.

## Main definitions and results

* `New.Data.chainCombination_eq_sum`: take a chain that is jointly invariant for the kernels
  `D.liftKernel ϑ`. Its value at `g D.m` is a sum over tuples of classes for the levels
  `D.levelX j`, `j < D.m`, and over the tuples x in the support of Ψ. The terms are the kernel
  products times Ψ x.
* `New.Data.IsWeakChainDatum.gaugeLe_chain`: let `Ψ` be a weak chain datum for the twist `ϑ`, and
  let the places of `ϑ` have norm prime to `p`. Suppose every datum of the chain, changed by an
  operator `t j` that commutes with the levels, multiplies gauges by at most `p ^ r j` from the base
  point `d j` to `d (j + 1)`. Then the `Ψ`-combination of the chains sends a source form of gauge at
  most 1 at `d 0` to a form of gauge at most `p ^ ∑ r j` at `d D.m`.

Throughout, `D : Data P` fixes a CM field `E = D.E`, primes `p₀`, `p₁`, `N = D.N`, an integer
`π = D.piN` of `E` with `π π̄ = N`, and a length `m = D.m`. The type `D.X j` indexes a basis of a
definite hermitian space `X_j` over `E`, and `Gf D.E (D.X j)` is the group of finite adelic points
of its unitary group. Forms on `X_j` (`D.FormX j`) are algebraic automorphic forms on this group.
The level of `X_j` is `D.levelX j`, the elements of the integral subgroup `D.chosenLevel` whose last
row is `(0, …, 0, 1)` modulo `π`. Source forms are the forms on `X_0` fixed by `D.levelX 0`.

Notions from other files:
* `New.Data.Twist`: A twist: a tame character (`New.Data.TameChar`) whose tame part is non-trivial
  at every place of its set Q.
* `New.Data.Translations`: Tuples (x_j) of finite adelic matrices with rows X_{j+1} and columns X_j,
  the translations that define the data of a chain.
* `New.IsJointlyInvariant`: the tensor ∑_x L_x ⊗ Φ_{x,m−1} ⊗ ⋯ ⊗ Φ_{x,0} is unchanged by the joint
  action of the levels K_j, j < m.
* `New.Data.translateDatum`: The j-th datum of the tuple x: the normalised vacuum of Hom(X_j,
  X_{j+1}) translated by the finite Heisenberg operator of x_j.
* `New.Data.piNPlaces`: the set of primes dividing `π`, where `π π̄ = N`.
-/

noncomputable section

namespace New.Data

/-!
## Standard data at p and the chain value as a sum over classes

Ψ is a finitely supported function on tuples x of translations, and `New.Data.IsWeakChainDatum`
records where these are integral, that the coefficients Ψ x are integral away from the twist, and
that the combination is jointly invariant under the levels.
-/

section StandardData

open Finset Parameters Space

variable {P : Parameters} (D : Data P) {p : ℕ} [Fact p.Prime]

/-- A place of E above a prime p ≠ N does not lie above N, and its conjugate does not divide π. -/
lemma natCast_notMem_and_star_notMem_piNPlaces_of_ne (hp : p ≠ D.N) {w : FinPlace D.E}
    (hw : ↑p ∈ w.asIdeal) :
    ↑D.N ∉ w.asIdeal ∧ star w ∉ D.piNPlaces := by
  -- A place of `piNPlaces` contains `N`, and `N` is fixed by conjugation.
  suffices hN : ↑D.N ∉ w.asIdeal from
    ⟨hN, fun h ↦ hN (by simpa using D.isSplitLevel_piNPlaces.natCast_level_mem _ h)⟩
  simp [w.natCast_mem_iff_dvd hw, Nat.prime_dvd_prime_iff_eq, Fact.out, hp]

/-- Let x be an admissible tuple of translations for q (the `x_j` become integral at the places
prime to q after multiplication by the image of `New.Data.piMBar`), and S a set of places such that
at each w in S, q is not in w, and δ is `New.Data.piMBar` or the conjugate of w is not chosen. Then
x_j lies in `integralAfter δ S`. -/
lemma mem_integralAfter_of_mem_admissibleTranslations {q : ℕ} {x : D.Translations} {j : ℕ}
    {δ : NumberField.RingOfIntegers P.K}
    {S : FinPlace (P.E D.towerExp) → Prop} (hx : x ∈ D.admissibleTranslations q)
    (hS : ∀ w : FinPlace D.E, S w → ↑q ∉ w.asIdeal ∧ (δ = D.piMBar ∨ ¬D.IsChosen (star w))) :
    x j ∈ integralAfter δ S := by
  intro i w hw
  obtain ⟨hq, hδ⟩ := hS w hw
  -- `star piM * x j i` is integral at `w`, and `star piM` is the image of `piMBar`, so it is
  -- enough that `δ * x j i` is at most as large at `w`
  refine (hx j i w hq).trans' ?_
  have h_coe (y : NumberField.RingOfIntegers P.K) : algebraMap P.K D.E y = (algebraMap
      (NumberField.RingOfIntegers P.K) (NumberField.RingOfIntegers D.E) y : D.E) := rfl
  rcases hδ with rfl | not_chosen
  · simp [h_coe]
  -- if `star w` is not chosen, `piMBar` is a unit at `w`, while `δ` is integral
  have h_unit : w.valuation D.E
      (algebraMap (NumberField.RingOfIntegers P.K) (NumberField.RingOfIntegers D.E) D.piMBar : D.E)
        =
        1 := w.valuation_eq_one_iff_notMem.2 (by simpa [IsChosen] using not_chosen)
  simpa [h_unit, h_coe] using mul_le_of_le_one_left' (w.valuation_le_one
    (algebraMap (NumberField.RingOfIntegers P.K) (NumberField.RingOfIntegers D.E) δ))

/-- Let S be a set of finite places, and let x_j be integral at the places of `Set.conjClosure S`,
those in S and their conjugates. Then the datum of x at j, the integral vacuum of the space
Hom(X_j, X_{j+1}) (`homX j`) translated by x_j, is fixed by `projOn (homX j) S`. This operator is
the mean, over integral vectors y, of the Heisenberg translations by the part of y at S and the
conjugate places. -/
lemma projOn_translateDatum {x : D.Translations} {j : ℕ} {S : Set (FinPlace (P.E D.towerExp))}
    (h_int : x j ∈ integralAfter 1 (· ∈ Set.conjClosure S)) :
    projOn (homX j) S (D.translateDatum x j).val = (D.translateDatum x j).val := by
  simp_all [translateDatum, projOn_finHeisenbergOp, intVacuum, mem_integralBox, idem_mul_mem_Ô,
    integralAfter]

/-- If `x` lies in `D.admissibleTranslations q`, then some `x'` in `D.admissibleTranslations q` that
vanishes at all places prime to `D.M * q` (where `D.M = p₀ p₁`) has the same data:
`D.translateDatum x = D.translateDatum x'`. -/
lemma exists_supported_translateDatum_eq {q : ℕ} {x : D.Translations}
    (hx : x ∈ D.admissibleTranslations q) :
    ∃ x' ∈ D.admissibleTranslations q ∩ D.supportedTranslations (D.M * q),
      D.translateDatum x = D.translateDatum x' := by
  -- The part of `x` at the places prime to `M * q` is integral and fixes the vacuum, so it can
  -- be dropped.
  let S : Set (FinPlace D.E) := {w | ↑(D.M * q) ∈ w.asIdeal}
  refine ⟨fun j ↦ idem S • x j, ⟨fun j i w hw ↦ ?_,
    fun j i w (hw : w ∉ S) ↦ by simp [hw]⟩, funext fun j ↦ ?_⟩
  · by_cases h_mem : w ∈ S
    · simpa [h_mem] using hx j i w hw
    · simp [h_mem]
  -- the hypothesis of `mem_integralAfter_of_mem_admissibleTranslations` for `δ = 1`; outside `S`,
  -- both `q` and `M = piM * star piM` are units
  have h_unit_outside (w : FinPlace D.E) (hw : w ∈ Sᶜ) :
      ↑q ∉ w.asIdeal ∧ (1 = D.piMBar ∨ ¬D.IsChosen (star w)) := by
    simp_all [S, ← piM_mul_star, IsChosen, w.2.mul_mem_iff_mem_or_mem]
  have h_int : idem Sᶜ • x j ∈ stdLattice D.E (D.X (j + 1) × D.X j) := fun i ↦
    idem_mul_mem_Ô.2 fun w hw ↦ by simpa using D.mem_integralAfter_of_mem_admissibleTranslations hx
                                     h_unit_outside i w hw
  -- The set `S` is stable under conjugation, so the two parts compose with no phase.
  have h_orth : star (idem Sᶜ : 𝔸f D.E) * idem S = 0 := by
    ext w
    by_cases h_mem : w ∈ S <;> simp_all [S, star_idem]
  -- The two parts of `x j` add up to `x j`, and the integral part fixes the vacuum.
  have h_comp := (D.homX j).finHeisenbergOp_finHeisenbergOp (x := idem S • x j) (y := idem Sᶜ • x j)
    (f := (D.homX j).vacElem)
  rw [finHeisenbergOp_vacElem h_int, star_smul, smul_dotProduct, dotProduct_smul, smul_smul, h_orth,
    ← add_smul, idem_compl, add_sub_cancel, one_smul] at h_comp
  have h_datum : (D.homX j).finHeisenbergOp (x j) (D.homX j).vacElem =
      (D.homX j).finHeisenbergOp (idem S • x j) (D.homX j).vacElem := by simpa using h_comp.symm
  ext1
  simp [translateDatum, Parameters.intVacuum, h_datum]

variable {D} {ϑ : D.Twist} {Ψ : D.Translations →₀ ℂ}

/-- **A chain of lifts is a plain sum.** Let `D.liftKernel ϑ j` be the theta kernel from forms on
`X_j` to forms on `X_{j+1}` for the twist `ϑ`, and let the tensor `∑ x, Ψ x • ⊗ⱼ Φ x j` of data be
jointly invariant under the levels `D.levelX j`, `j < D.m`. Let `φ` be a source form, a form on
`X_0` fixed by its level. The form `chainCombination ϑ Ψ Φ D.m φ` is the sum over `x` of `Ψ x` times
the result of `D.m` successive lifts of `φ` with data `Φ x`. Its value at `g D.m` is the sum, over
tuples `c` of classes for these levels and over `x` in the support of `Ψ`, of `Ψ x` times
`kernelProduct`: the kernels at the points `classPoints c g`, applied in turn to the value of `φ` at
the first point. -/
theorem chainCombination_eq_sum {Φ : D.Translations → ∀ j : ℕ, (D.homX j).finitePart}
    (h_inv : IsJointlyInvariant (D.liftKernel ϑ) D.m Ψ.support
      (fun x : D.Translations ↦ Ψ x • LinearMap.id) Φ)
    (φ : D.SourceForm) (g : ∀ j : ℕ, Gf D.E (D.X j)) :
    (chainCombination ϑ Ψ Φ D.m φ).val (g D.m) =
      ∑ c : ∀ j : Fin D.m, StdClasses (D.levelX j), ∑ x ∈ Ψ.support,
        Ψ x • kernelProduct (D.liftKernel ϑ) (Φ x) φ (classPoints c g) D.m := by
  -- The classes for the levels below `D.m` have trivial automorphism groups.
  have free (j : ℕ) (hj : j < D.m) : ∀ g, classAut stdRatPoints (D.levelX j) g = ⊥ :=
    D.classAut_eq_bot_of_le_chosenLevel inf_le_left (by grind [card_X, D.n_mono hj.le])
  simpa [Finsupp.sum] using h_inv.sum_chain_eq_sum_kernelProduct _ free φ.prop g

/-- Let `Ψ` be a weak chain datum for the twist `ϑ`; only the support condition is used: each tuple
`x` in the support of `Ψ` is integral, up to the factor `star D.piM`, at the places prime to
`ϑ.normQ * N`. For a prime `p ≠ N` coprime to `ϑ.normQ`, the datum of `x` at `j` lies in
`New.Parameters.standardData` (the span of the translates of the integral vacuum by points that `δ`
makes integral above `p`) for `δ = D.piMBar`, and for every `δ` if `p` does not divide
`D.M = p₀ p₁`. -/
lemma IsWeakChainDatum.translateDatum_mem_standardData (h_weak : IsWeakChainDatum ϑ Ψ)
    [PadicPlace p] (hQ : p.Coprime ϑ.normQ) (hp : p ≠ D.N) {x : D.Translations}
    (hx : x ∈ Ψ.support) (j : ℕ) {δ : NumberField.RingOfIntegers P.K}
    (hδ : δ = D.piMBar ∨ ¬p ∣ D.M) :
    (D.translateDatum x j).val ∈ Parameters.standardData (homX j) δ := by
  -- The datum is the translate of the vacuum by `x j`, which `δ` has to make integral above `p`.
  suffices h_int : x j ∈ Parameters.integralAfter δ fun w ↦ ↑p ∈ w.asIdeal from
    Submodule.subset_span ⟨x j, h_int, rfl⟩
  refine D.mem_integralAfter_of_mem_admissibleTranslations (h_weak.support_subset x hx) fun w hw ↦
    ⟨?_, ?_⟩
  · -- `w` lies above `p`, which is prime to `ϑ.normQ` and to `N`
    rw [Nat.cast_mul, w.2.mul_mem_iff_mem_or_mem, not_or]
    exact ⟨w.2.notMem_of_isCoprime_of_mem hQ.cast hw,
      (D.natCast_notMem_and_star_notMem_piNPlaces_of_ne hp hw).1⟩
  -- as `M = piM * star piM`, a chosen `star w` above `p` forces `p ∣ M`
  refine hδ.imp_right fun h ↦ ?_
  simp_all [← piM_mul_star, IsChosen, ← w.natCast_mem_iff_dvd, w.2.mul_mem_iff_mem_or_mem]

end StandardData

/-!
## Valuation bound for chains with data changed by commuting operators

`New.Kernel.raises` collects the data whose kernel multiplies gauges by at most a constant.
-/

section ChainValuation

open Finset Real

variable {P : Parameters} {D : Data P}
  {p : ℕ} [Fact p.Prime] [PadicPlace p]
  {ϑ : D.Twist} {Ψ : D.Translations →₀ ℂ}

/-- Let the tensor of data `∑ x, Ψ x • ⊗ⱼ Φ x j` be jointly invariant: it is unchanged when `Φ x j`
is moved by `(D.liftKernel ϑ j).ω (a j, a (j + 1))`, for `a j` in the level `D.levelX j` and
`a j = 1` for `j ≥ m = D.m`. Let the `Ψ x` be integral at `p`, and let the kernel of each `Φ x j`
send vectors of gauge `c` at `g * d j` to vectors of gauge at most `p ^ r j * c` at `g' * d (j + 1)`
(`raises`). Then the `Ψ`-combination of the chains of `m` lifts sends a source form of gauge at most
`1` at `d 0` to a form of gauge at most `p ^ ∑ j < m, r j` at `d m`. -/
lemma gaugeLe_chainCombination {Φ : D.Translations → ∀ j : ℕ, (D.homX j).finitePart}
    (h_inv : IsJointlyInvariant (D.liftKernel ϑ) D.m Ψ.support
      (fun x : D.Translations ↦ Ψ x • LinearMap.id) Φ)
    (h_int : ∀ x : D.Translations, ‖ιₚ (Ψ x)‖ ≤ 1) (d : ∀ j : ℕ, Gf D.E (D.X j)) {r : ℕ → ℝ}
    (h_raise : ∀ x ∈ Ψ.support, ∀ j < D.m,
      Φ x j ∈ (D.liftKernel ϑ j).raises (d j) (d (j + 1)) (p ^ r j))
    {φ : D.SourceForm} (hφ : GaugeLe (d 0) 1 φ.val) :
    GaugeLe (d D.m) (p ^ ∑ j ∈ range D.m, r j) (chainCombination ϑ Ψ Φ D.m φ) := by
  -- The value at `h` is a plain sum of products of kernels, each of gauge at most `∏ p ^ r j`. The
  -- gauge is ultrametric, so the whole sum obeys the same bound.
  intro h
  obtain ⟨g, rfl⟩ : ∃ g : ∀ j : ℕ, Gf D.E (D.X j), g D.m = h := ⟨Pi.mulSingle D.m h, by simp⟩
  rw [chainCombination_eq_sum h_inv]
  refine weylGauge_sum_le _ (by positivity) fun c _ ↦
    weylGauge_sum_le _ (by positivity) fun x hx ↦ ?_
  have h_term : weylGauge D.columnCount (D.lastEntry D.m) (g D.m * d D.m)
      (kernelProduct (D.liftKernel ϑ) (Φ x) φ.val (classPoints c g) D.m) ≤
      (∏ j ∈ range D.m, max ((p : ℝ) ^ r j) 0) * 1 := by
    simpa only [classPoints_of_le c g le_rfl] using apply_kernelProduct_le_prod_mul (D.liftKernel ϑ)
      (fun j g ↦ weylGauge D.columnCount (D.lastEntry j) (g * d j)) (by simp) (h_raise x hx) hφ
      (classPoints c g)
  grw [weylGauge_smul, h_term, h_int]
  simp [rpow_nonneg, rpow_sum_of_pos, NeZero.pos]

/-- Let `Ψ` be a weak chain datum for the twist `ϑ`: the tensor `∑ x, Ψ x • ⊗ⱼ D.translateDatum x j`
is invariant under the joint action of the levels `D.levelX j`, `j < m = D.m`, and the `Ψ x` are
integral at the primes that do not divide `ϑ.normQ`, such as `p` (`hQ`). Let `t j` be linear
operators on the finite part of `D.homX j`, and let `d j` be base points. Suppose that (a) the `t j`
commute with the action of `D.levelX j × D.levelX (j + 1)` on the data `D.translateDatum x j`, `x`
in the support of `Ψ`; (b) the theta kernel of each `t j (D.translateDatum x j)` sends vectors of
gauge at most `c` at `g * d j` to vectors of gauge at most `p ^ r j * c` at `g' * d (j + 1)`
(`raises`); (c) the source form `φ` has gauge at most `1` at `d 0`. Then the `Ψ`-combination of the
chains of `m` lifts with data `t j (D.translateDatum x j)` sends `φ` to a form of gauge at most
`p ^ ∑ j < m, r j` at `d m`. -/
lemma IsWeakChainDatum.gaugeLe_chain (h_weak : IsWeakChainDatum ϑ Ψ) (hQ : p.Coprime ϑ.normQ)
    (t : ∀ j : ℕ, Module.End ℂ (D.homX j).finitePart)
    (ht : ∀ j : ℕ, ∀ x ∈ Ψ.support, ∀ a : D.levelX j, ∀ b ∈ D.levelX (j + 1),
      (D.liftKernel ϑ j).ω (a, b) (t j (D.translateDatum x j)) =
        t j ((D.liftKernel ϑ j).ω (a, b) (D.translateDatum x j)))
    (d : ∀ j : ℕ, Gf D.E (D.X j)) {r : ℕ → ℝ}
    (h_raise : ∀ x ∈ Ψ.support, ∀ j < D.m,
      t j (D.translateDatum x j) ∈ (D.liftKernel ϑ j).raises (d j) (d (j + 1)) (p ^ r j))
    {φ : D.SourceForm} (hφ : GaugeLe (d 0) 1 φ.val) :
    GaugeLe (d D.m) (p ^ ∑ j ∈ range D.m, r j)
      (chainCombination ϑ Ψ (fun (x : D.Translations) (j : ℕ) ↦ t j (D.translateDatum x j))
        D.m φ) := by
  -- The changed data are still jointly invariant, as the `t j` commute with the levels.
  have h_inv : IsJointlyInvariant (D.liftKernel ϑ) D.m Ψ.support
      (fun x ↦ Ψ x • LinearMap.id) fun x j ↦ t j (D.translateDatum x j) := fun a ha β ↦ by
    -- apply the invariance of the original data to `β` composed with the tensor of the `t j`
    simpa +contextual [*] using
      h_weak.isJointlyInvariant a ha (β ∘ₗ TensorChain.map (fun j ↦ t j) D.m)
  exact gaugeLe_chainCombination h_inv (fun x ↦ by simpa using h_weak.integral x p hQ ιₚ) d h_raise
    hφ

lemma norm_star_piMBar_le_one : ‖ιₚ (star D.piMBar)‖ ≤ 1 :=
  norm_le_one_of_isIntegral (ιₚ.comp (starRingEnd _)) D.piMBar.prop.algebraMap

end ChainValuation

end New.Data

/-! ## Gauge and norm bounds for the restriction of forms -/

section RestrictionGauge

open Matrix Finset Valued WithZero New IsSplitLevel Gf NeZero Fintype

namespace New.Data

variable {P : Parameters} (D : Data P) {p : ℕ} [Fact p.Prime] [PadicPlace p]
-- Keeps definitional checks from unfolding the finite sums.
seal Finset.sum in
open scoped Classical in
/-- Let `φ : D.FormX D.m` be an algebraic automorphic form on the unitary group of the hermitian
space `X_m`, and `D.restrictToY φ` its restriction to the subspace `Y_m` orthogonal to the last
basis vector. For each infinite place `τ : D.Φ` of `E`, let `w = inducedPlace τ` be the place above
`p` that `ιₚ ∘ τ` induces; the map `adeleExtension (weightEmbedding ιₚ τ)` reads an adele in `ℂ_[p]`
through its component at the conjugate place `w̄`. Suppose that this component of `d` is
`diag (1, …, 1, N)` if `w̄` lies in `D.piNPlaces`, the primes dividing `π = D.piN` (where
`π π̄ = N`), and `1` otherwise. Then `GaugeLe d c φ` implies the bound `c` for the restriction, with
base point `1`. -/
lemma GaugeLe.restrictToY_of_diag {d : Gf D.E (D.X D.m)}
    (hd : ∀ τ : D.Φ, GeneralLinearGroup.map (adeleExtension (weightEmbedding ιₚ τ)) d.val =
      diagGL fun i : D.X D.m ↦ if i.isLeft then 1 else
        if star (inducedPlace τ) ∈ D.piNPlaces then Units.mk0 ↑D.N NeZero.out else 1)
    {c : ℝ} {φ : D.FormX D.m} (hφ : GaugeLe d c φ) : GaugeLe 1 c (D.restrictToY φ) := by
  -- The branching map turns the action of `d⁻¹` into a scalar with the absolute value of the scalar
  -- in `restrictToY`; and it has integer entries, so it does not increase norms.
  have h_integral (ξ : WeylIndex (D.X D.m) D.columnCount → ℂ_[p]) :
    ‖D.branching.map (↑) *ᵥ ξ‖ ≤ ‖ξ‖ := by
    simpa using norm_mulVec_le (c := 1) (by simp [IsUltrametricDist.norm_intCast_le_one]) ξ
  intro g
  suffices h_eq : weylGauge D.columnsY (D.lastEntry D.m) (g * 1) ((D.restrictToY φ).1 g) =
      ‖D.branching.map (↑) *ᵥ weylRep D.columnCount (D.lastEntry D.m) (fun τ ↦
          GeneralLinearGroup.map (adeleExtension (weightEmbedding ιₚ τ)) (D.borderU g * d)⁻¹.1) *ᵥ
        (ιₚ ∘ φ.1 (D.borderU g))‖ from
    h_eq.trans_le ((h_integral _).trans (hφ (D.borderU g)))
  -- At `τ`, `(diag (g, 1) * d)⁻¹` is the block matrix `diag (g⁻¹, s τ)`.
  let s (τ : D.Φ) : ℂ_[p]ˣ := (d.1.map (adeleExtension (weightEmbedding ιₚ τ))).det⁻¹
  have h_block (τ : D.Φ) : ((D.borderU g * d)⁻¹.1.map (adeleExtension (weightEmbedding ιₚ τ))).1 =
      GL.blockScalar (fun _ ↦ D.lastIndexEquiv.sumCongr (.refl _))
        (fun τ ↦ ((g * 1)⁻¹.1.map (adeleExtension (weightEmbedding ιₚ τ))).1) (fun τ ↦ s τ) τ := by
    simp [s, ← map_inv, ← ext_iff, borderU, GL.blockScalar, map_inv _ d.1, hd]
  let a : ℂ := ∏ τ : D.Φ, Φ τ (star (D.piN : D.E)) ^ (-D.branchExponent τ)
  have h_restrict : (D.restrictToY φ).1 g = a • D.branching.map (↑) *ᵥ φ.1 (D.borderU g) := rfl
  have h_intertwine : D.branching.map (↑) * weylRep D.columnCount (D.lastEntry D.m) (fun τ ↦
        GeneralLinearGroup.map (adeleExtension (weightEmbedding ιₚ τ)) (D.borderU g * d)⁻¹.1) =
      (∏ τ, s τ ^ D.branchExponent τ) • (weylRep D.columnsY (D.lastEntry D.m) (fun τ ↦
          GeneralLinearGroup.map (adeleExtension (weightEmbedding ιₚ τ)) (g * 1)⁻¹.1) *
        D.branching.map (↑)) :=
    D.isBranchingMap_branching.mul_weylRep _ _ s _ h_block
  -- The scalars: `weightEmbedding ιₚ τ π = ιₚ (Φ τ π̄)` has the absolute value of `N` if
  -- `star (inducedPlace τ)` divides `π`, and is a unit if not.
  have h_norm (τ : D.Φ) : NormedField.valuation.comap (weightEmbedding ιₚ τ) D.piN =
      NormedField.valuation.comap (weightEmbedding ιₚ τ)
        (if star (inducedPlace τ) ∈ D.piNPlaces then D.N else 1) := by
    rw [(isEquiv_placeOfEmb (weightEmbedding ιₚ τ)).eq_iff]
    split <;> simp_all [inducedPlace, placeOfEmb_comp_star, ← v_algebraMap_eq_valuation,
      v_algebraMap_eq_intValuation, intValuation_piN, D.isSplitLevel_piNPlaces.v_natCast, piNPlaces]
  have h_scalar : ‖ιₚ a‖ = ‖((∏ τ, s τ ^ D.branchExponent τ : ℂ_[p]ˣ) : ℂ_[p])‖ := by
    have h_prod : ∏ τ, ‖weightEmbedding ιₚ τ (D.piN : D.E)‖ ^ D.branchExponent τ =
        ∏ τ, ‖weightEmbedding ιₚ τ (if star (inducedPlace τ) ∈ D.piNPlaces then (D.N : D.E) else 1)‖
          ^ D.branchExponent τ :=
      prod_congr rfl fun τ _ ↦ congrArg (· ^ D.branchExponent τ) (congrArg NNReal.toReal (h_norm τ))
    simpa [a, s, hd, apply_ite, starRingEnd_apply (R := D.E)] using h_prod
  have h_comp : ιₚ ∘ (D.branching.map (↑) *ᵥ φ.1 (D.borderU g)) =
      D.branching.map (↑) *ᵥ (ιₚ ∘ φ.1 (D.borderU g)) := funext (by simp [mulVec_eq_sum])
  rw [h_restrict, weylGauge_smul, mulVec_mulVec]
  -- `erw`, as `D.X D.m` and `InitIndex ⊕ Unit` agree only after unfolding
  erw [h_intertwine, smul_mulVec, ← mulVec_mulVec, Units.smul_def, norm_smul]
  rw [h_scalar, weylGauge, h_comp]

/-- For `p ≠ N`, a form that has gauge at most `c` at every point has a restriction to `Y_m` with
the same bound. -/
lemma GaugeLe.restrictToY (hp : p ≠ D.N) {c : ℝ} {φ : D.FormX D.m} (hφ : GaugeLe 1 c φ) :
    GaugeLe 1 c (D.restrictToY φ) :=
  restrictToY_of_diag D
    (by simp [D.natCast_notMem_and_star_notMem_piNPlaces_of_ne hp, p_mem_inducedPlace,
      Units.ext_iff]) hφ

/-- For every embedding `σ` of `ℂ`, the squared norm of `σ` of the value at `h` of the restriction
of `φ` to `Y_m` is at most `exp (x ^ 70) N ^ (-∑ τ, n_τ)` times that of `σ` of the value of `φ` at
`D.borderU h = diag (h, 1)`. Here `weylNormSq` is the squared norm for the Gram matrix of the Weyl
module, `x = D.x` is the large integer `D.natX` that sets the scale of the data `D`, and
`n_τ = D.branchExponent τ` is the sum of the entries of the weight on `X_m` at `τ` minus that of the
weight on `Y_m`. -/
lemma weylNormSq_restrictToY_le (σ : ℂ →+* ℂ) (φ : D.FormX D.m) (h : Gf D.E (D.Y D.m)) :
    weylNormSq (σ ∘ (D.restrictToY φ).val h) ≤
      Real.exp (D.x ^ 70 - (∑ τ : D.Φ, D.branchExponent τ : ℝ) * Real.log D.N) *
        weylNormSq (σ ∘ φ.val (D.borderU h)) := by
  -- As `|σ τ π̄|² = N`, the scalar `c` in `restrictToY` has squared modulus `N ^ (-∑ τ, n_τ)`.
  -- The matrix `branching` has integer entries, so it commutes with `σ`, and it multiplies
  -- `weylNormSq` by at most `exp (x ^ 70)`.
  let c : ℂ := ∏ τ : D.Φ, Φ τ (star (D.piN : D.E)) ^ (-D.branchExponent τ)
  have log_π (τ : D.Φ) : 2 * Real.log ‖weightEmbedding σ τ D.piN‖ = Real.log D.N := by
    have h_pi : (D.piN : D.E) * star (D.piN : D.E) = D.N := by exact_mod_cast D.piN_mul_star
    have h_mul : ‖weightEmbedding σ τ ((D.piN : D.E) * star (D.piN : D.E))‖ = (D.N : ℝ) := by
      rw [h_pi, map_natCast, Complex.norm_natCast]
    -- the embeddings commute with conjugation, so the left side is `‖π‖ ^ 2`
    have h_sq : ‖weightEmbedding σ τ D.piN‖ ^ 2 = (D.N : ℝ) := by
      simpa [← sq, -RingHom.coe_comp] using h_mul
    simpa [Real.log_pow] using congrArg Real.log h_sq
  have res_eq : weylNormSq (σ ∘ (D.restrictToY φ).val h) =
      ‖σ c‖ ^ 2 * weylNormSq (D.branching.map (↑) *ᵥ σ ∘ φ.val (D.borderU h)) :=
    (weylNormSq_comp_smul _ σ c).trans (by simp [c, Function.comp_def, σ.map_mulVec])
  have log_c : Real.log (‖σ c‖ ^ 2) = -((∑ τ, D.branchExponent τ : ℝ) * Real.log D.N) := by
    have h_norm_c : ‖σ c‖ = ∏ τ : D.Φ, ‖weightEmbedding σ τ D.piN‖ ^ (-D.branchExponent τ) := by
      simp [c, starRingEnd_apply (R := D.E)]
    rw [h_norm_c, Real.log_pow, Real.log_prod fun τ _ ↦ zpow_ne_zero _ (by simp), mul_sum,
      sum_mul, ← sum_neg_distrib]
    refine sum_congr rfl fun τ _ ↦ ?_
    rw [Real.log_zpow, mul_left_comm, Nat.cast_ofNat, log_π τ, Int.cast_neg, neg_mul]
  calc
    _ = ‖σ c‖ ^ 2 * weylNormSq (D.branching.map (↑) *ᵥ σ ∘ φ.val (D.borderU h)) := res_eq
    _ ≤ ‖σ c‖ ^ 2 * (Real.exp (D.x ^ 70) * weylNormSq (σ ∘ φ.val (D.borderU h))) := by
      grw [D.isBranchingMap_branching.weylNormSq_le]
    _ ≤ _ := by
      grw [← mul_assoc, Real.le_exp_of_log_le log_c.le, ← Real.exp_add, neg_add_eq_sub]
      exact weylNormSq_nonneg _

end New.Data

end RestrictionGauge

/-! ## Values of source forms -/

section SourceValues

open Matrix

namespace New.Data

/-- The weight on the hermitian space `X₀` has `D.columnCount τ h` columns of height `h` in its
Young diagram at the infinite place `τ`, and last entry `D.lastEntry 0 = 0`. Let `ζ` be a vector of
its Weyl module, `toPoly` of `ιₚ ∘ ζ` its polynomial, and `z_τ` the first column of variables at
`τ`, indexed by the basis of `X₀`. Then `ζ` has gauge at most `1` at `g` if and only if this
polynomial, after the substitution `rowSubst` of `g z_τ` for `z_τ`, is a combination of the
`∏_τ (a_τ! / α_τ!) z_τ ^ α_τ` with `|α_τ| = a_τ` and coefficients in the unit ball `valRingCp p` of
`ℂ_[p]`. Here `g` is read at the place induced by `ιₚ` and the complex embedding `New.Φ τ` chosen at
`τ`, and `a_τ`, the length of the one row of the weight at `τ`, is `D.a` at the places in
`D.aPlaces` and `0` at the others. -/
lemma weylGauge_le_one_iff_mem_span {P : Parameters} (D : Data P) {p : ℕ} [Fact p.Prime]
    [PadicPlace p] (g : Gf D.E (D.X 0)) (ζ : WeylIndex (D.X 0) D.columnCount → ℂ) :
    weylGauge D.columnCount (D.lastEntry 0) g ζ ≤ 1 ↔
      rowSubst (fun τ : D.Φ ↦ (g : Matrix (D.X 0) (D.X 0) (𝔸f D.E)).map
          (adeleExtension (ιₚ.comp (New.Φ τ))))
          (toPoly (fun _ : D.Φ ↦ D.X 0) D.columnCount (ιₚ ∘ ζ)) ∈
        Submodule.span (valRingCp p) (multinomialMonomial ℂ_[p] ''
          {α | ∀ τ : D.Φ, ∑ b : D.X 0, α τ b = if τ ∈ D.aPlaces then D.a else 0}) := by
  classical
  -- The gauge at `g` is the norm of `ζ` moved by the Schur matrix of the conjugate `z` of `g⁻¹`. On
  -- polynomials this substitutes `zᵀ`, and the weight of `X₀` has one row at each place.
  let z (τ : D.Φ) : Matrix (D.X 0) (D.X 0) ℂ_[p] :=
    g⁻¹.val.val.map (adeleExtension (weightEmbedding ιₚ τ))
  have h_card : Fintype.card (D.X 0) = D.k := by simp [D.card_X, Data.n]
  have h_gauge :
      weylGauge D.columnCount (D.lastEntry 0) g ζ = ‖schur D.columnCount z *ᵥ ιₚ ∘ ζ‖ := by
    simp [weylGauge, weylRep, Data.lastEntry, z, -map_inv, -coe_units_inv]
  -- As `g` is unitary, the transpose of the conjugate of `g⁻¹` is `g`.
  have h_transpose (τ : D.Φ) : (z τ)ᵀ =
      (g : Matrix (D.X 0) (D.X 0) (𝔸f D.E)).map (adeleExtension (ιₚ.comp (New.Φ τ))) := by
    ext a b
    simp only [z, U.inv_val_eq_conjTranspose g, transpose_apply, map_apply, conjTranspose_apply,
      ← adeleExtension_star, star_star]
  have h_poly : toPoly (fun _ : D.Φ ↦ D.X 0) D.columnCount (schur D.columnCount z *ᵥ ιₚ ∘ ζ) =
      rowSubst (fun τ : D.Φ ↦ (z τ)ᵀ) (toPoly (fun _ : D.Φ ↦ D.X 0) D.columnCount (ιₚ ∘ ζ)) := by
    simp [toPoly_schur, detPow, schurDetExp]
  have h_row (τ : D.Φ) : D.columnCount τ 1 = if τ ∈ D.aPlaces then D.a else 0 := ite_eq_left rfl
  have h_rank (τ : D.Φ) : 1 < rankAt (fun _ : D.Φ ↦ D.X 0) τ := by grind [D.ten_thousand_le_m]
  have h_one_row (τ : D.Φ) (h : ℕ) (h_one : 1 < h) (h_lt : h < rankAt (fun _ : D.Φ ↦ D.X 0) τ) :
      D.columnCount τ h = 0 := by grind [Data.columnCount]
  simp only [← h_transpose, ← h_poly, ← h_row, h_gauge]
  -- The gauge is the largest norm of a coordinate, and `valRingCp p` is the unit ball.
  rw [toPoly_mem_span_multinomialMonomial_iff h_rank h_one_row,
    pi_norm_le_iff_of_nonneg zero_le_one]
  rfl

end New.Data

end SourceValues

end
