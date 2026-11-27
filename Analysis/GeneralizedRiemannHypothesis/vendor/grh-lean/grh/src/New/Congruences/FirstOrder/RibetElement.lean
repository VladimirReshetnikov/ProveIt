import New.Congruences.FirstOrder.RibetLemma
import New.Congruences.FirstOrder.TraceRelations

/-!
# Ribet's element for conjugate self-dual representations

This file chooses the coefficient ring: polynomials over the integers of `ℚ̄_ℓ`, and models of the
representations, are defined over every large coefficient ring. It bounds the valuation at the lift
and counts the cocycles of the main summand at the lift by its loss and its Selmer group. It then
constructs Ribet's element for a finite family of conjugate self-dual `ℓ`-adic representations of
the Galois group of `E`, some of which have the trace of a twisted main summand plus `t` powers of
the cyclotomic character.

## Main definitions and results

* `New.Selmer.exists_length_le_loss_add_crystallineSelmerLength`: with divisible coefficients, the
  cocycles of the main summand at the lift are counted by its loss, free of the level, and its
  Selmer group.
* `New.Selmer.ribet_columns`: Ribet's element and the bound on its coefficient of `∏ X j`.

Letters: the new places are `w j`, with tame generators `τ j`, Frobenius elements `φ j` and tied
relations `τ j - 1 - X j * (φ j - 1) * H j (φ j)`. The primes `p₀ = D.levelPrime 0`
and `p₁ = D.levelPrime 1` give the principal level; `g₀` is the element of the Galois group that
separates the characters.

Notions from other files:
* `New.CoeffRing`: rings of integers of finite Galois extensions of `ℚ_ℓ` inside `ℚ̄_ℓ`; their
  `normLength` is length over `O`, scaled so that `O/ℓ` has length 1.
* `New.Selmer.IsLiftSetting`: a descent pair `V` (`New.DescentPair`) has the places of the data and
  of the twist `ϑ`, an odd rank `card r ≤ D.r` and an odd difference of ranks `V.rankDiff ≤ D.t`.
  Its type polynomials `c i` are monic squarefree polynomials of degree `card r` over the residue
  fields at the chosen places above `p₀` and `p₁`, with conditions on their roots.
* `New.Lift.InClass F C U`: the local lattices `Y` such that `Bmax ⊗ Y` is spanned by the periods
  fixed both near `1` and along the filter `F`, the Hodge–Tate jumps lie in the sets `U`, and every
  polynomial `Q` with `C s Q` kills the inertial element `s` on the periods.
* `New.Selmer.IsPrimeTriangle`: a linearly ordered tame generator family `w j` with monotone
  exponents `ty j`. An even class of exponent `ty j` that kills the earlier `τ i`, and the earlier
  `φ i` of the same exponent, has its value at `τ j` killed by `ℓ ^ h`. Finitely many test points
  and `g₀` detect the cocycles unramified off `ℓ`, and `g₀` separates the characters up to `ℓ ^ h`.
* `New.Selmer.IsTameGeneratorFamily`: `w j` is not above `ℓ`, `τ j` is the chosen tame generator at
  a place over `w j`, and `φ j` fixes the `ℓ ^ ν`-th roots of unity.
* `New.Selmer.clearingBound` (in `New.Congruences.FirstOrder.TraceRelations`): the clearing bound
  `β_ℓ` per unit of rank of a main summand at `ℓ`.
* `New.Selmer.denominatorError` (in `New.Congruences.FirstOrder.TraceRelations`): the error term
  `e_ℓ`, with crude constants.

## Relation to the literature

Ribet's method in any rank, with congruent summands and tied primes, gives a Hecke element,
polynomial in the tie parameters, that kills all determinants det (1 - u g) modulo the ties. On
lifts it has no term properly dividing the product of all parameters, and the coefficient of that
product has bounded valuation; the orders of the even classes do not enter. Fitting-ideal forms of
Ribet's method are known for distinct summands in any rank and for congruent characters in rank 2.
Related work: Dasgupta–Kakde–Silliman–Wang, The residually indistinguishable case of Ribet's method
for GL2, 2023; Bellaïche–Chenevier, Families of Galois representations and Selmer groups, 2009;
Urban, Selmer groups and the Eisenstein–Klingen ideal, 2001.
-/

namespace New.Selmer

section RibetColumns

open Matrix Polynomial Fintype Module Filter ENNReal Finset CoeffRing

open IsDiscreteValuationRing (addVal)

variable {ℓ : ℕ} [ThePrime ℓ] {P : Parameters} {D : Data P}
  {K Y n r : Type} [Fintype n] [DecidableEq n] [Fintype Y] [Fintype r] [DecidableEq r]

/-- A polynomial over the integers of `ℚ̄_ℓ` is defined over every large coefficient ring. -/
lemma eventually_exists_map_eq (H : (intQpBar ℓ)[X]) : ∀ᶠ O : CoeffRing ℓ in atTop,
    ∃ H' : O[X], H'.map (algebraMap O (PadicAlgCl ℓ)) = H.map (intQpBar ℓ).subtype := by
  filter_upwards [H.finite_range_coeff.eventually_all.2 fun a _ ↦ eventually_mem a.2] with O hO
  rw [← mem_lifts, lifts_iff_coeff_lifts]
  exact fun k ↦ ⟨⟨H.coeff k, hO _ ⟨k, rfl⟩⟩, by simp⟩

/-- Finitely many polynomials over the integers of `ℚ̄_ℓ` with value `1` at `1` come from such
polynomials over every large coefficient ring. -/
lemma eventually_exists_map_eq_and_eval_one [Finite K] {H : K → (intQpBar ℓ)[X]}
    (hH : ∀ j : K, (H j).eval 1 = 1) :
    ∀ᶠ O : CoeffRing ℓ in atTop, ∃ H' : K → O[X],
      (∀ j : K, (H' j).map (algebraMap O (PadicAlgCl ℓ)) = (H j).map (intQpBar ℓ).subtype) ∧
      ∀ j : K, (H' j).eval 1 = 1 := by
  filter_upwards [eventually_all.2 fun j ↦ eventually_exists_map_eq (H j)] with O hO
  choose H' hH' using hO
  exact ⟨H', hH', fun j ↦ by simpa [eval_map, hH] using congrArg (eval 1) (hH' j)⟩

/-- Let `τ j` be tame generators at the places `w j` with auxiliary elements `φ j` fixing the
`ℓ ^ ν`-th roots of unity (`IsTameGeneratorFamily ν w τ φ`), and let `H(1) = 1`. The elements `φ j`
and the inverses of their conjugates (`withConjInv φ k`) act on the character `O(-e)` by scalars
that are `1` modulo `ℓ ^ ν`. Hence the values of `H` at these scalars are also `1` modulo
`ℓ ^ ν`. -/
lemma IsTameGeneratorFamily.dvd_eval_cyclotomicInv_sub_one {ν : ℕ} {w : K → FinPlace D.E}
    {τ φ : K → AbsGal D} {O : CoeffRing ℓ} (hw : IsTameGeneratorFamily ν w τ φ)
    {H : O[X]} (hH : H.eval 1 = 1) (e : ℕ) (k : K × Bool) :
    (ℓ ^ ν : ↑O) ∣ H.eval (cyclotomicInv ℓ D.E O (withConjInv φ k) ^ e) - 1 := by
  have h_dvd : (ℓ ^ ν : ↑O) ∣ cyclotomicInv ℓ D.E O (withConjInv φ k) ^ e - 1 :=
    (hw.cyclotomicInv_withConjInv_eq_one_and_dvd O k).2 e
  simpa [hH] using h_dvd.trans (sub_dvd_eval_sub _ 1 H)

lemma normLength_addVal_pow {O : CoeffRing ℓ} (m : ℕ) :
    O.normLength (addVal O (ℓ ^ m)) = m := by
  simp [normLength_addVal]

/-- The valuation at the lift. Let `v` be the `ℓ`-adic valuation of `chosenGroupOrder` and put
`sep = halfGap h`. Let `t' ≤ D.t`, `h ≤ v`, `(k + nTest) sep ≤ halfGap ^ 22 h` and
`nDetect ≤ 2 (k + nTest)`; in the application `k` counts the new places, `nTest` the test points
together with `g₀`, and `nDetect` these elements together with two tame generators for each new
place. Let the valuation of `d` in `O` be at most the sum of the losses `lossT` of the main summand
and `lossχ e` of the `t'` characters, the Selmer length `selT`, the lengths `odd e` of the odd
classes, `t'` times the cost `tame` of the tame places, and `2 t' nDetect + k + 1` times the
valuation of `ℓ ^ sep`. Let each `odd e` be at most the valuation in `O` of the positive integer
`oddClassBound D`. After scaling by `normLength`, which gives `O/ℓ` length 1, let the losses add up
to at most `loc`, `selT ≤ sel` and `tame ≤ 2 ram + 8 D.f v`. Then `ellVal d + 2 v ≤ sel + 2 t'
ram + loc + denominatorError D ℓ`. -/
lemma ellVal_add_le_of_addVal_le {O : CoeffRing ℓ} {t' h k nTest nDetect : ℕ} (ht' : t' ≤ D.t)
    (h_le : h ≤ padicValNat ℓ D.chosenGroupOrder)
    (h_points : (k + nTest) * (D.halfGap * h) ≤ D.halfGap ^ 22 * h)
    (h_detect : nDetect ≤ 2 * (k + nTest))
    {lossT selT tame : ℕ∞} {lossχ odd : Fin t' → ℕ∞} {loc sel ram : ℝ≥0∞}
    (h_loc : O.normLength lossT + ∑ e : Fin t', O.normLength (lossχ e) ≤ loc)
    (h_sel : O.normLength selT ≤ sel) (h_odd : ∀ e : Fin t', odd e ≤ addVal O (oddClassBound D))
    (h_tame : O.normLength tame ≤ 2 * ram + 8 * D.f * padicValNat ℓ D.chosenGroupOrder) {d : ↑O}
    (hd : addVal O d ≤ lossT + selT + (∑ e : Fin t', (lossχ e + odd e) +
      t' * (tame + 2 * nDetect * addVal O (ℓ ^ (D.halfGap * h))) +
      (k + 1) * addVal O (ℓ ^ (D.halfGap * h)))) :
    ellVal d.1 + 2 * padicValNat ℓ D.chosenGroupOrder ≤
      sel + 2 * t' * ram + loc + denominatorError D ℓ := by
  have h_odd_val (e : Fin t') : O.normLength (odd e) ≤ padicValNat ℓ (oddClassBound D) :=
    (normLength_mono (h_odd e)).trans_eq (by simp [ellVal_natCast (oddClassBound_ne_zero D)])
  have h_val : ellVal d.1 ≤ sel + loc + (t' * padicValNat ℓ (oddClassBound D) +
      t' * (O.normLength tame + 2 * nDetect * (D.halfGap * h : ℕ)) +
      (k + 1) * (D.halfGap * h : ℕ)) := by
    grw [← normLength_addVal d, hd, ← h_sel, ← h_loc]
    simp only [map_add, two_mul, add_mul, one_mul, normLength_natCast_mul, normLength_addVal_pow,
      sum_add_distrib]
    grw [map_sum O.normLength lossχ, map_sum O.normLength odd, h_odd_val]
    rw [sum_const, Finset.card_fin, nsmul_eq_mul]
    exact le_of_eq (by ring)
  calc
    _ ≤ sel + loc + (2 * t' * ram + denominatorError D ℓ) := by
      grw [h_val, add_assoc,
        mul_padicValNat_add_le_add_denominatorError ht' h_le h_points h_detect h_tame]
    _ = sel + 2 * t' * ram + loc + denominatorError D ℓ := by ring

/-- Models over a large coefficient ring. Fix an isomorphism `ℂ ≃ ℚ̄_ℓ` (`PadicIso ℓ`); `intQpBar ℓ`
is the ring of integers of `ℚ̄_ℓ`. Let the `u x` be conjugate self-dual, and for `x ∈ 𝓧` let `u x`
have the trace of the twisted main summand `ψ (R x)` plus the characters `O(-e)`, `e < t`. Let each
`x ∈ 𝓧` have, over all large `O`, a model `R₀`, `ψ'`, `ζ'` with a property `Good x O R₀ ψ'`; here
`IsTwistedLattice` says that `R₀` is a lattice in `R x`, that `ψ'` and `ζ'` are `ψ` and `ζ x` with
values in `O`, and that the inertial element `γ x` acts on `ψ' R₀` by the scalar `ζ'`, with `ζ' - 1`
a unit. Then over every large `O` there are such models `R₀ x`, `ψ' x`, `ζ' x`, whose twisted
lattices span all matrices, and lattices `u' x` in all `u x` that are block diagonal for `x ∈ 𝓧`:
the twisted lattice, then the characters. -/
lemma eventually_exists_twistedLattice_and_block_lattices [PadicIso ℓ] {t : ℕ}
    {u : Y → GalRep ℓ D.E n} (hu : ∀ x : Y, IsConjSelfDual t (u x))
    {ψ : AbsGal D →* PadicAlgCl ℓ} {𝓧 : Set Y}
    {J : 𝓧 → (D.E →+* ℂ) → Multiset ℤ} {R : 𝓧 → GalRep ℓ D.E r}
    (h_summand : ∀ x : 𝓧, IsMainSummandLike D t (J x) (R x))
    (h_trace : ∀ (x : 𝓧) (g : AbsGal D), (u x g).val.trace =
      ψ g * (R x g).val.trace + ∑ e ∈ range t, cyclotomicInv ℓ D.E (PadicAlgCl ℓ) g ^ e)
    {γ : 𝓧 → AbsGal D} {ζ : 𝓧 → intQpBar ℓ}
    {Good : 𝓧 → ∀ O : CoeffRing ℓ, (AbsGal D →* Matrix r r O) → (AbsGal D →* O) → Prop}
    (h_model : ∀ x : 𝓧, ∀ᶠ O : CoeffRing ℓ in atTop,
      ∃ (R₀ : AbsGal D →* Matrix r r O) (ψ' : AbsGal D →* O) (ζ' : ↑O),
        IsTwistedLattice ψ (R x) (γ x) (ζ x) R₀ ψ' ζ' ∧ Good x O R₀ ψ')
    (ϵ : Sigma (SummandCoordIndex r (t := t)) ≃ n) :
    ∀ᶠ O : CoeffRing ℓ in atTop,
      ∃ (R₀ : 𝓧 → AbsGal D →* Matrix r r O) (ψ' : 𝓧 → AbsGal D →* O) (ζ' : 𝓧 → ↑O)
        (u' : Y → AbsGal D →* Matrix n n O),
        (∀ x : 𝓧,
          IsTwistedLattice ψ (R x) (γ x) (ζ x) (R₀ x) (ψ' x) (ζ' x) ∧ Good x O (R₀ x) (ψ' x)) ∧
        (∀ x : 𝓧, Submodule.span O (.range (twistRep (.id O) (ψ' x) (R₀ x))) = ⊤) ∧
        (∀ x : Y, IsLatticeIn (u x) (u' x)) ∧
        ∀ (x : 𝓧) (g : AbsGal D), u' x g = reindex ϵ ϵ (blockDiagonal' fun i : Option (Fin t) ↦
          summandRep (twistRep (.id O) (ψ' x) (R₀ x)) i g) := by
  filter_upwards [eventually_all.2 fun x ↦ eventually_exists_isLatticeIn (hu x).continuous,
    eventually_all.2 fun x ↦ (h_summand x).eventually_span_eq_top_and_exists_eq_smul_one,
      eventually_all.2 h_model]
    with O h_lat h_span h_model
  choose R₀ ψ' ζ' h_tw h_good using h_model
  -- twisting multiplies the matrices by units, which does not change their span
  have h_span_twist (x : 𝓧) : Submodule.span O (.range (twistRep (.id O) (ψ' x) (R₀ x))) = ⊤ :=
    Basis.units_smul_span_eq_top (w := (ψ' x).toHomUnits) (h_span x _ (h_tw x).isLatticeIn).1
  obtain ⟨u', hu', hu'_block⟩ := exists_blockDiagonal_lattices (fun x ↦ (hu x).nondeg) h_lat h_trace
    (fun x ↦ (h_tw x).isLatticeIn) (fun x ↦ (h_tw x).twist_eq) h_span_twist ϵ
  exact ⟨R₀, ψ', ζ', u', fun x ↦ ⟨h_tw x, h_good x⟩, h_span_twist, hu', hu'_block⟩

/-- The determinant `det (1 - R g)` can be computed on a lattice `R₀` in `R`, where `1 - R₀ g` is
the combination of the `R₀ g' - 1` with the single coefficient `-1` at `g`. -/
lemma IsLatticeIn.det_one_sub {O : CoeffRing ℓ} {R : GalRep ℓ D.E n}
    {R₀ : AbsGal D →* Matrix n n O} (hR₀ : IsLatticeIn R R₀) (g : AbsGal D) :
    (1 - (R g).val).det = algebraMap O (PadicAlgCl ℓ)
      ((Finsupp.single g (-1 : ↑O)).linearCombination O fun g' : AbsGal D ↦ R₀ g' - 1).det := by
  obtain ⟨F, -, hF : ∀ g : AbsGal D, F (R₀ g) = R g, hF_det⟩ := hR₀.exists_algHom
  rw [Finsupp.linearCombination_single, neg_one_smul, neg_sub, ← hF, ← map_one F, ← map_sub]
  exact (hF_det _).1

/-- The losses at the lift, with divisible coefficients. Let the `w j` form a tame generator family:
`w j` is not above `ℓ`, `τ j` is the chosen tame generator at a place over `w j`, and `φ j` fixes
the `ℓ ^ ν`-th roots of unity. Over the coefficient ring `O`, let the classes
`InClass (F v) (C v) (U v)` of local lattices at the places `v` above `ℓ` contain the restrictions
of all `u x` and of the summands `summandRep T i`, which are `T` for `i = none` and `O(-e)` for
`i = some e`. Let the defects `dualDefect` of these summands have normalised sum at most
`card r * localDefectBound D ℓ`, an explicit bound (`eventually_exists_inClass_sum_dualDefect_le`).
Let the `u x` be continuous and unramified off `ℓ p₀ p₁`, `Q`, the places `w j` and their
conjugates, and `T` off `ℓ p₀ p₁`, `Q` and `Q̄`. Let `selT = crystallineSelmerLength T Q γ`, the
length of the Selmer group of `T` in `Frac(O) / O` of cocycles zero at `γ`, have normalised value at
most `sel < ∞`. Then the cocycles of `T` in `Frac(O) / O` that obey the relations among the
`u x g - 1` and vanish at the `τ j`, the inverses of their conjugates and `γ` have length at most a
number `b₀ = lossT + selT`, where the loss `lossT` (in the proof, the sum of the defects of `T`
above `ℓ`) and the colengths modulo `ℓ ^ ν` (`crystallineColength`) of the characters `O(-e)`,
`e < t`, have normalised sum at most `card r * localDefectBound D ℓ`. -/
lemma exists_length_le_loss_add_crystallineSelmerLength {ν : ℕ} {w : K → FinPlace D.E}
    {τ φ : K → AbsGal D} {O : CoeffRing ℓ} (hw : IsTameGeneratorFamily ν w τ φ)
    {t : ℕ} {Q : Finset (FinPlace D.E)} {T : AbsGal D →* Matrix r r O}
    {u : Y → AbsGal D →* Matrix n n O}
    {F : ∀ v : placesDividing D.E ℓ, Filter (decompGroup (AbsGal D) (placeOver v.val))}
    {C : ∀ v : placesDividing D.E ℓ, decompGroup (AbsGal D) (placeOver v.val) → O[X] → Prop}
    {U : placesDividing D.E ℓ → (O →ₐ[ℤ_[ℓ]] ℂ_[ℓ]) → Finset ℤ}
    (hu_cl : ∀ (v : placesDividing D.E ℓ) (x : Y), InClass (F v) (C v) (U v) (localLattice (u x) v))
    (hT_cl : ∀ (v : placesDividing D.E ℓ) (i : Option (Fin t)),
      InClass (F v) (C v) (U v) (localLattice (summandRep T i) v))
    (h_sum : ∑ i : Option (Fin t), ∑ v : placesDividing D.E ℓ, O.normLength
      (Lift.dualDefect (InClass (F v) (C v) (U v)) (localLattice (summandRep T i) v).tateDual) ≤
      card r * localDefectBound D ℓ)
    (hu_cont : ∀ x : Y, Continuous (u x))
    (hu_unr : ∀ g ∈ inertiaAbove (placesDividing D.E ℓ ∪ placesAboveM D ∪
      (.conjClosure Q ∪ (Set.range w).conjClosure))ᶜ, ∀ x : Y, u x g = 1)
    (hT_unr : ∀ g ∈ inertiaAbove (placesDividing D.E ℓ ∪ placesAboveM D ∪ .conjClosure Q)ᶜ, T g = 1)
    (γ : AbsGal D) {sel : ℝ≥0∞} (h_selT : O.normLength (crystallineSelmerLength T Q γ) ≤ sel)
    (h_fin : sel ≠ ⊤) :
    ∃ (b₀ : ℕ) (lossT : ℕ∞),
      length O (ribetCocyclesVanishingOn u T (DivisibleQuot O) (.range (withConjInv τ)) γ) ≤ b₀ ∧
      (b₀ : ℕ∞) = lossT + crystallineSelmerLength T Q γ ∧
      O.normLength lossT +
          ∑ e : Fin t, O.normLength (crystallineColength (tateTwist ℓ D.E O e) u ν) ≤
        card r * localDefectBound D ℓ := by
  -- the loss of `T`, free of the level: the sum of its defects
  let lossT : ℕ∞ := ∑ v : placesDividing D.E ℓ,
    Lift.dualDefect (InClass (F v) (C v) (U v)) (localLattice T v).tateDual
  have h_loc : O.normLength lossT + ∑ e : Fin t,
      O.normLength (crystallineColength (tateTwist ℓ D.E O e) u ν) ≤
      card r * localDefectBound D ℓ := by
    grw [← h_sum, sum_option, map_sum]
    refine add_le_add le_rfl (sum_le_sum fun e _ ↦ ?_)
    rw [← map_sum]
    exact normLength_mono
      (crystallineColength_le_sum_dualDefect hu_cl (fun v ↦ hT_cl v (some e)) ν)
  -- modulo every `ℓ ^ M` the cocycles are counted by the loss and the Selmer group
  have h_main (M : ℕ) : length O (ribetCocyclesVanishingOn u T (QuotSpan (ℓ ^ M : ↑O))
      (.range (withConjInv τ)) γ) ≤ lossT + crystallineSelmerLength T Q γ :=
    (length_ribetCocyclesVanishingOn_le hw hu_cont hu_unr hT_unr M γ).trans
      (add_le_add (crystallineColength_le_sum_dualDefect hu_cl (fun v ↦ hT_cl v none) M)
        (length_selmerCocycles_le_crystallineSelmerLength _ Q M γ))
  -- both are finite, so the bound holds with divisible coefficients
  have h_ne {a : ℕ∞} {b : ℝ≥0∞} (hb : b ≠ ⊤) (hab : O.normLength a ≤ b) : a ≠ ⊤ :=
    fun ha ↦ hb (by simpa [ha, normLength_top] using hab)
  obtain ⟨b₀, hb₀⟩ : ∃ b₀ : ℕ, b₀ = lossT + crystallineSelmerLength T Q γ :=
    ENat.ne_top_iff_exists.1 <| WithTop.add_ne_top.2
      ⟨h_ne (by finiteness) (le_self_add.trans h_loc), h_ne h_fin h_selT⟩
  have hℓ_ne : (ℓ : ↑O) ≠ 0 := ne_zero_pow one_ne_zero (NeZero.ne _)
  have hℓ_unit : ¬IsUnit (ℓ : ↑O) := fun h ↦ by
    simpa [IsDiscreteValuationRing.addVal_eq_zero_iff.2 h] using normLength_addVal_pow (O := O) 1
  exact ⟨b₀, lossT, length_ribetCocyclesVanishingOn_divisibleQuot_le u T _ γ hℓ_ne hℓ_unit
    fun M ↦ (h_main M).trans_eq hb₀.symm, hb₀, h_loc⟩

/-- Ribet's element for conjugate self-dual representations, with `t' = V.rankDiff`, the difference
`card n - card r` of the ranks of the descent pair `V`, and `r' = card r`. Let `V` with type
polynomials `c i` over the residue fields at its chosen places above `p₀`, `p₁` form a lift setting
for `ϑ` (`IsLiftSetting`), and let `ψ` be an auxiliary twist of modulus `Q` with ramification at
most `ram` (`IsAuxTwist`). Write `v = ellVal`, `N = D.chosenGroupOrder` and `halfGap = D.r ^ 8`. Let
the places `w j`, with tame generators `τ j`, elements `φ j` and exponents `0 < ty j < t'`, form a
triangle of primes for `g₀` (`IsPrimeTriangle`) up to `ℓ ^ (halfGap h)` with bound `halfGap ^ 22 h`,
where `h ≤ v(N)`. Let `u x`, `x : Y`, be finitely many conjugate self-dual representations with
Hodge–Tate jumps `J'` and level `Q`, the `w j` and their conjugates, on which inertia at the chosen
places acts through the roots of the rescaled polynomials `scaledTypePoly V c i` and `1`
(`IsRepOfType`), and inertia above `Q` and `Q̄` satisfies `(g - ψ g) (g - 1) = 0`. For `x ∈ 𝓧` let
`u x` have the trace of `ψ (R x)` plus the characters `O(-e)`, `e < t'`. Here `R x` is a main
summand, and `ψ (R x)` has a lattice on which `γ x` acts by the scalar `ζ x`. Let `S` be an algebra
of families, indexed by `Y`, of polynomials in variables `X j`, and let the `S`-module `𝒥` contain
`ℓ ^ ν` times the traces and the traces of the relations `τ j - 1 - X j (φ j - 1) H j (φ j)`
(`IsTraceIdeal`), with `H j (1) = 1`. At one `π ∈ 𝓧` let the Selmer group of `ψ (R π)` with
divisible coefficients have length at most `sel < ∞`. Then the determinants `det (1 - u x g)` lie in
`S` and vanish on `𝓧`, and there is one `f ∈ S`, the Ribet element, that multiplies each of them
into `𝒥`, has on `𝓧` no monomial properly dividing `∏ X j`, and whose coefficient `d` of `∏ X j` at
`π` satisfies `v(d) + 2 v(N) ≤ sel + 2 t' ram + r' loc + e_ℓ`, with the explicit bounds
`loc = localDefectBound D ℓ` and `e_ℓ = denominatorError D ℓ`. -/
lemma ribet_columns {ν : ℕ} {w : K → FinPlace D.E} {τ φ : K → AbsGal D}
    [PadicIso ℓ] {V : DescentPair D.E r n}
    {c : ∀ i : V.ChosenIndex, (ResField (V.chosenPlace i))[X]} {ϑ : D.Twist}
    (hc : IsLiftSetting V c ϑ)
    {ψ : AbsGal D →* PadicAlgCl ℓ} {Q : Finset (FinPlace D.E)} {ram : ℝ≥0∞}
    (h_twist : IsAuxTwist (badPlaces D ℓ) Q ψ ram)
    -- the triangle of new places
    [Fintype K] [LinearOrder K] {ty : K →o {e : Fin V.rankDiff // 0 < e.val}} {g₀ : AbsGal D}
    {h : ℕ} (h_le : h ≤ padicValNat ℓ D.chosenGroupOrder)
    (h_tri : IsPrimeTriangle ν w τ φ g₀ V.rankDiff ty (D.halfGap * h) (D.halfGap ^ 22 * h))
    -- the representations of a type
    {u : Y → GalRep ℓ D.E n} {J' : (D.E →+* ℂ) → Multiset ℤ}
    (h_type : ∀ x : Y, IsRepOfType V V.rankDiff J'
      (fun i : V.ChosenIndex ↦ scaledTypePoly V c i * (X - 1) ^ V.rankDiff)
      (.conjClosure Q ∪ (Set.range w).conjClosure) (u x))
    (h_quad : ∀ x : Y, ∀ g ∈ inertiaAbove (Set.conjClosure Q),
      ((u x g).val - ψ g • 1) * ((u x g).val - 1) = 0)
    -- the lifts and their main summands
    {𝓧 : Set Y} {J : 𝓧 → (D.E →+* ℂ) → Multiset ℤ} {R : 𝓧 → GalRep ℓ D.E r}
    (h_summand : ∀ x : 𝓧, IsMainSummandLike D V.rankDiff (J x) (R x))
    (h_trace : ∀ (x : 𝓧) (g : AbsGal D), (u x g).val.trace =
      ψ g * (R x g).val.trace + ∑ e ∈ range V.rankDiff, cyclotomicInv ℓ D.E (PadicAlgCl ℓ) g ^ e)
    {γ : 𝓧 → AbsGal D} {ζ : 𝓧 → intQpBar ℓ}
    (h_lat : ∀ x : 𝓧, HasTwistedLattice ψ (R x) (γ x) (ζ x))
    -- the tied relations
    {S : Subalgebra (intQpBar ℓ) (Y → MvPolynomial K (PadicAlgCl ℓ))}
    {𝒥 : Submodule S (Y → MvPolynomial K (PadicAlgCl ℓ))} {H : K → (intQpBar ℓ)[X]}
    (h𝒥 : IsTraceIdeal 𝒥 (fun (x : Y) (g : AbsGal D) ↦ (u x g).val) (ℓ ^ ν) τ φ id H)
    (hH : ∀ j : K, (H j).eval 1 = 1)
    -- the lift, and the Selmer group of its twisted main summand with divisible coefficients
    (π : 𝓧) {sel : ℝ≥0∞} (h_sel : HasDivisibleSelmerLengthLe ψ (R π) Q (γ π) (ζ π) sel)
    (h_fin : sel ≠ ⊤) :
    ∃ d : PadicAlgCl ℓ,
      IsCommonRibetElement 𝒥 (fun (g : AbsGal D) (x : Y) ↦ (1 - (u x g).val).det) π d ∧
      ellVal d + 2 * padicValNat ℓ D.chosenGroupOrder ≤
        sel + 2 * V.rankDiff * ram + card r * localDefectBound D ℓ + denominatorError D ℓ := by
  classical
  -- Choose a ring `O` that carries all data, check the hypotheses of Ribet's lemma
  -- `exists_isCommonRibetElement_addVal_le` over `O`, and add up the losses in its bound for `d`.
  obtain ⟨-, hψ : IsFromU1 (placesDividing D.E ℓ) Q ψ, -⟩ := id h_twist
  have : NeZero V.rankDiff := .of_pos hc.odd.2.pos
  have ϵ : Sigma (SummandCoordIndex r (t := V.rankDiff)) ≃ n :=
    equivOfCardEq (by simp! [V.rank_lt.le])
  have h_dual (x : Y) : IsConjSelfDual V.rankDiff (u x) := (h_type x).toIsConjSelfDual
  -- the models: at `π` the one of `h_sel`, with its Selmer bound; elsewhere those of `h_lat`
  have h_lat' (x : 𝓧) : ∀ᶠ O : CoeffRing ℓ in atTop,
      ∃ (u : AbsGal D →* Matrix r r O) (ψ' : AbsGal D →* O) (ζ' : ↑O),
        IsTwistedLattice ψ (R x) (γ x) (ζ x) u ψ' ζ' ∧
        (x = π → O.normLength (crystallineSelmerLength (twistRep (.id O) ψ' u) Q (γ x)) ≤ sel) := by
    obtain rfl | hx := eq_or_ne x π
    · exact Eventually.mono h_sel fun _ ⟨u, ψ', ζ', h_tw, h_le⟩ ↦ ⟨u, ψ', ζ', h_tw, fun _ ↦ h_le⟩
    · exact Eventually.mono (h_lat x) fun _ ⟨u, ψ', ζ', h_tw⟩ ↦ ⟨u, ψ', ζ', h_tw, hx.elim⟩
  obtain ⟨O, h_def, h_odd, ⟨H', hH', hH'_one⟩, R₀, ψ', ζ', u', h_model, hT_span, hu', hu'_block⟩ :=
    (eventually_exists_inClass_sum_dualDefect_le hc (h_summand π) h_type ϵ π |>.and <|
      eventually_length_shaOdd_le D ℓ |>.and <|
      eventually_exists_map_eq_and_eval_one hH |>.and <|
      eventually_exists_twistedLattice_and_block_lattices h_dual h_summand h_trace h_lat' ϵ).exists
  choose h_tw h_selT using h_model
  -- the main summands `T x` of the lattices `u' x`, `x ∈ 𝓧`
  let T (x : 𝓧) : AbsGal D →* Matrix r r O := twistRep (.id O) (ψ' x) (R₀ x)
  have hu'_cont (x : Y) : Continuous (u' x) := (hu' x).continuous (h_type x).continuous
  have hu'_unr (g : AbsGal D) (hg : g ∈ inertiaAbove (placesDividing D.E ℓ ∪ placesAboveM D ∪
      (.conjClosure Q ∪ (Set.range w).conjClosure))ᶜ) (x : Y) : u' x g = 1 :=
    (hu' x).eq_one ((h_type x).eq_one_of_mem_inertiaAbove g hg)
  -- the classes of local lattices above `ℓ`, and the losses and the Selmer group at the lift
  have hT_loc : ∀ v ∈ placesDividing D.E ℓ, ∀ g ∈ decompGroup (AbsGal D) (placeOver v),
      T π g = R₀ π g := fun v hv g hg ↦ (h_tw π).twistRep_apply_eq_of_eq_one
    (hψ.eq_one_of_mem_decompGroup hv v.isPlaceOver_placeOver hg)
  obtain ⟨F, C, U, hu_cl, hT_cl, h_sum⟩ :=
    h_def (T π) (R₀ π) u' (hu'_block π) hu' (h_tw π).isLatticeIn hT_loc
  replace h_selT : O.normLength (crystallineSelmerLength (T π) Q (γ π)) ≤ sel := h_selT π rfl
  have hw : IsTameGeneratorFamily ν w τ φ := h_tri.isTameGeneratorFamily
  obtain ⟨b₀, lossT, hb₀, hb₀_eq, h_loc⟩ :=
    exists_length_le_loss_add_crystallineSelmerLength hw hu_cl hT_cl h_sum hu'_cont hu'_unr
      ((h_tw π).twistRep_eq_one_of_mem_inertiaAbove hψ (h_summand π)) (γ π) h_selT h_fin
  -- the tame places, and the test points `s`, which detect cocycles together with `g₀`
  obtain ⟨W, _, q, δ, o, hq, hq_cover, hδ, ho⟩ :=
    exists_tame_relations hc h_twist h_type h_quad hu' (h_tw π).twist_eq
  obtain ⟨s, -, hs_card : (card K + (#s + 1)) * (D.halfGap * h) ≤ D.halfGap ^ 22 * h, hs, -⟩ :=
    h_tri.exists_test_points
  have h_detect (e : ℕ) : IsDetectedBy (selmerModule (tateTwist ℓ D.E O e) (placesDividing D.E ℓ) ∅
      (QuotSpan (ℓ ^ ν : ↑O))) (insert g₀ s) :=
    fun z hz h_zero ↦ hs O e z hz (h_zero g₀ (by simp)) fun g hg ↦ h_zero g (by simp [hg])
  let s' : Finset (AbsGal D) := insert g₀ s ∪ image (withConjInv τ) univ
  have hs'_card : #s' ≤ 2 * (card K + (#s + 1)) := by
    grw [card_union_le, card_insert_le, card_image_le, card_univ, card_prod, card_bool]
    omega
  -- the characters `χ e`, which `g₀` separates up to `ℓ ^ (halfGap h)`
  let χ (e : Fin V.rankDiff) : AbsGal D →* O := cyclotomicInv ℓ D.E O ^ e.1
  have h_sep (e : Fin V.rankDiff) : ∏ e' ∈ {e}ᶜ, (χ e g₀ - χ e' g₀) ∣ ℓ ^ (D.halfGap * h) := by
    simpa [χ, cyclotomicInv] using map_dvd (algebraMap ℤ_[ℓ] O) (h_tri.prod_dvd e)
  let ϵ' : r ⊕ Fin V.rankDiff ≃ n := (summandCoordIndexEquiv r V.rankDiff).trans ϵ
  have h_block (x : 𝓧) (g : AbsGal D) :
      u' x g = reindex ϵ' ϵ' (fromBlocks (T x g) 0 0 (diagonal fun e ↦ χ e g)) := by
    simp [ϵ', χ, T, hu'_block x, blockDiagonal'_summandRep]
  have hχγ (x : 𝓧) (e : Fin V.rankDiff) : χ e (γ x) = 1 := by
    simp [χ, cyclotomicInv, (h_tw x).cyclotomicChar_eq_one]
  have hχδ (k : W × Bool) (e : Fin V.rankDiff) : χ e (withConjInv δ k) = 1 := by
    simp [χ, (hq.cyclotomicInv_withConjInv_eq_one_and_dvd O k).1]
  -- the trace ideal over `O` for the doubled families, whose factors are `1` modulo `ℓ ^ ν`
  have h𝒥' : IsTraceIdeal (S := restrictToCoeffRing S O) 𝒥 (fun x : Y ↦ u' x) (ℓ ^ ν)
      (withConjInv τ) (withConjInv φ) Prod.fst H' := h𝒥.of_isLatticeIn hw h_dual hu' hH'
  have hH'_dvd (e : Fin V.rankDiff) (k : K × Bool) :
      (ℓ ^ ν : ↑O) ∣ (H' k.1).eval (χ e (withConjInv φ k)) - 1 :=
    hw.dvd_eval_cyclotomicInv_sub_one (hH'_one k.1) e k
  -- the cost of the character `χ e`
  let cost (e : Fin V.rankDiff) : ℕ∞ :=
    crystallineColength (tateTwist ℓ D.E O e) u' ν + length O (shaOdd ℓ D.E O e ν)
  have h_cost (e : Fin V.rankDiff) (Z : Submodule O (AbsGal D → Unit → QuotSpan (ℓ ^ ν : ↑O)))
      (hZ : ∀ z ∈ Z, IsCharacterCocycle u' (χ e) (withConjInv δ) (γ π) g₀ z) :
      HasTriangleCost Z τ (fun j ↦ (conjGal (τ j))⁻¹) φ (fun j ↦ (conjGal (φ j))⁻¹)
        {j : K | (ty j).val = e} (ℓ ^ (D.halfGap * h)) (cost e) ∧ IsDetectedBy Z s' :=
    hasTriangleCost_of_isCharacterCocycle h_tri hu'_cont hq hq_cover hu'_unr e
      (h_tw π).mem_inertiaAbove (h_detect e) hZ
  obtain ⟨d, ⟨h_mem, h_zero, f, hf_mem, hf_low, hf_top⟩, hd_le⟩ :=
    exists_isCommonRibetElement_addVal_le u' 𝒥 (S := restrictToCoeffRing S O) ϵ' π T
      (hξ₀ := by simp [χ]) (hu_block := h_block) (hρ_span := hT_span π)
      (hργ := fun x ↦ (h_tw x).apply_eq_smul) (hy_unit := fun x ↦ (h_tw x).isUnit_sub_one)
      (hξγ := hχγ) (hp := NeZero.ne _) (h𝒥 := h𝒥') (hε := hH'_dvd) (a := g₀) (hC_dvd := h_sep)
      (ty := ⟨fun j ↦ ty j, ty.mono⟩) (hb₀ := hb₀) (hξδ := hχδ) (hδ_poly := hδ) (hb := h_cost)
  rw [hb₀_eq] at hd_le
  have ht' : V.rankDiff ≤ D.t := (h_summand π).t_le
  refine ⟨d, ?_, ellVal_add_le_of_addVal_le ht' h_le hs_card hs'_card h_loc h_selT
    (fun e ↦ h_odd e (e.2.trans_le ht') ν) ho hd_le⟩
  -- `det (1 - u x g)` is the determinant of the combination `∑ ω g' (u' x g' - 1)`, where the
  -- coefficient function `ω` is `-1` at `g` and `0` elsewhere
  simp only [(hu' _).det_one_sub]
  exact ⟨fun g ↦ h_mem _, fun g x ↦ h_zero _ x, f, fun g ↦ hf_mem _, hf_low, hf_top⟩

end RibetColumns

end New.Selmer
