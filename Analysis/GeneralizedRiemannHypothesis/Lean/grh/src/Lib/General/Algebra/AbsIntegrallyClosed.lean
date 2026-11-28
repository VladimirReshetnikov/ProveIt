import Lib.Base

/-!
# Absolutely integrally closed rings and their stability properties; Frobenius powers

* `New.Variety.frobPow`: the ring endomorphism `x ↦ x ^ p ^ f`, for a prime `p` with `p = 0` in
  the ring.
* `New.Variety.IsAbsIntegrallyClosed`: every monic polynomial of positive degree has a root (the
  ring need not be a domain).
* The property passes to subrings that are integrally closed in the ring
  (`New.Variety.IsAbsIntegrallyClosed.of_isIntegrallyClosedIn`), to quotients
  (`New.Variety.IsAbsIntegrallyClosed.of_surjective`) and to localisations
  (`New.Variety.IsAbsIntegrallyClosed.of_isLocalization`). For a field it means algebraically
  closed: algebraically closed fields have it by an instance, and
  `New.Variety.IsAbsIntegrallyClosed.isAlgClosed` gives the converse.
* `New.Variety.IsAbsIntegrallyClosed.exists_root_map_eq`,
  `New.Variety.IsAbsIntegrallyClosed.mem_range_of_isIntegralElem`: for `f : A →+* B` from an
  absolutely integrally closed ring into a domain, roots in `B` of monic polynomials over `A` lift
  to roots in `A`, so integral elements lie in the image.
* `New.exists_val_coeff_le_val_eval`: finitely many multivariable polynomials over an algebraically
  closed valued field attain the sizes of their largest coefficients at one integral point.
-/

namespace New.Variety

open Polynomial IsLocalization

/-- The ring endomorphism `x ↦ x ^ p ^ f` of a commutative ring `B` in which the prime `p` is
zero. -/
@[simps! -fullyApplied]
def frobPow {p : ℕ} {B : Type*} [Fact (Nat.Prime p)] [CommRing B] (h : (p : B) = 0) (f : ℕ) :
    B →+* B :=
  -- The map is additive because the mixed terms of the binomial expansion are multiples of `p`.
  RingHom.mk' (powMonoidHom (p ^ f)) (by simp [add_pow_prime_pow_eq Fact.out, h])

/-- `A` is absolutely integrally closed: every monic polynomial over `A` of positive degree has a
root in `A`. -/
class IsAbsIntegrallyClosed (A : Type*) [CommRing A] : Prop where
  /-- Every monic polynomial over `A` of positive degree has a root in `A`. -/
  exists_root (P : A[X]) : Monic P → 0 < P.natDegree → ∃ x : A, P.IsRoot x

variable {A B K : Type*} [CommRing A] [CommRing B] [Field K]

/-- An algebraically closed field is absolutely integrally closed. -/
instance [IsAlgClosed K] : IsAbsIntegrallyClosed K where
  exists_root P _ h_deg := IsAlgClosed.exists_root P (natDegree_pos_iff_degree_pos.1 h_deg).ne'

namespace IsAbsIntegrallyClosed

/-- A field that is absolutely integrally closed is algebraically closed. -/
lemma isAlgClosed (hK : IsAbsIntegrallyClosed K) : IsAlgClosed K :=
  .of_exists_root K fun P hP h_irr ↦ hK.exists_root P hP h_irr.natDegree_pos

/-- If `A` is absolutely integrally closed and `f : B →+* A` is a ring map, then every monic
polynomial over `B` of positive degree has a root in `A` along `f`. -/
lemma exists_eval₂_eq_zero [hA : IsAbsIntegrallyClosed A] (f : B →+* A) {P : B[X]} (hP : Monic P)
    (h_deg : 0 < P.natDegree) : ∃ x : A, P.eval₂ f x = 0 := by
  nontriviality A
  simpa [eval_map] using hA.exists_root (P.map f) (hP.map f) (by rwa [hP.natDegree_map f])

variable (A) in
/-- If `A` is absolutely integrally closed and `B` is integrally closed in the `B`-algebra `A`
(in particular `B → A` is injective), then `B` is absolutely integrally closed. -/
lemma of_isIntegrallyClosedIn [hA : IsAbsIntegrallyClosed A] [Algebra B A]
    [h_closed : IsIntegrallyClosedIn B A] : IsAbsIntegrallyClosed B := by
  refine ⟨fun P hP h_deg ↦ ?_⟩
  obtain ⟨h_inj, h_range⟩ := isIntegrallyClosedIn_iff.1 h_closed
  obtain ⟨x, hx⟩ := hA.exists_eval₂_eq_zero (algebraMap B A) hP h_deg
  -- The root `x` is integral over `B`, so it comes from `B`; and `B → A` is injective.
  obtain ⟨b, rfl⟩ : ∃ b : B, algebraMap B A b = x := h_range ⟨P, hP, hx⟩
  exact ⟨b, h_inj (by simpa using hx)⟩

/-- Let `A` be absolutely integrally closed and `f : A →+* B` a ring map. A monic polynomial over
`B` of positive degree whose coefficients lie in the image of `f` has a root in `B`. -/
lemma exists_root_of_coeffs_subset_range [hA : IsAbsIntegrallyClosed A] {f : A →+* B} {P : B[X]}
    (h_coeffs : (P.coeffs : Set B) ⊆ Set.range f) (hP : P.Monic) (h_deg : 0 < P.natDegree) :
    ∃ x : B, P.IsRoot x := by
  -- `P` is the image of a monic `Q` of the same degree, and `f` maps a root of `Q` to one of `P`.
  obtain ⟨Q, rfl, hQ_deg, hQ⟩ :=
    lifts_and_natDegree_eq_and_monic ((lifts_iff_coeffs_subset_range P).2 h_coeffs) hP
  obtain ⟨x, hx⟩ := hA.exists_root Q hQ (by lia)
  exact ⟨f x, hx.map⟩

/-- In an absolutely integrally closed ring, every element has an `n`-th root for `n ≠ 0`. -/
lemma exists_pow_eq [hA : IsAbsIntegrallyClosed A] (n : ℕ) [hn : NeZero n] (a : A) :
    ∃ x : A, x ^ n = a := by
  nontriviality A
  simpa [sub_eq_zero] using
    hA.exists_root (X ^ n - C a) (monic_X_pow_sub_C a hn.ne) (by simpa using hn.pos)

/-- In a nonzero absolutely integrally closed ring `A`, for `n > 1` and any `c`, `b` in `A`, the
equation `x ^ n - c * x = b` has a solution `x` in `A`. -/
lemma exists_pow_sub_mul_eq [hA : IsAbsIntegrallyClosed A] [Nontrivial A] (n : ℕ)
    [hn : Fact (1 < n)] (c b : A) : ∃ x : A, x ^ n - c * x = b := by
  -- The solutions are the roots of a monic polynomial of degree `n > 1`.
  let P : A[X] := X ^ n - (C c * X + C b)
  have hP : P.IsMonicOfDegree n :=
    (isMonicOfDegree_X_pow A n).sub (natDegree_linear_le.trans_lt hn.out)
  have h_deg : 0 < P.natDegree := (zero_lt_one.trans hn.out).trans_eq hP.natDegree_eq.symm
  simpa [P, ← sub_sub, sub_eq_zero] using hA.exists_root P hP.monic h_deg

/-- If `A` is absolutely integrally closed and `f : A →+* B` is a surjective ring map, then `B` is
absolutely integrally closed. -/
lemma of_surjective [hA : IsAbsIntegrallyClosed A] {f : A →+* B} (hf : Function.Surjective f) :
    IsAbsIntegrallyClosed B :=
  ⟨fun _ ↦ hA.exists_root_of_coeffs_subset_range fun b _ ↦ hf b⟩

/-- A localization `B` of an absolutely integrally closed ring `A` at a submonoid is absolutely
integrally closed. -/
lemma of_isLocalization [hA : IsAbsIntegrallyClosed A] (S : Submonoid A) [Algebra A B]
    [IsLocalization S B] : IsAbsIntegrallyClosed B := by
  -- Scaling the roots of `P` by a common denominator `d` of its coefficients gives a monic
  -- polynomial with coefficients from `A`; it has a root `x`, and `x / d` is a root of `P`.
  refine ⟨fun P hP h_deg ↦ ?_⟩
  let d : B := algebraMap A B (commonDenom S P.support P.coeff)
  have hd : IsUnit d := map_units B _
  have h_mem : P.scaleRoots d ∈ lifts (algebraMap A B) :=
    scaleRoots_commonDenom_mem_lifts S P ⟨1, by simp [hP.leadingCoeff]⟩
  obtain ⟨x, hx⟩ : ∃ x : B, (P.scaleRoots d).IsRoot x := hA.exists_root_of_coeffs_subset_range
    ((lifts_iff_coeffs_subset_range _).1 h_mem) ((monic_scaleRoots_iff d).2 hP) (by simpa)
  obtain ⟨y, rfl⟩ : d ∣ x := hd.dvd
  have h_eval : d ^ P.natDegree * P.eval y = 0 := by rwa [← scaleRoots_eval_mul]
  exact ⟨y, (hd.pow _).mul_right_eq_zero.1 h_eval⟩

/-! ### Maps to a domain -/

/-- Let `A` be absolutely integrally closed, `f : A →+* B` a ring map to a domain, and `P` a monic
polynomial over `A`. Every root `x` in `B` of the image of `P` is `f a` for some root `a` of `P`
in `A`. -/
lemma exists_root_map_eq [hA : IsAbsIntegrallyClosed A] {f : A →+* B} [IsDomain B] {x : B}
    {P : A[X]} (hP : Monic P) (hx : P.eval₂ f x = 0) : ∃ a : A, P.IsRoot a ∧ f a = x := by
  -- Induction on the degree: split off a linear factor `X - C a`; as `B` is a domain, `x` is
  -- `f a` or a root of the image of the cofactor.
  induction h_deg : P.natDegree generalizing P with
  | zero => simp [hP.natDegree_eq_zero.1 h_deg] at hx
  | succ n ih =>
    have : Nontrivial A := f.domain_nontrivial
    obtain ⟨a, ha⟩ := hA.exists_root P hP (by lia)
    obtain ⟨Q, rfl⟩ : X - C a ∣ P := dvd_iff_isRoot.2 ha
    have hQ : Q.Monic := (monic_X_sub_C a).of_mul_monic_left hP
    rw [(monic_X_sub_C a).natDegree_mul hQ, natDegree_X_sub_C] at h_deg
    obtain rfl | hx_root : x = f a ∨ Q.eval₂ f x = 0 := by simpa [sub_eq_zero] using hx
    · exact ⟨a, ha, rfl⟩
    · obtain ⟨b, hb, rfl⟩ := ih hQ hx_root (by lia)
      exact ⟨b, root_mul_left_of_isRoot _ hb, rfl⟩

/-- If `A` is absolutely integrally closed and `f : A →+* B` is a ring map to a domain, then every
element of `B` that is integral along `f` lies in the image of `f`. -/
lemma mem_range_of_isIntegralElem [hA : IsAbsIntegrallyClosed A] {f : A →+* B} [IsDomain B] {x : B}
    (hx : f.IsIntegralElem x) : x ∈ f.range := by
  obtain ⟨P, hP, hPx⟩ := hx
  obtain ⟨a, -, rfl⟩ := hA.exists_root_map_eq hP hPx
  exact ⟨a, rfl⟩

end IsAbsIntegrallyClosed

end New.Variety

/-!
## A general integral point

Each polynomial is a constant times a polynomial with nonzero reduction. As the residue field is
infinite, there is a point at which none of the reductions vanishes. This is the Gauss norm
property on the unit polydisc, as in Bosch, Güntzer and Remmert, *Non-Archimedean Analysis*.
-/

section IntegralityPrinciple

open Finset IsLocalRing MvPolynomial New.Variety.IsAbsIntegrallyClosed

/-- Over an algebraically closed valued field there is an integral point at which each of finitely
many polynomials takes a value at least as large as all its coefficients. -/
lemma New.exists_val_coeff_le_val_eval {K σ : Type*} {n : ℕ} [Field K] [IsAlgClosed K]
    (v : Valuation K NNReal) (f : Fin n → MvPolynomial σ K) :
    ∃ y : σ → v.valuationSubring,
      ∀ (i : Fin n) (m : σ →₀ ℕ),
        v ((f i).coeff m) ≤ v (eval (algebraMap v.valuationSubring K ∘ y) (f i)) := by
  classical
  -- Write `f i = c i • g i` with `g i` over `V` of nonzero reduction. The residue field is
  -- algebraically closed, hence infinite, so at some `y` no reduction vanishes: each `g i` takes
  -- a unit value at `y`.
  set V : ValuationSubring K := v.valuationSubring
  have h_scale (q : MvPolynomial σ K) :
      ∃ (c : K) (g : MvPolynomial σ V), map (residue V) g ≠ 0 ∧ q = c • g.map (algebraMap V K) := by
    -- A coefficient `q.coeff k` of largest valuation divides the others, with quotients `w m`.
    obtain ⟨k, hk⟩ : ∃ k : σ →₀ ℕ, ∀ m ∈ q.support,
        V.valuation (q.coeff m) ≤ V.valuation (q.coeff k) :=
      Set.exists_upper_bound_image q.support (V.valuation ∘ q.coeff) (Set.toFinite _)
    have h_dvd : ∀ m ∈ q.support, ∃ w : V, (w : K) * q.coeff k = q.coeff m :=
      fun m hm ↦ (V.valuation_le_iff _ _).1 (hk m hm)
    choose! w hw using h_dvd
    let g : MvPolynomial σ V := monomial k 1 + ∑ d ∈ q.support.erase k, monomial d (w d)
    have h_coeff (d : σ →₀ ℕ) :
        g.coeff d = if k = d then 1 else if d ∈ q.support then w d else 0 := by
      obtain rfl | hkd := eq_or_ne k d <;> simp [g, coeff_monomial, eq_comm, *]
    refine ⟨q.coeff k, g, ne_of_apply_ne (·.coeff k) (by simp [coeff_map, h_coeff]), ?_⟩
    ext d
    rw [coeff_smul, coeff_map, h_coeff]
    split_ifs with hkd hd
    · simp [hkd]
    · simp [← hw d hd, mul_comm]
    · simpa using hd
  -- Now `f i = c i • g i`, and the reduction of each `g i` is not zero.
  choose c g hg hfg using fun i : Fin n ↦ h_scale (f i)
  have : IsAlgClosed (ResidueField V) :=
    ((of_isIntegrallyClosedIn K).of_surjective residue_surjective).isAlgClosed
  -- Over an infinite field a nonzero polynomial has a nonzero value.
  obtain ⟨y₀, hy₀⟩ :
      ∃ y₀ : σ → ResidueField V, eval y₀ (∏ i : Fin n, map (residue V) (g i)) ≠ eval y₀ 0 :=
    not_forall.1 fun h_eq ↦ prod_ne_zero_iff.2 (fun i _ ↦ hg i) (MvPolynomial.funext h_eq)
  obtain ⟨y, rfl⟩ : ∃ y : σ → V, residue V ∘ y = y₀ := residue_surjective.comp_left y₀
  have h_unit (i : Fin n) : IsUnit (eval y (g i)) := by
    rw [map_prod, map_zero, prod_ne_zero_iff] at hy₀
    rw [← residue_ne_zero_iff_isUnit]
    simpa [eval_map, ← eval₂_comp] using hy₀ i (mem_univ i)
  refine ⟨y, fun i m ↦ ?_⟩
  -- The factor `c i` is common, and the unit `eval y (g i)` divides every coefficient of `g i`.
  have h_le : v (algebraMap V K ((g i).coeff m)) ≤ v (algebraMap V K (eval y (g i))) :=
    (Valuation.integer.integers v).le_of_dvd (h_unit i).dvd
  grw [hfg i, coeff_smul, coeff_map, smul_eval, eval_map, ← eval₂_comp, smul_eq_mul, map_mul,
    map_mul, h_le]

end IntegralityPrinciple
