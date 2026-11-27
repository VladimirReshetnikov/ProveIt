import Lib.LocalGL.Green.LabelCharacters

/-!
# Shintani lifting of Green's characters along extensions of prime degree

For an extension `k'/k` of finite fields of prime degree, the file shows that Green's characters of
`GL_m` lift from `k` to `k'` by true characters. `New.Hall k` is the ring of complex functions on
similarity classes of square matrices over `k` of all sizes, with parabolic induction as product,
and μ is the inverse of the constant function 1 in it. For a label `c` (monic, squarefree,
`c(0) ≠ 0`), `New.labelChar T c` is the product Ξ_c of Green's functions `New.greenTau T P` over the
irreducible factors `P` of `c`. `thetaChar T q x` is a character of `K` attached to `x` and a field
size `q`; for `x` in `k`, `thetaChar T |k| x` at the norm from `k'` is `thetaChar T |k'| x`.
`New.Lift Z F F'` says that in each rank `m` one `Z`-combination of characters of
`GL_m(k') ⋊ Gal(k'/k)` restricts to `F'` on `GL_m(k')` and is `F` of the norm on the cosets of the
`σ` with fixed field `k` (`New.DescendsTo Φ F` for `F` over `k`; for `F'` over `k'`,
`DescendsTo Φ F'` means `Φ ∘ inl = F'.evalGL`).

## Main definitions and results

* `New.sum_evalGL_prod_eq_zero_iff`: the element `∑ conj (χ g) g` of a parabolically induced
  character `χ` kills a vector `v` if and only if the corresponding sum over the block upper
  triangular matrices kills all translates of `v`.
* `New.exists_isChar_descendsTo_labelChar`: let `P` be irreducible of degree `r = [L : k]`, a label
  (`IsLabel r P`), with a root `x`. Then one character of `GL_r(k') ⋊ Gal(k'/k)` descends both to
  the cuspidal function of `θ_x` times `μ` and to `(-1) ^ r Ξ_P μ` over `k'`. This is used to lift
  `Ξ_P` from `k` to `k'`.
* `New.lift_detChar`: the lift of `χ ∘ det`.
* `New.DescendsTo.card_mul_classInner`: the inner product of two lifts in terms of the inner
  products over `k'` and over `k`.
* `New.shintani_lift_labelChar`: the lift by true characters for any label (`New.IsLabel`: monic,
  squarefree, non-zero constant term).

Notions from other files:
* `New.Hall.evalGL`: for `F : Hall k` and `g : GL n k`, the value of `F` at the similarity class of
  the endomorphism of `n → k` given by `g`.
* `New.blockHom b a`: the homomorphism sending a block upper triangular invertible matrix (for the
  level function `b`) to its diagonal block of level `a`.
* `New.classInner f h`: the inner product of complex functions on a finite set, the average of
  `conj (f g) * h g`; `New.Hall.rankInner n F H` is the same over `GL_n(k)` for functions on
  classes, `F.mulMoebius` is `F` times `μ`, and `New.finMean f` is the average of `f` over a finite
  type.

## Relation to the literature

Known result: Shintani lifting of characters of GL_n(F_q) to an extension field, with the lift
identified for Green's characters. Here the degree is prime, and only Green's characters with
squarefree labels and characters of the determinant are treated. For these, one character of the
semidirect product with the Galois group is the lifted character on GL_n(k'), and on the cosets of
the σ with fixed field k it is the original character at the norm; no bijection of characters is
given. Source: T. Shintani, J. Math. Soc. Japan 28 (1976) 396-414; A. Silberger and E.-W. Zink, J.
Algebra 319 (2008) 4147-4176, Thm 5.1; for tensor induction, Gluck-Isaacs, Illinois J. Math. 27
(1983).

See also `Lib.LocalGL.Green.TauFunctions`.
-/

/-!
## Frobenius reciprocity for parabolically induced characters

A criterion for the element `∑ conj (χ g) g` of a parabolically induced character `χ` to kill a
vector, in terms of the sum over the block upper triangular matrices.
-/

namespace New

open MonoidAlgebra Representation Finset Fintype Matrix

attribute [local instance low] Fintype.ofFinite

variable {k n V ι : Type*} [Field k] [Fintype n] [DecidableEq n] [AddCommGroup V] [Module ℂ V]

/-- Let each `F a` be a character in every size (`hF`: the lift from `k` to itself makes each
`(F a).evalGL` an `ℕ`-combination of characters), and let the operators `A g` act on `v` like a
representation of `GL n k` (`hA_mul`). Let `χ` be the induction product of the `F a`, each cut down
to the size of the block of level `a`. Then `∑ g, conj (χ g) • A g v = 0` if and only if, for all
`y`, the sum of `conj (∏ a, F a (p_a)) • A (p * y) v` over the block upper triangular `p` with
diagonal blocks `p_a` vanishes. -/
lemma sum_evalGL_prod_eq_zero_iff [Finite k]
    [LinearOrder ι] (b : n → ι) [Fintype ι] {F : ι → Hall k}
    (hF : ∀ a : ι, Lift ℕ (F a) (F a)) (A : GL n k → Module.End ℂ V) {v : V}
    (hA_mul : ∀ g x : GL n k, A g (A x v) = A (g * x) v) :
    ∑ᶠ g : GL n k,
        star ((∏ a : ι, (F a).rankPart (Fintype.card {i // b i = a})).evalGL g) • A g v = 0 ↔
      ∀ y : GL n k,
        ∑ᶠ p : parabolic b, star (∏ a : ι, (F a).evalGL (blockHom b a p)) • A (p * y) v = 0 := by
  -- Let `ρ` be the representation of `GL n k` on `ℂ[GL n k] / ker L`, `L g = A g v`. Each side says
  -- that a character is orthogonal to that of `ρ`, and Frobenius reciprocity matches the two.
  let L : MonoidAlgebra ℂ (GL n k) →ₗ[ℂ] V :=
    Finsupp.linearCombination ℂ (fun g ↦ A g v) ∘ₗ (coeffLinearEquiv ℂ).toLinearMap
  have h_ker (g : GL n k) : L.ker ≤ L.ker.comap (leftRegular ℂ (GL n k) g) := by
    have h_comm : A g ∘ₗ L = L ∘ₗ leftRegular ℂ (GL n k) g := by aesop
    grw [← LinearMap.ker_comp, ← h_comm, ← L.ker_le_ker_comp (A g)]
  let ρ : Representation ℂ (GL n k) (MonoidAlgebra ℂ (GL n k) ⧸ L.ker) :=
    (leftRegular ℂ (GL n k)).quotient L.ker h_ker
  set χ : GL n k → ℂ := (∏ a, (F a).rankPart (card {i // b i = a})).evalGL
  let κ : parabolic b → ℂ := ∏ a, (F a).evalGL ∘ blockHom b a
  -- `Lift ℕ` is closed under `rankPart` and products, and `Lift ℕ F F` makes `F.evalGL` an
  -- `ℕ`-combination of characters.
  have hχ : IsChar χ := isChar_of_mem_virtualChars (Lift.evalGL_mem_virtualChars
    (univ.prod_hom_rel .one fun a _ _ ↦ .mul (.rankPart_of_hasCommonLift (hF a _))))
  have hκ : IsChar κ := isChar_of_mem_virtualChars
    (prod_mem fun a _ ↦ comp_mem_virtualChars (hF a).evalGL_mem_virtualChars (blockHom b a))
  have h_frob : classInner χ ρ.character = classInner κ (character (ρ.domRestrict (parabolic b))) :=
    classInner_evalGL_prod b F (fun i ↦ mem_univ (b i)) _ ρ.char_conj
  -- `∑ conj (χ g) g` acts as zero in a representation iff `χ` is orthogonal to its character.
  have h_kill : ρ.asAlgebraHom (groupAlgElem (starRingEnd ℂ ∘ χ)) = 0 ↔
      asAlgebraHom (ρ.domRestrict (parabolic b)) (groupAlgElem (starRingEnd ℂ ∘ κ)) = 0 := by
    rw [hχ.asAlgebraHom_groupAlgElem_eq_zero_iff, hκ.asAlgebraHom_groupAlgElem_eq_zero_iff, h_frob]
  -- An element of the group algebra acts as zero in `ρ` iff it kills the class of every `y`.
  have h_iff : (∀ y, ∑ᶠ g, star (χ g) • A (g * y) v = 0) ↔
      ∀ y, ∑ᶠ p : parabolic b, star (∏ a, (F a).evalGL (blockHom b a p)) • A (p * y) v = 0 := by
    simpa [L, ρ, κ, Submodule.linearMap_qext_iff, MonoidAlgebra.lhom_ext'_iff, Subtype.ext_iff,
      LinearMap.ext_ring_iff, ← L.quotKerEquivRange.map_eq_zero_iff, asAlgebraHom_eq_sum,
      finsum_eq_sum_of_fintype]
      using h_kill
  refine Iff.trans ⟨fun h_one y ↦ ?_, fun h_all ↦ ?_⟩ h_iff
  · -- As `χ` is a class function, the case `y = 1` gives all `y`: apply `A y` and conjugate by
    -- `y`.
    have h_apply : A y (∑ᶠ g : GL n k, star (χ g) • A g v) = A y 0 := congrArg (A y) h_one
    rw [finsum_eq_sum_of_fintype, ← (MulAut.conj y).sum_comp]
    simpa [hA_mul, hχ.isClassFunction, finsum_eq_sum_of_fintype] using h_apply
  · -- the case `y = 1` of the right side is the left side
    simpa using h_all 1

@[simp]
lemma evalGL_detChar (χ : MulChar k ℂ) (g : GL n k) : (detChar χ).evalGL g = χ g.val.det := by
  simp [Hall.evalGL, detChar, det_eq_sign_charpoly_coeff]

end New

/-! ## A Galois-twisted character descending to Green's functions -/

section TorusLift

namespace New

open Polynomial Module Finset Hall ComplexConjugate LinearMap Algebra TensorProduct
  FiniteField Function Fin IntermediateField IsGalois Units minpoly Nat

attribute [local instance low] Fintype.ofFinite

variable {k L K : Type*} {r : ℕ}
  (k' : Type*) [Field k] [Field k'] [Algebra k k'] [Finite k] [Finite k'] [Field L]
  [Algebra k L] [Field K] [Algebra k K] [Algebra k' K] [IsScalarTower k k' K]
  (T : MulChar K ℂ) [IsFaithfulMulChar K T] {P : k[X]} {x : K}

omit [IsScalarTower k k' K] in
/-- Let irreducible polynomials `S` over `k'` and `P` over `k` have a common root `z`. Then
`deg S ∣ n ↔ deg P ∣ [k' : k] * n`, as both sides say that `z ^ |k'| ^ n = z`. -/
lemma natDegree_dvd_iff_of_common_root (hP : Irreducible P) {S : k'[X]} (hS : Irreducible S)
    {z : K} (hzS : Polynomial.aeval z S = 0) (hzP : Polynomial.aeval z P = 0) (n : ℕ) :
    S.natDegree ∣ n ↔ P.natDegree ∣ finrank k k' * n := by
  rw [← root_pow_card_pow_eq_self_iff hS hzS, ← root_pow_card_pow_eq_self_iff hP hzP, Nat.pow_mul,
    ← natCard_eq_pow_finrank (K := k) (V := k')]

/-- Let `P` be irreducible over `k` with root `x`, and let the label `c` (monic, squarefree, nonzero
constant term) of degree `n` over `k'` divide `P`. For some `a j` (`j < b`): (a) each root of `c` is
`k'`-conjugate to some `x ^ |k| ^ a j` with `a j < deg P`; (b) `b * [k'(x) : k'] = n`; (c) for each
class function `B` over `k'`, `(-1) ^ n` times the `GL_n(k')`-mean of
`conj (labelChar T c) * mulMoebius B` equals the mean over units `u` of `k'(x) ^ b` of `B` at
multiplication by `u` times `∏ j, conj` of the `thetaChar` of `x ^ |k| ^ a j` at `u j`. Here
`labelChar` is the product of Green's `τ_Q` over the factors `Q` of `c`, and
`mulMoebius B = B · μ`. -/
lemma exists_rankInner_labelChar_eq_finMean (hP : Irreducible P) (hx : Polynomial.aeval x P = 0)
    (hx_int : IsIntegral k' x) [FiniteDimensional k' k'⟮x⟯] [Finite k'⟮x⟯] {n : ℕ} {c : k'[X]}
    (hc : IsLabel n c) (h_dvd : c ∣ P.map (algebraMap k k')) :
    ∃ b : ℕ, ∃ a : Fin b → ℕ,
      -- (a) the roots
      (∀ z : K, Polynomial.aeval z c = 0 → ∃ j : Fin b, ∃ v < finrank k' k'⟮x⟯,
        a j < P.natDegree ∧ z ^ Nat.card k' ^ v = x ^ Nat.card k ^ a j) ∧
      -- (b) the degree
      b * finrank k' k'⟮x⟯ = n ∧
      -- (c) the pairing
      ∀ B : Hall k',
        (-1) ^ n * rankInner n (labelChar T c) (mulMoebius B) =
          finMean fun u : Fin b → k'⟮x⟯ˣ ↦
            (∏ j : Fin b, conj (thetaChar T (Nat.card k'⟮x⟯) (x ^ Nat.card k ^ a j) (u j))) *
              B (simClassOf (LinearMap.mulLeft k' fun j : Fin b ↦ (u j).val)) := by
  -- Induction on the number of irreducible factors of `c`.
  revert h_dvd
  refine hc.induction_irreducible_mul K (fun _ ↦ ?_)
    fun S m c z hS_monic hS hS_zero hzS ih h_dvd ↦ ?_
  · simp [eq_simClassOf_zero_of_dim_eq_zero, finMean, univ_eq_empty, rankInner,
    finsum_eq_sum_of_fintype,
      mulMoebius, finrank_pi_fintype]
  -- The new factor `S` has a root `x ^ |k| ^ e`, and its degree is `[k'(x) : k']`.
  have hzP : Polynomial.aeval z P = 0 := by simpa [hzS] using map_dvd (aeval z) h_dvd
  have h_dvd_iff (d : ℕ) : S.natDegree ∣ d ↔ finrank k' k'⟮x⟯ ∣ d := by
    rw [adjoin.finrank hx_int, natDegree_dvd_iff_of_common_root k' hP hS hzS hzP,
      natDegree_dvd_iff_of_common_root k' hP (irreducible hx_int) (minpoly.aeval k' x) hx]
  have degree_eq : S.natDegree = finrank k' k'⟮x⟯ := Nat.dvd_right_iff_eq.mp h_dvd_iff
  obtain ⟨e, he, rfl⟩ : ∃ e < P.natDegree, x ^ Nat.card k ^ e = z :=
    exists_pow_card_pow_eq_of_root hP hx hzP
  -- the statement for `c`, by induction
  obtain ⟨b, a, roots, rfl, h_avg⟩ := ih (dvd_of_mul_left_dvd h_dvd)
  refine ⟨b + 1, cons e a, ?_, by grind, fun B ↦ ?_⟩
  · -- A root of `S * c` is a root of `S`, and then conjugate to `x ^ |k| ^ e`, or a root of `c`.
    suffices h_roots : ∀ z : K, Polynomial.aeval z S = 0 ∨ Polynomial.aeval z c = 0 →
        (∃ v < finrank k' k'⟮x⟯, e < P.natDegree ∧ z ^ Nat.card k' ^ v = x ^ Nat.card k ^ e) ∨
          ∃ i : Fin b, ∃ v < finrank k' k'⟮x⟯,
            a i < P.natDegree ∧ z ^ Nat.card k' ^ v = x ^ Nat.card k ^ a i by
      simpa [exists_fin_succ] using h_roots
    grind [exists_pow_card_pow_eq_of_root]
  -- Removing the factor `greenTau T S` replaces `B` by `B'`: up to sign, `B' o` is the mean over
  -- `z` in `k'(x)ˣ` of `conj (θ z)` times `B` at the direct sum of `o` and multiplication by `z`.
  let θ : MulChar K ℂ := thetaChar T (.card k'⟮x⟯) (x ^ .card k ^ e)
  let B' : Hall k' := fun o ↦ (-1) ^ finrank k' k'⟮x⟯ * finMean fun z : k'⟮x⟯ˣ ↦
    conj (θ (k'⟮x⟯.val z.val)) *
      B (simClassOf ((simClassOf (mulLeft k' z.val)).out.2.prodMap o.out.2))
  have h_skew : skew (finrank k' k'⟮x⟯) (greenTau T S) (mulMoebius B) = mulMoebius B' := by
    -- `greenTau T S` is Green's function of `θ` up to sign, and
    -- `rankInner_greenCuspidal_mulMoebius` computes its pairing.
    funext o
    simp only [mulMoebius, B']
    rw [← rankInner_greenCuspidal_mulMoebius θ k'⟮x⟯.val fun o' ↦
      B (simClassOf (o'.out.2.prodMap o.out.2))]
    simp [θ, mul_comm (finMean _), greenTau_eq hS hS_zero hzS, degree_eq, skew, rankInner,
      ← card_eq_pow_finrank, mulMoebius, ← finMean_const_mul]
    ac_rfl
  -- Multiplication by `cons z u` is the direct sum of the multiplications by `z` and by `u`.
  have block (z : k'⟮x⟯ˣ) (u : Fin b → k'⟮x⟯ˣ) :
      simClassOf ((simClassOf (mulLeft k' z.val)).out.2.prodMap
          (simClassOf (mulLeft k' fun j : Fin b ↦ (u j).val)).out.2) =
        simClassOf (mulLeft k' fun j : Fin (b + 1) ↦
          ((Fin.cons z u : Fin (b + 1) → k'⟮x⟯ˣ) j).val) := by
    obtain ⟨f, hf⟩ := exists_equiv_simClassOf_out (mulLeft k' z.val)
    obtain ⟨g, hg⟩ := exists_equiv_simClassOf_out (mulLeft k' fun j ↦ (u j).val)
    refine simClassOf_eq_of_equiv (f.prodCongr g ≪≫ₗ consLinearEquiv k' fun _ ↦ k'⟮x⟯) fun v ↦ ?_
    simp [hf, hg, funext_iff, forall_fin_succ]
  -- Split off the factor `greenTau T S` with its sign, and apply the case of `c` to `B'`.
  trans (-1 : ℂ) ^ finrank k' k'⟮x⟯ * finMean fun u : Fin b → k'⟮x⟯ˣ ↦
      (∏ j : Fin b, conj (thetaChar T (Nat.card k'⟮x⟯) (x ^ Nat.card k ^ a j) (u j))) *
        B' (simClassOf (LinearMap.mulLeft k' fun j : Fin b ↦ (u j).val))
  · rw [pow_add, map_mul, labelChar_eq_greenTau T hS hS_monic,
      rankInner_mul_eq_rankInner_skew greenTau_eq_zero_of_dim_ne, degree_eq, h_skew, mul_assoc,
      h_avg]
  -- Both sides are double sums, over `z` and over the other coordinates `u`; compare the terms.
  rw [finMean_equiv (consEquiv _) fun _ ↦ rfl]
  simp only [finMean_prod]
  simp [finMean, prod_univ_succ, mul_sum, sum_div, sum_comm (α := _ˣ), B', finsum_eq_sum_of_fintype]
  congr! 2 with z _ u
  rw [block z u]
  -- The sign in `B'` cancels the one split off by `pow_add`.
  simp [θ, field, ← pow_mul]

/-- Let `x` be a root of the irreducible `P` over `k`, and let `a j < deg P` (`j < g`) be exponents
such that every root of `P` over `k'` is conjugate over `k'` to some `x ^ |k| ^ a j`. If
`g * [k'(x) : k'] = deg P` and `[k' : k] * [k'(x) : k'] = deg P * s`, then the map
`(j, i) ↦ F ^ (a j + deg P * i)`, for `F` the Frobenius of `k'` over `k`, is a bijection from
`Fin g × Fin s` onto `Gal(k'/k)`. -/
private lemma bijective_frobeniusAlgEquivOfAlgebraic_pow_of_roots (hP : Irreducible P)
    (hx : Polynomial.aeval x P = 0) [FiniteDimensional k' k'⟮x⟯] {g s : ℕ} {a : Fin g → ℕ}
    (roots : ∀ z : K, Polynomial.aeval z (P.map (algebraMap k k')) = 0 →
      ∃ j : Fin g, ∃ v < finrank k' k'⟮x⟯,
        a j < P.natDegree ∧ z ^ Nat.card k' ^ v = x ^ Nat.card k ^ a j)
    (hg : g * finrank k' k'⟮x⟯ = P.natDegree)
    (hs : finrank k k' * finrank k' k'⟮x⟯ = P.natDegree * s) :
    Bijective fun i : Fin g × Fin s ↦
      frobeniusAlgEquivOfAlgebraic k k' ^ (a i.1 + P.natDegree * i.2) := by
  -- Every element `F ^ u` of `Gal(k'/k)` is hit; both sides have `g * s = [k' : k]` elements.
  set F : k' ≃ₐ[k] k' := frobeniusAlgEquivOfAlgebraic k k'
  have h_surj : Surjective fun i : Fin g × Fin s ↦ F ^ (a i.1 + P.natDegree * i.2) := by
    refine (bijective_frobeniusAlgEquivOfAlgebraic_pow k k').2.forall.mpr fun u ↦ ?_
    -- The root `x ^ |k| ^ u` of `P` is conjugate over `k'` to some `x ^ |k| ^ a j`.
    have h_root : Polynomial.aeval (x ^ Nat.card k ^ (u : ℕ)) (P.map (algebraMap k k')) = 0 := by
      simpa [hx, coe_frobeniusAlgHom] using P.aeval_algHom_apply (frobeniusAlgHom k K ^ (u : ℕ)) x
    obtain ⟨j, v, hv, a_lt, h_conj⟩ : ∃ j : Fin g, ∃ v < finrank k' k'⟮x⟯, a j < P.natDegree ∧
        (x ^ Nat.card k ^ (u : ℕ)) ^ Nat.card k' ^ v = x ^ Nat.card k ^ a j :=
      roots _ h_root
    have h_mod : (u + finrank k k' * v) % P.natDegree = a j := by
      rw [natCard_eq_pow_finrank (K := k) (V := k'), ← pow_mul, ← pow_mul, ← pow_add,
        root_pow_card_pow_eq_iff_modEq hP hx] at h_conj
      exact mod_eq_of_modEq h_conj a_lt
    have h_bound : u + finrank k k' * v < P.natDegree * s := by nlinarith [u.isLt]
    have h_exp : a j + P.natDegree * ((u + finrank k k' * v) / P.natDegree) =
        u + finrank k k' * v := by rw [← h_mod, mod_add_div]
    refine ⟨(j, ⟨_, Nat.div_lt_of_lt_mul h_bound⟩), ?_⟩
    ext
    simp [h_exp, F, pow_add, pow_mul, coe_frobeniusAlgEquivOfAlgebraic,
      ← card_eq_pow_finrank, pow_card_pow]
  refine h_surj.bijective_of_nat_card_le ?_
  rw [IsGalois.card_aut_eq_finrank, Nat.card_prod, Nat.card_fin, Nat.card_fin]
  nlinarith [hP.natDegree_pos]

/-- Let `χ m : k' ⊗ L → k'(x)` be `k'`-algebra maps such that `χ 0` after the power
`F ^ (a j + deg P * i)` of the Frobenius `F` of `k'` over `k` is `χ (a j)` followed by the same
power of the Frobenius of `k'(x)` (`χ_frob`), and let these powers run once through `Gal(k'/k)`
(`frob_bij`). Then for a unit `t` of `k' ⊗ L`, `conj θ_x` at `χ 0` of the norm `∏ τ, τ t` is the
product over `j` of `conj θ_(x ^ |k| ^ a j)` at `χ (a j) t`. -/
private lemma conj_thetaChar_prod_eq_prod_conj_thetaChar (hP : Irreducible P)
    (hP_coeff : P.coeff 0 ≠ 0) (hx : Polynomial.aeval x P = 0) [FiniteDimensional k' k'⟮x⟯]
    [Finite k'⟮x⟯] {g s : ℕ} {a : Fin g → ℕ}
    (hs : finrank k k' * finrank k' k'⟮x⟯ = P.natDegree * s)
    (χ : ℕ → k' ⊗[k] L →ₐ[k'] k'⟮x⟯)
    (frob_bij : Bijective fun i : Fin g × Fin s ↦
      frobeniusAlgEquivOfAlgebraic k k' ^ (a i.1 + P.natDegree * i.2))
    (χ_frob : ∀ (i : Fin g × Fin s) (t : k' ⊗[k] L),
      χ 0 (map (frobeniusAlgEquivOfAlgebraic k k' ^ (a i.1 + P.natDegree * i.2)).toAlgHom
          (.id k L) t) =
        (frobeniusAlgEquivOfAlgebraic k k'⟮x⟯ ^ (a i.1 + P.natDegree * i.2)) (χ (a i.1) t))
    (t : (k' ⊗[k] L)ˣ) :
    conj (thetaChar T (.card k ^ P.natDegree) x
        (k'⟮x⟯.val.comp (χ 0) (∏ τ : Gal(k'/k), map τ.toAlgHom (.id k L) (t : k' ⊗[k] L)))) =
      ∏ j : Fin g, conj (thetaChar T (.card k'⟮x⟯) (x ^ .card k ^ a j) (χ (a j) t)) := by
  -- Group the norm by `j`. Each group is the `|k| ^ a j`-th power of the norm of `χ (a j) t` from
  -- `k'(x)` to its subfield with `|k| ^ deg P` elements, to which `thetaChar_eq_apply_norm_pow`
  -- applies.
  obtain ⟨x_pow, two_le⟩ := root_pow_card_pow_pred_eq_one hP hP_coeff hx
  have card_eq : Nat.card k'⟮x⟯ = (Nat.card k ^ P.natDegree) ^ s := by
    rw [← pow_mul, ← hs, finrank_mul_finrank, ← natCard_eq_pow_finrank]
  simp_rw [← frob_bij.prod_comp, map_prod, AlgHom.comp_apply, χ_frob, Fintype.prod_prod_type]
  congr! 1 with j
  -- the value `χ (a j) t`, seen in `K`, in the form of `thetaChar_eq_apply_norm_pow`
  have h_coe : ((χ (a j) (t : k' ⊗[k] L) : k'⟮x⟯) : K) =
      algebraMap k'⟮x⟯ K (t.map (χ (a j) : k' ⊗[k] L →* k'⟮x⟯)).val := rfl
  rw [h_coe, thetaChar_eq_apply_norm_pow T two_le x_pow Finite.one_lt_card card_eq rfl
    (algebraMap_pow_card_pred_eq_one _)]
  simp [prod_range, prod_pow, pow_add, pow_mul, coe_frobeniusAlgEquivOfAlgebraic,
    ← prod_pow_eq_pow_sum]

/-- Let `P` over `k` be irreducible and a label of degree `r` (`IsLabel r P`: monic, squarefree,
nonzero constant term), with a root `x` in `K`, and let `[L : k] = r`. There is a character `Φ` of
the semidirect product `GL_r(k') ⋊ Gal(k'/k)` that descends (`DescendsTo`) to `μ` times the
cuspidal function `greenCuspidal k θ_x`, where `θ_x = thetaChar T (|k| ^ r) x`. The same `Φ`
descends to `(-1) ^ r Ξ_P μ`, with `Ξ_P = labelChar T P` formed over `k'`. -/
lemma exists_isChar_descendsTo_labelChar [Finite L] (hP : Irreducible P) (hP_label : IsLabel r P)
    (hx : Polynomial.aeval x P = 0) (hL_rank : finrank k L = r) :
    ∃ Φ : GalSemidirect k k' (Fin r) → ℂ,
      -- (a) a character
      IsChar Φ ∧
      -- (b) that lifts the function over `k` induced from the torus `Lˣ`
      DescendsTo Φ (greenCuspidal k (thetaChar T (Nat.card k ^ r) x)).mulMoebius ∧
      -- (c) and on `GL r k'` is, up to sign, the function with label `P` times `μ`
      DescendsTo Φ ((-1 : ℂ) ^ r • (labelChar T (P.map (algebraMap k k'))).mulMoebius) := by
  -- `exists_rankInner_labelChar_eq_finMean` gives a mean over the units of `k'(x) ^ g`. We identify
  -- `k' ⊗ L` with `k'(x) ^ g`, check that `thetaChar` of the norm `∏ τ, τ t` is the product of the
  -- characters, and conclude by `exists_torus_induced_descendsTo`.
  obtain ⟨hP_monic, -, rfl, hP_coeff⟩ :
    P.Monic ∧ Squarefree P ∧ P.natDegree = r ∧ P.coeff 0 ≠ 0 := id hP_label
  have hx_int : IsIntegral k' x := .tower_top ⟨P, hP_monic, hx⟩
  have := adjoin.finiteDimensional hx_int
  have : Finite k'⟮x⟯ := finite_of_finite k'
  have : Finite (k' ⊗[k] L) := finite_of_finite k'
  obtain ⟨g, a, roots, hg, h_avg⟩ := exists_rankInner_labelChar_eq_finMean k' T hP hx hx_int
    (hP_label.map k') dvd_rfl
  -- `s = [k'(x) : L]`, for an embedding `ψ` of `L` in `k'(x)`.
  obtain ⟨s, hs⟩ : P.natDegree ∣ finrank k k' * finrank k' k'⟮x⟯ := by
    rw [adjoin.finrank hx_int,
      ← natDegree_dvd_iff_of_common_root k' hP (irreducible hx_int) (minpoly.aeval k' x) hx]
  obtain ⟨ψ⟩ : Nonempty (L →ₐ[k] k'⟮x⟯) :=
    nonempty_algHom_of_finrank_dvd ⟨s, by rw [hL_rank, ← hs, finrank_mul_finrank]⟩
  let F : k' ≃ₐ[k] k' := frobeniusAlgEquivOfAlgebraic k k'
  let F_x : k'⟮x⟯ ≃ₐ[k] k'⟮x⟯ := frobeniusAlgEquivOfAlgebraic k k'⟮x⟯
  let n (i : Fin g × Fin s) : ℕ := a i.1 + P.natDegree * i.2
  -- On `L`, `χ m` is `ψ` followed by the inverse of `z ↦ z ^ |k| ^ m`.
  let χ (m : ℕ) : k' ⊗[k] L →ₐ[k'] k'⟮x⟯ := AlgHom.liftEquiv k k' L _ (.comp ↑(F_x ^ m)⁻¹ ψ)
  -- On `L` the map `z ↦ z ^ |k| ^ deg P` is the identity, so `n i` and `a i.1` act alike there.
  have χ_frob (i : Fin g × Fin s) (t : k' ⊗[k] L) :
      χ 0 (Algebra.TensorProduct.map (F ^ n i).toAlgHom (.id k L) t) =
        (F_x ^ n i) (χ (a i.1) t) := by
    induction t with
    | add t u ht hu => simp [ht, hu]
    | tmul c l =>
      simp [χ, n, F, F_x, Algebra.smul_def, mul_pow, ← map_pow, ← hL_rank,
        coe_frobeniusAlgEquivOfAlgebraic, pow_add, pow_mul, ← card_eq_pow_finrank, pow_card_pow,
        AlgEquiv.eq_symm_apply]
  -- Every element of `Gal(k'/k)` is `F ^ n i` for exactly one `i`.
  have frob_bij : Bijective (F ^ n ·) :=
    bijective_frobeniusAlgEquivOfAlgebraic_pow_of_roots k' hP hx roots hg hs
  -- The coordinates of `t` in the trace-dual basis are traces, which the `χ (a j) t` determine.
  let e := equivFinsuppOfBasisLeft (N := L) (finBasis k k').traceDual
  have coord (t : k' ⊗[k] L) (i : Fin (finrank k k')) :
      ψ (e t i) = ∑ τ : Gal(k'/k), χ 0 (map τ.toAlgHom (.id k L) (t * finBasis k k' i ⊗ₜ 1)) := by
    induction t with
    | add t u ht hu => simp [ht, hu, e, add_mul, sum_add_distrib]
    | tmul c l => simp [e, χ, ← sum_smul, -map_mul, ← trace_eq_sum_automorphisms]
  let π : k' ⊗[k] L →ₐ[k'] (Fin g → k'⟮x⟯) := AlgHom.pi fun j ↦ χ (a j)
  have π_inj : Injective π.toLinearMap := by
    refine fun t u htu ↦ e.injective (Finsupp.ext fun i ↦ ψ.injective ?_)
    simp_all [π, ← frob_bij.sum_comp, funext_iff]
  let E : k' ⊗[k] L ≃ₗ[k'] (Fin g → k'⟮x⟯) :=
    linearEquivOfInjective _ π_inj (by simp [*, finrank_pi_fintype])
  obtain ⟨Ψ, hΨ_char, hΨ_down, hΨ_up⟩ :=
    exists_torus_induced_descendsTo k k' (thetaChar T (.card k ^ P.natDegree) x) hL_rank
      (k'⟮x⟯.val.comp (χ 0))
  -- `E` respects multiplication, so it keeps the similarity classes of the multiplications.
  have h_cls (t : (k' ⊗[k] L)ˣ) :
      simClassOf (mulLeft k' (t : k' ⊗[k] L)) = simClassOf (mulLeft k' (π t)) :=
    simClassOf_eq_of_equiv E (map_mul π _)
  refine ⟨Ψ, hΨ_char, hΨ_down, hΨ_up _ fun B ↦ ?_⟩
  calc
    _ = (-1) ^ P.natDegree *
        rankInner P.natDegree (labelChar T (P.map (algebraMap k k'))) (mulMoebius B) := by
      simp [rankInner, mulMoebius, ← finMean_const_mul]
      ac_rfl
    _ = finMean fun u : Fin g → k'⟮x⟯ˣ ↦
          (∏ j : Fin g, conj (thetaChar T (Nat.card k'⟮x⟯) (x ^ Nat.card k ^ a j) (u j))) *
            B (simClassOf (mulLeft k' fun j : Fin g ↦ (u j).val)) := h_avg B
    _ = finMean fun t : (k' ⊗[k] L)ˣ ↦
          conj (thetaChar T (.card k ^ P.natDegree) x
            (k'⟮x⟯.val.comp (χ 0) (∏ τ : Gal(k'/k), map τ.toAlgHom (.id k L) (t : k' ⊗[k] L)))) *
          B (simClassOf (mulLeft k' (t : k' ⊗[k] L))) := by
      -- Change variables by `E`: the weights agree by `conj_thetaChar_prod_eq_prod_conj_thetaChar`.
      refine finMean_equiv ((mapEquiv ⟨E.toEquiv, map_mul π⟩).trans .piUnits) fun t ↦ ?_
      simp only [h_cls t,
        conj_thetaChar_prod_eq_prod_conj_thetaChar k' T hP hP_coeff hx hs χ frob_bij χ_frob t]
      rfl

end New

end TorusLift

namespace New

open Module Polynomial Finset Matrix Hall FiniteField Finite SemidirectProduct Subgroup Function
  Subalgebra IsScalarTower

variable {k k' n K : Type*} {r : ℕ} [Field k] [Field k'] [Algebra k k'] [Finite k] [Finite k']
  [Fintype n] [DecidableEq n] [Field K] [Algebra k K] [Algebra k' K] (hp : (finrank k k').Prime)
  (T : MulChar K ℂ) [IsFaithfulMulChar K T] {c : k[X]}

/-- Let `k'` be an algebra over itself (through some automorphism) whose Galois group is trivial
(`h_gal`), and let the structure map raise the roots of every polynomial to the power `a`
(`h_roots`). Then for every `η : K → ℂ` the Brauer lift of `y ↦ η (y ^ a)` lifts to the Brauer
lift of `η`: over `ℂ` every class function is a combination of characters. -/
private lemma lift_brauerLift_pow_of_forall_eq_one [Algebra k' k']
    (h_gal : ∀ τ : Gal(k'/k'), τ = 1) {a : ℕ}
    (h_roots : ∀ P : k'[X], (P.map (algebraMap k' k')).aroots K =
      (P.aroots K).map fun y : K ↦ y ^ a)
    (η : K → ℂ) : Lift ℂ (brauerLift k' fun y : K ↦ η (y ^ a)) (brauerLift k' η) := by
  intro m
  have h_span : (brauerLift k' η).evalGL ∈ virtualChars ℂ (GL (Fin m) k') := by
    -- part (b) of `isIrreducibleChar_and_mem_virtualChars_and_exists_mul`: every inner product with
    -- a character is a complex number
    obtain ⟨-, h_crit, -⟩ := isIrreducibleChar_and_mem_virtualChars_and_exists_mul ℂ
      (isClassFunction_evalGL (F := brauerLift k' η) (n := Fin m))
    exact h_crit fun χ _ ↦ ⟨_, rfl⟩
  refine hasCommonLift_of_gal_trivial h_gal h_span fun g ↦ ?_
  simp [Hall.evalGL, charpoly_map, h_roots]

/-- In the situation of `lift_brauerLift_pow_of_forall_eq_one`, let the structure map of `k'` over
itself also keep irreducible polynomials irreducible (`h_irr`). Then for every label `c` over `k'`
the function `labelChar T` of the image of `c` lifts to `labelChar T c`, by induction on the
irreducible factors of `c`. -/
private lemma lift_labelChar_map_of_forall_eq_one [Algebra k' k']
    (h_gal : ∀ τ : Gal(k'/k'), τ = 1) {a : ℕ} [NeZero a]
    (h_roots : ∀ P : k'[X], (P.map (algebraMap k' k')).aroots K =
      (P.aroots K).map fun y : K ↦ y ^ a)
    (h_irr : ∀ P : k'[X], Irreducible P → Irreducible (P.map (algebraMap k' k')))
    {c : k'[X]} (hc : IsLabel r c) :
    Lift ℂ (labelChar T (c.map (algebraMap k' k'))) (labelChar T c) := by
  refine hc.induction_irreducible_mul (p := fun _ c ↦
      Lift ℂ (labelChar T (c.map (algebraMap k' k'))) (labelChar T c)) K (by simp)
    fun P _ c x hP_monic hP hP_coeff hx h_lift_c ↦ ?_
  -- An irreducible factor: as `x` is a root of `P`, `x ^ a` is a root of the image of `P`.
  have hPσ : Irreducible (P.map (algebraMap k' k')) := h_irr P hP
  have hx_pow : aeval (x ^ a) (P.map (algebraMap k' k')) = 0 := by
    refine (mem_aroots.mp (?_ : x ^ a ∈ (P.map (algebraMap k' k')).aroots K)).right
    rw [h_roots]
    exact Multiset.mem_map_of_mem _ (mem_aroots.mpr ⟨hP.ne_zero, hx⟩)
  -- Write both sides through `greenCuspidal`: passing from `θ_x` to `θ_(x ^ a)` composes with
  -- the `a`-th power map (`rankPart_greenCuspidal_pow`), so the lift of Brauer lifts applies.
  have h_lift_P : Lift ℂ (labelChar T (P.map (algebraMap k' k'))) (labelChar T P) := by
    rw [labelChar_eq_greenTau T hP hP_monic, labelChar_eq_greenTau T hPσ (hP_monic.map _),
      greenTau_eq hP hP_coeff hx, greenTau_eq hPσ (by simpa using hP_coeff) hx_pow, natDegree_map,
      rankPart_greenCuspidal_pow hP hP_coeff hx]
    exact (lift_brauerLift_pow_of_forall_eq_one T h_gal h_roots _).rankPart_mulMoebius_mul_constOne
  simpa using h_lift_P.mul h_lift_c

/-- Let `k'` be an algebra over itself with surjective structure map `s` (`h_surj`), and let `F`
lift to `F'` over it. Then `F'` at `s(g)` is `F` at `g`: a common lift `Φ` is `F'` on `GL n k'`
and descends to `F` on the coset of `1`, whose fixed field is `k'`. -/
private lemma evalGL_map_eq_of_lift [Algebra k' k'] {F F' : Hall k'} (h_lift : Lift ℂ F F')
    (h_surj : Function.Surjective (algebraMap k' k')) (g : GL n k') :
    F'.evalGL (g.map (algebraMap k' k')) = F.evalGL g := by
  obtain ⟨Φ, -, hΦ_twist, hΦ⟩ := h_lift.hasCommonLift n
  have h_fixed : HasFixedField k' (1 : Gal(k'/k')) :=
    Set.ext fun y ↦ iff_of_true (h_surj y) rfl
  calc F'.evalGL (g.map (algebraMap k' k'))
    _ = Φ (inl (g.map (algebraMap k' k'))) := by rw [← DescendsTo.iff_comp_inl_eq_evalGL.mp hΦ]
    _ = F.evalGL g := hΦ_twist 1 h_fixed (inl (g.map (algebraMap k' k'))) g rfl (by simp)

/-- Galois equivariance of Green's functions. Let `T` be a faithful character (`K` algebraically
closed, `T : K → ℂ` injective), and let `Ξ_c = labelChar T c`, the parabolic-induction product of
the `τ_P` over the irreducible factors `P` of `c`. Then for `σ ∈ Gal(k'/k)`, every label `c` of
degree `r` over `k'` (monic, squarefree, of degree `r`, with nonzero constant term) and every
`g ∈ GL_n(k')`, we have Ξ_c(σ(g)) = Ξ_{σ(c)}(g). -/
lemma evalGL_labelChar_map (σ : Gal(k'/k)) {c : k'[X]} (hc : IsLabel r c) (g : GL n k') :
    (labelChar T c).evalGL (g.map σ) = (labelChar T (c.map σ)).evalGL g := by
  -- View `k'` as an extension of itself through `σ`; its Galois group is trivial. For this
  -- extension `labelChar T (c.map σ)` lifts to `labelChar T c`, by induction on the irreducible
  -- factors of `c`. Evaluating the common combination of characters at `g.map σ` gives the claim.
  let twist : Algebra k' k' := σ.toRingEquiv.toRingHom.toAlgebra
  have h_gal (τ : Gal(k'/k')) : τ = 1 := by
    ext y
    obtain ⟨z, rfl⟩ := σ.surjective y
    exact τ.commutes z
  -- `σ` is the power map `y ↦ y ^ a`, so it raises the roots of a polynomial to the power `a`.
  obtain ⟨i, hσ_pow⟩ : ∃ i : ℕ, ∀ y : k', σ y = y ^ Nat.card k ^ i :=
    exists_forall_apply_eq_pow k _ k' σ
  set a : ℕ := Nat.card k ^ i
  have h_roots (P : k'[X]) :
      (P.map (algebraMap k' k')).aroots K = (P.aroots K).map fun y ↦ y ^ a :=
    aroots_map_frobenius_pow _ hσ_pow P
  -- `σ` keeps irreducible polynomials irreducible; the lemmas above give the lift.
  have h_irr (P : k'[X]) (hP : Irreducible P) : Irreducible (P.map (algebraMap k' k')) :=
    hP.map (mapEquiv σ.toRingEquiv)
  have h_lift : Lift ℂ (labelChar T (c.map (algebraMap k' k'))) (labelChar T c) :=
    lift_labelChar_map_of_forall_eq_one T h_gal h_roots h_irr hc
  -- Evaluate the common lift at `g.map σ`; the structure map of the twisted algebra is `σ`.
  have h_alg : algebraMap k' k' = (σ : k' →+* k') := RingHom.ext fun _ ↦ rfl
  simpa [h_alg] using evalGL_map_eq_of_lift h_lift σ.surjective g

/-- Let `T` be an injective character of the algebraically closed field `K`, and let `χ`, `χ'` be
multiplicative characters of `k` and `k'` whose names correspond, that is, the name of `χ'` is the
image of the name of `χ`. Here `charName T χ` is the unit `x_χ ∈ kˣ` with `χ = θ_{x_χ}` on `k`, and
`θ` is built from `T` with `Q = |k|`. Then `χ ∘ det` lifts to `χ' ∘ det` by characters: for every
`m`, some character `Φ` of `GL_m(k') ⋊ Gal(k'/k)` descends (`DescendsTo`) both to `χ ∘ det` over `k`
and to `χ' ∘ det` over `k'`. -/
lemma lift_detChar [IsScalarTower k k' K] {χ : MulChar k ℂ} {χ' : MulChar k' ℂ}
    (h_name : (charName T χ' : k') = algebraMap k k' (charName T χ)) :
    Lift ℕ (detChar χ) (detChar χ') := by
  -- With `x = x_χ`, the lift is `(g, σ) ↦ ∏ τ, θ_x (det (τ g))`: `θ_x` of the norm of `det g`.
  intro m
  let ν : Matrix (Fin m) (Fin m) k' →* ℂ :=
    (thetaChar T (Nat.card k) (algebraMap k K (charName T χ))).comp
      (.comp (algebraMap k' K) detMonoidHom)
  obtain ⟨ϑ, hϑ_char, hϑ, hϑ_lifts⟩ := exists_norm_char_semidirect (galActionGL k k' (Fin m)) ν
  refine ⟨ϑ, hϑ_char.mem_virtualChars, fun σ hσ ↦ ?_,
    DescendsTo.iff_comp_inl_eq_evalGL.mpr (funext fun g ↦ ?_)⟩
  · -- over `σ` with fixed field `k`, `ϑ` descends to `θ_x ∘ det`, which is `χ ∘ det` on `GL m k`
    simp +contextual [DescendsOnCoset, hϑ_lifts σ hσ _, ν, RingHom.map_det, ← thetaChar_charName T,
      algebraMap_apply k k' K]
  · -- on `GL m k'`: `θ_x` for `#k` at the norm of `z` is `θ_x` for `#k'` at `z`
    set x : K := algebraMap k K (charName T χ)
    set z : K := algebraMap k' K g.val.det
    have h_det (τ : Gal(k'/k)) : (galActionGL k k' (Fin m) τ g).val.det = τ g.val.det :=
      (τ.map_det _).symm
    calc ϑ (inl g)
      _ = thetaChar T (Nat.card k) x (algebraMap k' K (∏ τ : Gal(k'/k), τ g.val.det)) := by
        simp [hϑ, ν, h_det, x]
      _ = thetaChar T (Nat.card k) x (z ^ ∑ i ∈ range (finrank k k'), Nat.card k ^ i) := by
        rw [← Algebra.norm_eq_prod_automorphisms, algebraMap_norm_eq_pow_sum, map_pow]
      _ = thetaChar T (Nat.card k') x z := by
        simpa using (thetaChar_eq_apply_norm_pow T one_lt_card
          (algebraMap_pow_card_pred_eq_one (charName T χ)) one_lt_card natCard_eq_pow_finrank
          (pow_one _) (algebraMap_pow_card_pred_eq_one g.det)).symm
      _ = (detChar χ').evalGL g := by
        simp [← thetaChar_charName T χ', h_name, ← IsScalarTower.algebraMap_apply, x, z]

/-- Let `P` be a label of degree `m` over `k` with `P(1) ≠ 0`, and suppose that `Ξ_P` is `(-1) ^ m`
times the rank-`m` part of `greenCuspidal k θ`. Then the inner product in rank `m` of
`greenCuspidal k θ` times `μ` with the Brauer lift of `θ` is `1`. -/
private lemma rankInner_greenCuspidal_mulMoebius_brauerLift {P : k[X]} {m : ℕ} (hL : IsLabel m P)
    (h_not_root_one : ¬P.IsRoot 1) {θ : K → ℂ}
    (h_labelChar_eq : labelChar T P = (-1 : ℂ) ^ m • rankPart m (greenCuspidal k θ)) :
    rankInner m (greenCuspidal k θ).mulMoebius (brauerLift k θ) = 1 := by
  -- Move `μ` and the sign across, pass from the Brauer lift times `μ` to `greenCuspidal` by
  -- multiplying with `constOne`, and use that `Ξ_P` has norm `1`.
  calc rankInner m (greenCuspidal k θ).mulMoebius (brauerLift k θ)
    _ = (-1) ^ m * rankInner m (labelChar T P) (brauerLift k θ).mulMoebius := by
      simp [h_labelChar_eq, rankInner, rankPart, ← finMean_const_mul, ← mul_assoc, ← mul_pow,
        mul_right_comm _ (moebius _)]
    _ = (-1) ^ m * rankInner m (labelChar T P) (greenCuspidal k θ) := by
      rw [greenCuspidal, rankInner_labelChar_mul_constOne T hL h_not_root_one]
    _ = rankInner m (labelChar T P) ((-1 : ℂ) ^ m • rankPart m (greenCuspidal k θ)) := by
      simp [rankInner, rankPart, ← finMean_const_mul, mul_left_comm]
    _ = 1 := by
      rw [← h_labelChar_eq]
      simpa using rankInner_labelChar T hL _ hL

/-- Let `c` be a label of degree `m` over `k'` with `c(1) ≠ 0`, and `B` a class function. The inner
product in rank `m` of `(-1) ^ m` times `Ξ_c μ` with `B` is the inner product of `Ξ_c` with
`(-1) ^ m` times the rank-`m` part of `B μ` times the constant function `1`. -/
private lemma rankInner_neg_one_pow_smul_mulMoebius_labelChar {c : k'[X]} {m : ℕ} (hc : IsLabel m c)
    (hc_one : c.eval 1 ≠ 0) (B : Hall k') :
    rankInner m ((-1 : ℂ) ^ m • (labelChar T c).mulMoebius) B =
      rankInner m (labelChar T c) ((-1 : ℂ) ^ m • rankPart m (B.mulMoebius * constOne)) :=
  calc rankInner m ((-1 : ℂ) ^ m • (labelChar T c).mulMoebius) B
    _ = (-1) ^ m * rankInner m (labelChar T c) B.mulMoebius := by
      simp [rankInner, ← finMean_const_mul, mul_comm, mul_left_comm]
    _ = (-1) ^ m * rankInner m (labelChar T c) (B.mulMoebius * constOne) := by
      rw [rankInner_labelChar_mul_constOne T hc hc_one]
    _ = rankInner m (labelChar T c) ((-1 : ℂ) ^ m • rankPart m (B.mulMoebius * constOne)) := by
      simp [rankInner, rankPart, ← finMean_const_mul, mul_left_comm]

/-- For a label `P` over `k`, the function `Ξ` of `P` formed over `k'` is Galois stable: its value
at `σ(g)` is its value at `g`, as `σ` fixes the coefficients of `P`. -/
private lemma labelChar_map_evalGL_galActionGL {P : k[X]} {m : ℕ}
    (hL' : IsLabel m (P.map (algebraMap k k'))) (σ : Gal(k'/k)) (g : GL (Fin m) k') :
    (labelChar T (P.map (algebraMap k k'))).evalGL (galActionGL k k' (Fin m) σ g) =
      (labelChar T (P.map (algebraMap k k'))).evalGL g := by
  have hσP : (P.map (algebraMap k k')).map σ = P.map (algebraMap k k') :=
    Polynomial.ext fun _ ↦ by simp
  change (labelChar T (P.map (algebraMap k k'))).evalGL (g.map σ) = _
  rw [evalGL_labelChar_map T σ hL', hσP]

variable [IsScalarTower k k' K]

include hp

omit [Finite k] [Finite k'] in
/-- In an extension `k'/k` of prime degree, the fixed field of `σ` is `k` exactly when `σ ≠ 1`. -/
lemma hasFixedField_iff_ne_one {σ : Gal(k'/k)} : HasFixedField k σ ↔ σ ≠ 1 := by
  -- As the degree is prime, the fixed subalgebra of `σ` is `⊥` unless it is `⊤`, that is `σ = 1`.
  set fixed : Subalgebra k k' := σ.toAlgHom.equalizer 1 with h_fixed
  calc HasFixedField k σ
    _ ↔ fixed = ⊥ := by
      simp [h_fixed, HasFixedField, SetLike.ext_iff, Set.ext_iff, Algebra.mem_bot, IsFixedPt,
        iff_comm]
    _ ↔ fixed < ⊤ := (isSimpleOrder_of_finrank_prime k k' hp).lt_top_iff_eq_bot.symm
    _ ↔ σ ≠ 1 := by simp [h_fixed, lt_top_iff_ne_top, SetLike.ext_iff, DFunLike.ext_iff]

/-- Let `k'/k` have prime degree, and let the class functions `Φ` and `Ψ` on
`GL n k' ⋊ Gal(k'/k)` descend to `F` and `G`. Then `#Gal(k'/k)` times the inner product of `Φ` and
`Ψ` is the inner product of their restrictions to `GL n k'`, plus `#Gal(k'/k) - 1` times the inner
product of `F` and `G` in rank `#n`. -/
lemma DescendsTo.card_mul_classInner {F G : Hall k} {Φ Ψ : GalSemidirect k k' n → ℂ}
    (hΦ : IsClassFunction Φ) (hΨ : IsClassFunction Ψ)
    (hΦF : DescendsTo Φ F) (hΨG : DescendsTo Ψ G) :
    Nat.card Gal(k'/k) * classInner Φ Ψ =
      classInner (Φ ∘ inl) (Ψ ∘ inl) + (Nat.card Gal(k'/k) - 1) * rankInner (Nat.card n) F G := by
  classical
  -- Split the mean over the cosets of `GL n k'`. The coset of `1` gives the inner product of the
  -- restrictions. Each `σ ≠ 1` has fixed field `k`, so by
  -- `IsRootChoice.index_mul_finMean_eq_classInner` its coset gives the inner product over `k`.
  set π : GalSemidirect k k' n →* Gal(k'/k) := rightHom with hπ
  set coset : Gal(k'/k) → ℂ := fun σ ↦
    π.ker.index * finMean fun s ↦ if π s = σ then starRingEnd ℂ (Φ s) * Ψ s else 0 with h_coset
  have h_one : coset 1 = New.classInner (Φ ∘ inl) (Ψ ∘ inl) := by
    simp [h_coset, hπ, New.classInner, index_ker, ↓rightHom_surjective,
      rightHom_eq_right, field]
  have h_other (σ : Gal(k'/k)) (hσ : σ ∈ univ.erase 1) :
      coset σ = rankInner (Fintype.card n) F G := by
    have h_fixed : HasFixedField k σ := (hasFixedField_iff_ne_one hp).2 (ne_of_mem_erase hσ)
    obtain ⟨root, h_root, -⟩ := exists_isRootChoice_GL (n := n) h_fixed
    rw [← classInner_evalGL]
    exact h_root.index_mul_finMean_eq_classInner (hΦF σ h_fixed) (hΨG σ h_fixed)
      (fun s x _ ↦ hΦ s x) fun s x _ ↦ hΨ s x
  calc Nat.card Gal(k'/k) * New.classInner Φ Ψ
    _ = ∑ σ, coset σ := by
      simp [h_coset, hπ, New.classInner, index_ker, rightHom_surjective, ← mul_sum, ← finMean_sum,
        -rightHom_eq_right]
    _ = New.classInner (Φ ∘ inl) (Ψ ∘ inl) +
        (Nat.card Gal(k'/k) - 1) * rankInner (Nat.card n) F G := by
      rw [← add_sum_erase _ _ (mem_univ 1), h_one, sum_congr rfl h_other]
      simp [Fintype.card_pos]

/-- The irreducible case of `shintani_lift_labelChar` when `1` is not a root. Let `P` be a label of
degree `m` over `k` with `P(1) ≠ 0` and `Ξ_P = (-1) ^ m` times the rank-`m` part of
`greenCuspidal k θ`, and let the character `J` descend to `greenCuspidal k θ` times `μ` over `k` and
to `(-1) ^ m` times `Ξ_P μ` formed over `k'`. Then `Ξ_P` lifts by characters to `Ξ_P` over `k'`. -/
private lemma lift_labelChar_of_not_isRoot_one {P : k[X]} {m : ℕ} [NeZero m] (hL : IsLabel m P)
    (h_not_root_one : ¬P.IsRoot 1) {θ : MulChar K ℂ}
    (h_labelChar_eq : labelChar T P = (-1 : ℂ) ^ m • rankPart m (greenCuspidal k θ))
    {J : GalSemidirect k k' (Fin m) → ℂ} (hJ : IsChar J)
    (hJ_down : DescendsTo J (greenCuspidal k θ).mulMoebius)
    (hJ_up : DescendsTo J ((-1 : ℂ) ^ m • (labelChar T (P.map (algebraMap k k'))).mulMoebius)) :
    Lift ℕ (labelChar T P) (labelChar T (P.map (algebraMap k k'))) := by
  classical
  -- Take a virtual lift `Φ` of `Y = Ξ_P` and replace it on `GL m k'` by the irreducible character
  -- `Y'` of label `P` over `k'`. By `IsIrreducibleChar.extend_semidirect` the result is a character
  -- once `Y'` is Galois stable (`labelChar_map_evalGL_galActionGL`, as `σ` fixes `P`),
  -- `⟨Y', Φ⟩ ≡ 1` modulo `#Gal` on `GL m k'` (`h_pair`), and the cosets of the `σ ≠ 1` add
  -- `#Gal - 1` to the norm (`h_self`).
  have hL' : IsLabel m (P.map (algebraMap k k')) := hL.map k'
  suffices h_rank : Lift ℕ (rankPart m (labelChar T P))
      (rankPart m (labelChar T (P.map (algebraMap k k')))) by
    rwa [rankPart_labelChar T hL, rankPart_labelChar T hL'] at h_rank
  set Y : Hall k := labelChar T P
  set Y' : Hall k' := labelChar T (P.map (algebraMap k k'))
  -- `β` lifts `(brauerLift k θ, B)` and `Φ` lifts `(Y, C)`.
  obtain ⟨B, hB⟩ := exists_lift_brauerLift k k' θ
  obtain ⟨β, hβ, hβ_down, hβ_up⟩ := hB m
  obtain ⟨Φ, hΦ, hΦ_down, hΦ_up⟩ := hB.rankPart_mulMoebius_mul_constOne (m := m) m
  set C : Hall k' := (-1 : ℂ) ^ m • rankPart m (B.mulMoebius * constOne)
  rw [← greenCuspidal, ← h_labelChar_eq] at hΦ_down
  have hΦ_class : IsClassFunction Φ := isClassFunction_of_mem_virtualChars hΦ
  have hΦ_res : Φ ∘ inl = C.evalGL := DescendsTo.iff_comp_inl_eq_evalGL.mp hΦ_up
  obtain ⟨N, hN⟩ : ∃ N : ℤ, classInner J β = N := hJ.exists_classInner_eq hβ
  -- The two inner products in `DescendsTo.card_mul_classInner` for `J` and `β`, over `k` and over
  -- `k'`; both use `P(1) ≠ 0`.
  have h_down : rankInner m (greenCuspidal k θ).mulMoebius (brauerLift k θ) = 1 :=
    rankInner_greenCuspidal_mulMoebius_brauerLift T hL h_not_root_one h_labelChar_eq
  have h_up : rankInner m ((-1 : ℂ) ^ m • Y'.mulMoebius) B = rankInner m Y' C :=
    rankInner_neg_one_pow_smul_mulMoebius_labelChar T hL'
      (by simpa [aeval_def] using h_not_root_one) B
  -- `DescendsTo.card_mul_classInner` for `J` and `β` determines `rankInner m Y' C` modulo `#Gal`.
  have h_pair : classInner Y'.evalGL (Φ ∘ inl) = 1 + Nat.card Gal(k'/k) * (N - 1 : ℤ) := by
    have h_split : Nat.card Gal(k'/k) * N = rankInner m Y' C + (Nat.card Gal(k'/k) - 1) := by
      have hJ_res : J ∘ inl = ((-1 : ℂ) ^ m • Y'.mulMoebius).evalGL :=
        DescendsTo.iff_comp_inl_eq_evalGL.mp hJ_up
      have hβ_res : β ∘ inl = B.evalGL := DescendsTo.iff_comp_inl_eq_evalGL.mp hβ_up
      simpa only [hJ_res, hβ_res, classInner_evalGL, Fintype.card_fin, Nat.card_fin, hN, h_down,
        h_up, mul_one] using hJ_down.card_mul_classInner hp hJ.isClassFunction
          (isClassFunction_of_mem_virtualChars hβ) hβ_down
    rw [hΦ_res, classInner_evalGL, Fintype.card_fin]
    push_cast
    linear_combination -h_split
  have h_self : Nat.card Gal(k'/k) * classInner Φ Φ =
      classInner (Φ ∘ inl) (Φ ∘ inl) + (Nat.card Gal(k'/k) - 1) := by
    have hY_norm : rankInner m Y Y = 1 := by simpa using rankInner_labelChar T hL _ hL
    simpa [hY_norm] using hΦ_down.card_mul_classInner hp hΦ_class hΦ_class hΦ_down
  let Ψ : GalSemidirect k k' (Fin m) → ℂ := fun s ↦ if s.right = 1 then Y'.evalGL s.left else Φ s
  have h_irr : IsIrreducibleChar Ψ :=
    (IsLabel.isIrreducibleChar_labelChar T (by simpa using hL')).extend_semidirect
      (labelChar_map_evalGL_galActionGL T hL') hΦ h_self _ h_pair
  -- `Ψ` is `Y'` on `GL m k'`, and `Φ`, which descends to `Y` (`hΦ_down`), over the `σ ≠ 1`.
  have h_on_cosets : DescendsTo Ψ Y := by
    simpa +contextual [Ψ, DescendsTo, DescendsOnCoset, hasFixedField_iff_ne_one hp] using hΦ_down
  exact .rankPart_of_hasCommonLift ⟨Ψ, h_irr.left.mem_virtualChars, h_on_cosets, by simp [Ψ, Y']⟩

/-- Shintani lifting: let `k'/k` be an extension of finite fields of prime degree (`hp`), `T`
injective (`IsFaithfulMulChar`) and `c` a label over `k` (`IsLabel`: monic, squarefree,
`c(0) ≠ 0`). Then `Ξ_c = labelChar T c` lifts by characters (`New.Lift ℕ`) to `Ξ_c` formed over
`k'`. -/
lemma shintani_lift_labelChar (hc : IsLabel r c) :
    Lift ℕ (labelChar T c) (labelChar T (c.map (algebraMap k k'))) := by
  classical
  -- Lifts multiply, so it is enough to treat an irreducible label `P`, with a root `x`.
  refine hc.induction_irreducible_mul (p := fun _ c ↦
      Lift ℕ (labelChar T c) (labelChar T (c.map (algebraMap k k')))) K (by simp)
    fun P _ c x hP_monic hP hP_coeff hx h_lift_c ↦ ?_
  suffices h_lift_P : Lift ℕ (labelChar T P) (labelChar T (P.map (algebraMap k k'))) by
    simpa using h_lift_P.mul h_lift_c
  by_cases h_root_one : P.IsRoot 1
  · -- For `P = X - 1` this is the lift of the trivial character in rank `1`.
    have h_det : Lift ℕ (detChar (1 : MulChar k ℂ)) (detChar (1 : MulChar k' ℂ)) :=
      lift_detChar T (by simp)
    simpa [← labelChar_X_sub_C T, minpoly.eq_of_irreducible_of_monic hP h_root_one hP_monic] using
      Lift.rankPart_of_hasCommonLift (h_det 1)
  -- Otherwise `Ξ_P` is `(-1) ^ deg P` times a rank part of `greenCuspidal k θ_x`, and
  -- `exists_isChar_descendsTo_labelChar` gives the character `J` that
  -- `lift_labelChar_of_not_isRoot_one` needs.
  have hP_deg : NeZero P.natDegree := .of_pos hP.natDegree_pos
  have hL : IsLabel P.natDegree P := ⟨hP_monic, hP.squarefree, rfl, hP_coeff⟩
  have h_labelChar_eq : labelChar T P = (-1 : ℂ) ^ P.natDegree •
      rankPart P.natDegree (greenCuspidal k (thetaChar T (Nat.card k ^ P.natDegree) x)) :=
    (labelChar_eq_greenTau T hP hP_monic).trans (greenTau_eq hP hP_coeff hx)
  obtain ⟨J, hJ, hJ_down, hJ_up⟩ :=
    exists_isChar_descendsTo_labelChar k' T hP hL hx (finrank_extension k _ P.natDegree)
  exact lift_labelChar_of_not_isRoot_one hp T hL h_root_one h_labelChar_eq hJ hJ_down hJ_up

end New
