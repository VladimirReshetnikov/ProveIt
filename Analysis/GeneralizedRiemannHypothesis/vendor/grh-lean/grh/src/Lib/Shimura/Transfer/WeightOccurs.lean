import Lib.DiscreteSeries.Character.WeylCharacterFormula
import Lib.GLn.SchurModule.SchurNorm
import Lib.Shimura.TraceFormula.DefiniteTrace
import Lib.Shimura.TraceFormula.MarkedDefiniteSums
import Lib.Shimura.TraceFormula.TestFunction
import Lib.Shimura.Transfer.Lefschetz

/-!
# Coefficient systems from weights and the degrees where Hecke eigensystems occur

A weight `κ` gives a coefficient system on `GL_a(E)`. Its Hecke eigensystems occur in the degrees
given by the jumps of `κ`, in the sense of `New.Variety.OccursInWeight`: the local terms of the
Lefschetz side do not all cancel.

`Φ v` is the embedding that the CM type chooses at `v`, and `v₀` is the base infinite place fixed by
`New.CMBase E`.

* `New.Variety.occursInWeight_of_isTestEigenform`: the Hecke eigenvalues of a test eigenform occur,
  if the character of the coefficients is given by a Schur polynomial and powers of the determinant.
* `New.Variety.exists_isCoefficientSystem`: the coefficient system attached to a weight, and the
  occurrence of the eigensystems of its test vectors.

Notions from other files:
* `New.Weight`: For `κ : Weight E` and an infinite place `v` of `E`, `κ.1 v h` is the number of
  columns of height `h` of a Young diagram, and `κ.2 v` is an integer exponent of the determinant.
* `New.Variety.entryConj`: The endomorphism of the unitary group {g : gᴴg = 1} of matrices over R
  indexed by `n` that applies the involution of R to each entry.
* `New.jumps`: The multiset {j − 1 − λ_j} if σ is in the CM type, else {λ_j + a − j}, 1 ≤ j ≤ a,
  with λ the highest weight of κ at σ.
* `New.Space.weightRep`: The representation of the rational unitary group on coordinate vectors of
  weight `(κ.1, κ.2)`, through its components at the infinite places and `New.conjWeylRep`.

## Relation to the literature

Known result: Transfer of eigensystems between unitary inner forms differing at a real place. Only
the occurrence is proved here, namely that the Hecke eigensystem of a definite form occurs, in each
Hodge weight, on the variety for signature (1, n-1), with n odd and a cuspidal type at one split
place. It is proved by comparing two finite counts, without stabilisation. Source: Harris and
Labesse, Conditional base change for unitary groups, Asian J. Math. 8 (2004), Thm 2.1.2; Labesse,
Changement de base CM et séries discrètes (2011), Thm 5.4; count as in Goresky and MacPherson, The
topological trace formula (2003), and Shimura, On the trace formula for Hecke operators, Acta Math.
132 (1974).
-/

open NumberField Matrix Polynomial Fintype Finset IsAlgClosed LinearMap Submodule New.QuadField Fin

/-- An endomorphism of a finite-dimensional complex vector space all of whose positive powers have
trace zero is nilpotent. -/
lemma New.Variety.isNilpotent_of_trace_pow_succ_eq_zero {V : Type} [AddCommGroup V] [Module ℂ V]
    [Module.Finite ℂ V] {f : Module.End ℂ V} (hf : ∀ k : ℕ, (f ^ (k + 1)).trace ℂ V = 0) :
    IsNilpotent f := by
  -- The powers of `f` have the traces of the powers of zero, so the characteristic polynomials
  -- agree.
  let b : Module.Basis (Module.Free.ChooseBasisIndex ℂ V) ℂ V := Module.Free.chooseBasis ℂ V
  have h_trace (k : ℕ) : (toMatrix b b f ^ k).trace =
      (toMatrix b b 0 ^ k).trace + ∑ e ∈ (∅ : Finset ℂ), e ^ k := by
    rw [toMatrix_pow, toMatrix_pow, ← trace_eq_matrix_trace, ← trace_eq_matrix_trace]
    cases k <;> simp [hf]
  rw [isNilpotent_iff_charpoly, ← charpoly_toMatrix f b,
    charpoly_eq_mul_of_trace_pow_add _ ∅ _ h_trace, charpoly_toMatrix, LinearMap.charpoly_zero,
    Finset.prod_empty, mul_one]

/-- For `a` odd, `rootCoeffEval` sends the variable `X 0` to minus the product of the `a` roots. -/
lemma New.Variety.rootCoeffEval_X_zero_of_odd {a : ℕ} [NeZero a] (ha : Odd a) {R : Type}
    [CommRing R] (r : Fin a → R) :
    rootCoeffEval (a := a) (univ.val.map r) (MvPolynomial.X 0) = -univ.prod r := by
  simp [rootCoeffEval, coeff_zero_eq_eval_zero, eval_prod, prod_neg, ha.neg_one_pow, -univ_val_map]

/-- Let `E` be a CM field containing ℚ(i√d₀), and let `w₁` be a finite place of `E` that is split
over the maximal real subfield and divides the level `𝔑`. Any product of the Hecke elements
`τ_{w,j}` (`tauHecke`, in the Hecke algebra of level `K(𝔑)`) at places `w` safe for `𝔑` (among other
things, `𝔑 ∉ w` and `𝔑` lies in no place over the conjugate of the place below `w`) lies in the span
of the group elements `[g]` with `g` a unitary similitude (`gᴴ g` a scalar finite idele of ℚ) whose
component at `w₁` is trivial. Here the component is taken via `dualComponent w₁`, the inverse
transpose of the `w₁`-component in `GL_a(E_{w₁})`. -/
lemma New.Variety.prod_map_tauHecke_mem_spanOn {E : Type} [Field E] [NumberField E] [IsCMField E]
    {a d₀ : ℕ} [HasQuadSubfield d₀ E] {𝔑 : 𝓞 E} {w₁ : SplitFinPlace E} (hw₁ : 𝔑 ∈ w₁.val.asIdeal)
    (L : List (SafePlace 𝔑 × ℕ)) :
    (L.map tauHecke).prod.val ∈ spanOn ℂ (GU E (Fin a) ⊓ (dualComponent w₁).ker).carrier := by
  induction L with
  | nil => exact subset_span ⟨1, Subgroup.one_mem _, by simp [MonoidAlgebra.one_def]⟩
  | cons s L ih =>
    obtain ⟨⟨v, hv_safe⟩, j⟩ := s
    refine spanOn.mul heckeSum_mem_spanOn ih ?_
    rintro _ ⟨U, rfl⟩ g
    have h_GU : invHeckeIsogeny (v : SplitFinPlace E) U ∈ GU E (Fin a) :=
      And.left (invHeckeIsogeny_mem_GUPlus _ U)
    refine Subgroup.mul_mem _ ⟨h_GU, ?_⟩
    -- Both factors of `invHeckeIsogeny` are trivial at `w₁`, because `w₁` divides `𝔑`, whereas a
    -- safe place and the places over the conjugate of the place below it do not.
    -- (`h_notMem` says that `𝔑 ∉ v`, and `h_notMem_conj` that `𝔑` lies in no place over the
    -- conjugate of the place below `v`.)
    obtain ⟨-, h_notMem, h_notMem_conj⟩ := hv_safe
    have h_below_ne : (w₁ : FinPlace E).below (QuadField d₀) ≠
        star ((v : FinPlace E).below (QuadField d₀)) :=
      fun h_below ↦ h_notMem_conj _ h_below hw₁
    have h_ne : (w₁ : FinPlace E) ≠ (v : FinPlace E) :=
      fun h_eq ↦ h_notMem (by rwa [← h_eq])
    have h_star_ne : star (w₁ : FinPlace E) ≠ (v : FinPlace E) :=
      fun h_eq ↦ h_below_ne (by rw [← h_eq, below_star, star_star])
    suffices h_triv :
        (invHeckeIsogeny (v : SplitFinPlace E) U).map (evalAt (w₁ : FinPlace E)) = 1 by
      simp [dualComponent, h_triv]
    rw [invHeckeIsogeny, map_mul, evalAt_conjAtSplit_of_ne (hu := h_ne) (hu' := h_star_ne),
      mul_one]
    -- `uniformizerNorm v` is a norm of a local idele at `v`, so the central scalar is trivial
    -- at `w₁`.
    rw [uniformizerNorm, ← map_pow, ← map_inv, ← map_pow, ← map_inv]
    exact evalAt_centralScalar_of_ne h_below_ne _

/-- A word `L` in the Hecke operators `tauHecke` at safe places acts on a common eigenvector `φ`
of the operators `heckeSum`, with eigenvalues `θ`, by the product of the eigenvalues of its
letters. -/
lemma New.Variety.asAlgebraHom_prod_map_tauHecke_apply {E : Type} [Field E] [NumberField E]
    [IsCMField E] {a d₀ : ℕ} [HasQuadSubfield d₀ E] {W : Type} [AddCommGroup W] [Module ℂ W]
    {𝔑 : 𝓞 E} {π : Representation ℂ (GL (Fin a) (𝔸f E)) W} {φ : W} {θ : SafePlace 𝔑 → ℕ → ℂ}
    (h_eig : ∀ (w : SafePlace 𝔑) (j : ℕ), π.asAlgebraHom (heckeSum (Fin a) ℂ w.val j) φ = θ w j • φ)
    (L : List (SafePlace 𝔑 × ℕ)) :
    π.asAlgebraHom (L.map tauHecke).prod.val φ = (L.map ↿θ).prod • φ := by
  induction L with
  | nil => simp
  | cons s L ih =>
    have h_head : π.asAlgebraHom (tauHecke s).val φ = ↿θ s • φ := h_eig s.1 s.2
    simp [ih, h_head, smul_smul, mul_comm, -SubmonoidClass.coe_list_prod]

/-- The local terms of a regular element `y`, summed over the marked eigenvalue. Let `q` be the
Schur polynomial of `l` at `Φ v₀`, and `(-X 0) ^ m` (for `a` odd, the `m`-th power of the product of
the roots) at the conjugate of `Φ v₀` and at the `Φ v` with `v ≠ v₀`. Let `μ k` be the numbered
roots of `y` at `Φ v₀`. The `k`-th term is the `k`-th Lagrange basis polynomial of the `μ` at
`μ k * X`, times the product over `σ` of `q σ` at `lieRoots`. These are the roots `r` of `σ y`,
taken as `r X` if the eigenline of `r` lies in the Lie algebra and as `r` otherwise: at `Φ v₀` only
the marked root, at its conjugate all but one, at the other `Φ v` all, at their conjugates none.
Then the sum is the product over `σ` of the values of `q σ` at the eigenvalues of `σ y`, times
`∑ k, X ^ l k` shifted by a fixed power of `X`. -/
lemma New.Variety.sum_basis_comp_mul_prod_rootCoeffEval_eq {E : Type} [Field E] [CMBase E] {a : ℕ}
    [NeZero a] (ha : Odd a) {q : (E →+* ℂ) → MvPolynomial (Fin a) ℤ} {l : Fin a → ℕ} {m : ℕ}
    (hq : q (Φ v₀) = genericSchur l) (hq_conj : q (star (Φ v₀)) = (-MvPolynomial.X 0) ^ m)
    (hq_other : ∀ v : InfinitePlace E, v ≠ v₀ → q (Φ v) = (-MvPolynomial.X 0) ^ m)
    {y : GL (Fin a) E} (hy : y.val.charpoly.Separable) :
    ∑ k : Fin a,
        (Lagrange.basis univ (numberedRoots (Φ v₀) y.val.charpoly) k).comp
            (X * C (numberedRoots (Φ v₀) y.val.charpoly k)) *
          ∏ σ : E →+* ℂ, rootCoeffEval
            (lieRoots y.val.charpoly (numberedRoots (Φ v₀) y.val.charpoly k) σ) (q σ) =
      C (∏ σ : E →+* ℂ, rootCoeffEval (y.val.charpoly.map σ).roots (q σ)) *
        ∑ k : Fin a, X ^ (m * (a - 1 + a * (Core.numInfPlaces E - 1)) + l k) := by
  -- Evaluate the factor at each embedding. Only the one at `Φ v₀` depends on the marked root `r k`,
  -- and there the sum over `k` is `sum_lagrange_smul_rootCoeffEval`; the others are constants
  -- times powers of `X`.
  set P : E[X] := y.val.charpoly
  set r : Fin a ↪ ℂ := numberedRoots (Φ v₀) P
  let s (σ : E →+* ℂ) : ℂ := rootCoeffEval (P.map σ).roots (q σ)
  have h_roots (σ : E →+* ℂ) : (P.map σ).roots = univ.val.map (numberedRoots σ P : Fin a ↪ ℂ) :=
    roots_eq_map_numberedRoots hy σ
  -- At `Φ v₀` only the marked root is multiplied by `X`.
  have h_marked (k : Fin a) : lieRoots P (r k) (Φ v₀) =
      univ.val.map fun k' : Fin a ↦ (if k' = k then X else 1) * C (r k') := by
    simp [lieRoots, IsLieRoot, h_roots, r, -ite_mul, -univ_val_map]
  -- At its conjugate `a - 1` roots are multiplied by `X`.
  have h_conj (k : Fin a) : rootCoeffEval (lieRoots P (r k) (star (Φ v₀))) (q (star (Φ v₀))) =
      X ^ (m * (a - 1)) * C (s (star (Φ v₀))) := by
    simp only [s, lieRoots, hq_conj, roots_map_conjugate]
    -- `ite_mul` is left out so that the factors `if … then X else 1` stay whole for `prod_ite`
    simp [IsLieRoot, h_roots, rootCoeffEval_X_zero_of_odd ha, -ite_mul,
      (RingHom.injective _).eq_iff,
      prod_ite, filter_ne', mul_pow, r, ← pow_mul', prod_mul_distrib, -univ_val_map]
  -- At another place `v` all `a` roots at `Φ v` are multiplied by `X`, and none at its conjugate.
  have h_other (k : Fin a) (v : {v // v ≠ v₀}) :
      rootCoeffEval (lieRoots P (r k) (Φ v.val)) (q (Φ v.val)) = X ^ (m * a) * C (s (Φ v.val)) := by
    simp [s, hq_other v v.prop, lieRoots, IsLieRoot, v.prop, h_roots,
      rootCoeffEval_X_zero_of_odd ha,
      mul_pow, prod_mul_distrib, -univ_val_map]
    -- what is left is `A ^ m * (X ^ a) ^ m = X ^ (m * a) * A ^ m`
    ring
  have h_other_conj (k : Fin a) (v : {v // v ≠ v₀}) :
      rootCoeffEval (lieRoots P (r k) (star (Φ v.val))) (q (star (Φ v.val))) =
        C (s (star (Φ v.val))) := by
    simp [s, lieRoots, IsLieRoot, v.prop, ← rootCoeffEval_map]
  have h_sum_marked : ∑ k : Fin a, (Lagrange.basis univ r k).comp (X * C (r k)) *
      rootCoeffEval (lieRoots P (r k) (Φ v₀)) (q (Φ v₀)) = C (s (Φ v₀)) * ∑ k : Fin a, X ^ l k := by
    simpa only [h_marked, s, h_roots, hq, smul_eq_mul, comp_eq_aeval] using
      sum_lagrange_smul_rootCoeffEval l r
  -- The factors at the embeddings other than `Φ v₀` do not depend on `k`: they give `X ^ N * C c`.
  set N : ℕ := m * (a - 1 + a * (Core.numInfPlaces E - 1)) with hN
  set c : ℂ := s (star (Φ v₀)) * ∏ v : {v // v ≠ v₀}, s (Φ v.val) * s (star (Φ v.val)) with hc
  have h_prod (k : Fin a) : ∏ σ : E →+* ℂ, rootCoeffEval (lieRoots P (r k) σ) (q σ) =
      X ^ N * C c * rootCoeffEval (lieRoots P (r k) (Φ v₀)) (q (Φ v₀)) := by
    simp [hN, hc, prod_embeddings_eq_prod_pairs, prod_eq_mul_prod_subtype_ne _ v₀, h_conj, h_other,
      h_other_conj, prod_mul_distrib]
    ring
  have h_const : ∏ σ : E →+* ℂ, s σ = s (Φ v₀) * c := by
    rw [hc, prod_embeddings_eq_prod_pairs, prod_eq_mul_prod_subtype_ne _ v₀, mul_assoc]
  calc _ = X ^ N * C c * ∑ k : Fin a, (Lagrange.basis univ r k).comp (X * C (r k)) *
        rootCoeffEval (lieRoots P (r k) (Φ v₀)) (q (Φ v₀)) := by
        simp only [h_prod, mul_sum, mul_left_comm]
    _ = C (∏ σ : E →+* ℂ, s σ) * ∑ k : Fin a, X ^ (N + l k) := by
        simp only [h_sum_marked, h_const, pow_add, ← mul_sum, map_mul]
        ring

/-- Comparison of trace formulas, for `a` odd and `𝔑` neat. Let the trace of `ξ y⁻¹` at regular `y`
be the product of the values of `q σ` at the eigenvalues of `σ y` (`q` as in
`sum_basis_comp_mul_prod_rootCoeffEval_eq`), and let `f` be regular of cuspidal type `χ` at `w₀`. If
`f` is null (`New.Variety.IsNullHecke`) in the weight `l j + m (a - 1 + a (n - 1))`, `n` the number
of infinite places of `E`, then `f` has trace zero on the definite forms with coefficients in
`ξ`. -/
lemma New.Variety.trace_definiteForms_rep_eq_zero_of_isNullHecke {E : Type} [Field E] [CMBase E]
    {a : ℕ} [NeZero a] (ha : Odd a) {W : Type} [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W]
    {ξ : Representation ℂ (GL (Fin a) E) W} {q : (E →+* ℂ) → MvPolynomial (Fin a) ℤ}
    {l : Fin a → ℕ} {m : ℕ}
    (h_char : ∀ y : GL (Fin a) E, y.val.charpoly.Separable →
      (ξ y⁻¹).trace ℂ W = ∏ σ : E →+* ℂ, rootCoeffEval (y.val.charpoly.map σ).roots (q σ))
    (hq : q (Φ v₀) = genericSchur l) (hq_conj : q (star (Φ v₀)) = (-MvPolynomial.X 0) ^ m)
    (hq_other : ∀ v : InfinitePlace E, v ≠ v₀ → q (Φ v) = (-MvPolynomial.X 0) ^ m)
    {𝔑 : 𝓞 E} (hN : IsNeat (Fin a) 𝔑)
    {f : heckeAlgebra (Fin a) ℂ 𝔑} (h_reg : IsRegularHecke f) {w₀ : SplitFinPlace E}
    {J : Subgroup (GL (Fin a) (LocField w₀.val))} {χ : J →* ℂ} (hχ : IsCuspidalType J χ)
    (h_type : f.val ∈ fixedToEigen (levelGU (Fin a) 𝔑) (conjAtSplit w₀) J χ) {j : Fin a}
    (h_null : IsNullHecke (∑ σ : E →+* ℂ, (q σ).totalDegree + 1)
      (m * (a - 1 + a * (Core.numInfPlaces E - 1)) + l j) f) :
    (definiteForms.rep 𝔑 ξ f).trace ℂ (definiteForms 𝔑 ξ) = 0 := by
  classical
  -- The definite trace formula writes the trace as an orbit sum weighted by the `X ^ d`
  -- coefficients of the local terms, divided by `mult`. By `finsum_countTerm_marked_eq_definite`
  -- this equals the marked orbit sum, which `h_null` kills.
  set d : ℕ := m * (a - 1 + a * (Core.numInfPlaces E - 1)) + l j
  have h_fin : (countTerm True f 1).support.Finite := (h_null h_reg 1).left
  have h_sum (α : Fin (∑ σ, (q σ).totalDegree + 1) → 𝓞 E) :
      ∑ᶠ c, countTerm True f (fun P μ ↦ (localTerm (2 * α) P μ).coeff d) c = 0 :=
    (h_null h_reg α).right
  -- `X ^ d` occurs `mult` times in the sum of powers of `X` in
  -- `sum_basis_comp_mul_prod_rootCoeffEval_eq`.
  let mult : ℕ := #{k | l j = l k}
  have h_mult : (mult : ℂ) ≠ 0 := by simp [mult]
  let lagrange (P : E[X]) (k : Fin a) : ℂ[X] :=
    (Lagrange.basis univ (numberedRoots (Φ v₀) P) k).comp (X * C (numberedRoots (Φ v₀) P k))
  let w (P : E[X]) (k : Fin a) : ℂ :=
    (lagrange P k * ∏ σ, rootCoeffEval (lieRoots P (numberedRoots (Φ v₀) P k) σ) (q σ)).coeff d /
      mult
  have h_weight (y : GL (Fin a) E) (hy : y.val.charpoly.Separable) :
      (ξ y⁻¹).trace ℂ W = ∑ k, w y.val.charpoly k := by
    rw [← sum_div, ← finsetSum_coeff, sum_basis_comp_mul_prod_rootCoeffEval_eq ha hq hq_conj
      hq_other hy, ← h_char y hy,
      eq_div_iff h_mult]
    simp [d, mult]
  have h_both : ∀ ε : Prop, (countTerm ε f 1).support.Finite :=
    Prop.forall.mpr ⟨finite_support_countTerm_definite hN f 1, h_fin⟩
  have h_trace : (definiteForms.rep 𝔑 ξ f).trace ℂ (definiteForms 𝔑 ξ) =
      ∑ᶠ c, countTerm True f w c := by
    calc _ = ∑ᶠ c, countTerm False f w c :=
          trace_definiteForms_eq_finsum_countTerm ξ hN h_reg h_weight
      _ = _ :=
          (finsum_countTerm_marked_eq_definite hN (by simpa using ha) h_reg hχ h_type w h_both).symm
  rw [h_trace]
  -- Both sums run over the finite set `h_fin.toFinset`, and the constant `mult` cancels.
  simp_rw [finsum_countTerm_eq_sum _ h_fin, ← sum_coe_sort h_fin.toFinset, w, mul_div_assoc',
    ← sum_div, div_eq_zero_iff, h_mult, or_false] at h_sum ⊢
  -- A class `c` has a characteristic polynomial `P c` and a marked root, numbered `μ c`. Now
  -- `h_sum` says that the linear form `L` (multiply by the Lagrange factor, take the `X ^ d`
  -- coefficient, sum over classes) kills the products `∏ (1 - σ (2 α) t)`, `t` in `lieRoots`, for
  -- all `α`; by `map_prod_rootCoeffEval_eq_zero` it then kills the products of the `q σ`.
  -- `c.val.out` is a triple (frame, element `y`, marked index), as in `countTerm`
  let P (c : h_fin.toFinset) : E[X] := c.val.out.snd.fst.val.charpoly
  let μ (c : h_fin.toFinset) : Fin a := c.val.out.snd.snd
  let L : (h_fin.toFinset → ℂ[X]) →ₗ[ℂ] ℂ :=
    dotProductBilin ℂ ℂ (fun c : h_fin.toFinset ↦ countTerm True f 1 c) ∘ₗ
      (lcoeff ℂ d).compLeft h_fin.toFinset ∘ₗ mulLeft ℂ fun c ↦ lagrange (P c) (μ c)
  have h_card (c : h_fin.toFinset) (σ : E →+* ℂ) :
      (lieRoots (P c) (numberedRoots (Φ v₀) (P c) (μ c)) σ).card = a := by
    simp [P, lieRoots, card_roots_eq_natDegree]
  have h_degree (σ : E →+* ℂ) :
      (q σ).totalDegree ≤ Fintype.card (Fin (∑ τ, (q τ).totalDegree + 1)) := by
    simp [sum_eq_add_sum_subtype_ne _ σ, add_assoc]
  change L (fun c ↦ ∏ σ, rootCoeffEval
    (lieRoots (P c) (numberedRoots (Φ v₀) (P c) (μ c)) σ) (q σ)) = 0
  exact map_prod_rootCoeffEval_eq_zero h_degree algebraicIndependent_embedding_two_mul h_card L
    h_sum

/-- `φ` is a definite form of level `𝔑` with coefficients in `ξ`, a test vector, and an
eigenvector of the Hecke operators at the safe places with eigenvalues `θ`. -/
structure New.Variety.IsTestEigenform {E : Type} [Field E] [CMBase E] {a d₀ : ℕ}
    [HasQuadSubfield d₀ E] {W : Type} [AddCommGroup W] [Module ℂ W] (𝔑 : 𝓞 E)
    (ξ : Representation ℂ (GL (Fin a) E) W) (φ : GL (Fin a) (𝔸f E) → W)
    (θ : SafePlace 𝔑 → ℕ → ℂ) : Prop where
  /-- `φ` is a form on the definite frames. -/
  mem_definiteForms : φ ∈ definiteForms 𝔑 ξ
  /-- `φ` is a test vector at some split places `w₀`, `w₁`, for some type `(J, χ)` at `w₀`. -/
  exists_isTestVector : ∃ (w₀ w₁ : SplitFinPlace E)
    (J : Subgroup (GL (Fin a) (LocField w₀.val))) (χ : J →* ℂ),
    IsTestVector 𝔑 (rightRegular ℂ (GL (Fin a) (𝔸f E)) W) φ w₀ w₁ χ
  /-- The `j`-th Hecke operator at `w` multiplies `φ` by `θ w j`. -/
  heckeSum_apply (w : SafePlace 𝔑) (j : ℕ) :
    (rightRegular ℂ (GL (Fin a) (𝔸f E)) W).asAlgebraHom (heckeSum (Fin a) ℂ w.val j) φ =
      θ w j • φ

/-- Let `a` be odd and `𝔑` neat. Suppose the trace of `ξ y⁻¹` at regular `y` is the product over `σ`
of the values of `q σ` at the eigenvalues of `σ y`, where `q` is the Schur polynomial of `l` at
`Φ v₀` and `(-X 0) ^ m` at the other `Φ v` and at the conjugate of `Φ v₀`. Let `θ` be the Hecke
eigenvalues at the safe places of a test eigenform of level `𝔑` with coefficients in `ξ`. Then `θ`
occurs (`New.Variety.OccursInWeight`, with parameter `∑ σ, deg (q σ) + 1`) in the weight
`l j + m (a - 1 + a (n - 1))` for every `j`, where `n` is the number of infinite places of `E`:
every combination `p` of `tauHecke` words with `p θ = 1` has a Hecke multiple `b p` that is not null
in that weight. -/
lemma New.Variety.occursInWeight_of_isTestEigenform {E : Type} [Field E] [CMBase E] {a d₀ : ℕ}
    [HasQuadSubfield d₀ E] [NeZero a] (ha : Odd a) {W : Type} [AddCommGroup W] [Module ℂ W]
    [Module.Finite ℂ W] {ξ : Representation ℂ (GL (Fin a) E) W}
    {q : (E →+* ℂ) → MvPolynomial (Fin a) ℤ} {l : Fin a → ℕ} {m : ℕ}
    (h_char : ∀ y : GL (Fin a) E, y.val.charpoly.Separable →
      (ξ y⁻¹).trace ℂ W = ∏ σ : E →+* ℂ, rootCoeffEval (y.val.charpoly.map σ).roots (q σ))
    (hq : q (Φ v₀) = genericSchur l) (hq_conj : q (star (Φ v₀)) = (-MvPolynomial.X 0) ^ m)
    (hq_other : ∀ v : InfinitePlace E, v ≠ v₀ → q (Φ v) = (-MvPolynomial.X 0) ^ m)
    {𝔑 : 𝓞 E} (hN : IsNeat (Fin a) 𝔑)
    {φ : GL (Fin a) (𝔸f E) → W} {θ : SafePlace 𝔑 → ℕ → ℂ} (h_form : IsTestEigenform 𝔑 ξ φ θ)
    (j : Fin a) :
    OccursInWeight a (∑ σ : E →+* ℂ, (q σ).totalDegree + 1) θ
      (m * (a - 1 + a * (Core.numInfPlaces E - 1)) + l j) := by
  -- Suppose all `b * p` are null in this weight, where the polynomial `p` in the Hecke operators
  -- fixes `φ`. For the test function `b` all positive powers of `b * p` then have trace zero, so
  -- `b * p` acts nilpotently on forms; but none of its powers kills `φ`.
  have hφ : φ ∈ definiteForms 𝔑 ξ := h_form.mem_definiteForms
  obtain ⟨w₀, w₁, J, χ, h_test⟩ := h_form.exists_isTestVector
  -- `p` is the combination `∑ c L • L` of words `L ∈ s` in the Hecke operators, with
  -- `∑ c L * θ(L) = 1` (`hc`); `h_null` says that every `b * p` is null in this weight
  intro s c hc h_null
  set p : heckeAlgebra (Fin a) ℂ 𝔑 := ∑ L ∈ s, c L • (L.map tauHecke).prod with hp
  -- `coe_list_prod` is left out of the two `simp` calls: it would rewrite the coerced products to
  -- `List.map (Subtype.val ∘ tauHecke)`, which the lemmas on words no longer match
  have h_supp : p.val ∈ spanOn ℂ (GU E (Fin a) ⊓ (dualComponent w₁).ker).carrier := by
    simp [hp, prod_map_tauHecke_mem_spanOn h_test.mem_snd, sum_mem, smul_mem,
      -SubmonoidClass.coe_list_prod]
  have h_fix : (rightRegular ℂ (GL (Fin a) (𝔸f E)) W).asAlgebraHom p.val φ = φ := by
    simp [hp, asAlgebraHom_prod_map_tauHecke_apply h_form.heckeSum_apply, hc, smul_smul,
      ← Finset.sum_smul, -SubmonoidClass.coe_list_prod]
  -- No power of `b * p` kills `φ`; the positive ones are regular and of type `χ` at `w₀`.
  obtain ⟨b, hb⟩ : ∃ b : heckeAlgebra (Fin a) ℂ 𝔑, ∀ m : ℕ,
      (rightRegular ℂ (GL (Fin a) (𝔸f E)) W).asAlgebraHom ((b * p) ^ m).val φ ≠ 0 ∧
        IsRegularHecke ((b * p) ^ (m + 1)) ∧
        ((b * p) ^ (m + 1)).val ∈ fixedToEigen (levelGU (Fin a) 𝔑) (conjAtSplit w₀) J χ :=
    exists_test_function (Submodule.mem_inf.mp hφ).right h_test h_supp h_fix
  have h_finite_forms : Module.Finite ℂ (definiteForms 𝔑 ξ) := finite_definiteForms ξ hN
  have h_nilpotent : IsNilpotent (definiteForms.rep 𝔑 ξ (b * p)) := by
    refine isNilpotent_of_trace_pow_succ_eq_zero fun k ↦ ?_
    obtain ⟨-, h_reg, h_type⟩ := hb k
    rw [← map_pow]
    refine trace_definiteForms_rep_eq_zero_of_isNullHecke ha h_char hq hq_conj hq_other hN h_reg
      h_test.isCuspidalType h_type
      (j := j) ?_
    rw [pow_succ, ← mul_assoc]
    exact h_null _
  obtain ⟨k, hk⟩ := h_nilpotent
  have h_kill : definiteForms.rep 𝔑 ξ ((b * p) ^ k) ⟨φ, hφ⟩ = 0 := by
    rw [map_pow, hk, LinearMap.zero_apply]
  exact (hb k).left (congrArg Subtype.val h_kill)

/-- Inverting nonzero numbers `r i` and reversing their order in a generalized Vandermonde
determinant amounts to replacing the exponents `w j` by `a - 1 - w j.rev`, up to the factor
`(∏ r) ^ (1 - a)`. -/
lemma New.Variety.det_inv_rev_zpow {a : ℕ} {r : Fin a → ℂ} (h_ne : ∀ i : Fin a, r i ≠ 0)
    (w : Fin a → ℤ) :
    (of fun i j : Fin a ↦ (r i.rev)⁻¹ ^ w j).det =
      univ.prod r ^ (1 - a : ℤ) * (of fun i j : Fin a ↦ r i ^ (a - 1 - w j.rev)).det := by
  rw [← det_zpow_add h_ne, ← det_submatrix_equiv_self revPerm
    (of fun i j : Fin a ↦ r i ^ ((1 - a : ℤ) + (a - 1 - w j.rev)))]
  simp [← add_sub_assoc, submatrix]

/-- The bialternant formula with integer exponents: if `l = m + k`, then the Schur polynomial of `l`
at nonzero numbers `r i`, times the Vandermonde determinant, is `(∏ r) ^ m * det (r i ^ k j)`. -/
lemma New.Variety.rootCoeffEval_genericSchur_mul_det_zpow {a : ℕ} {r : Fin a → ℂ}
    (h_ne : ∀ i : Fin a, r i ≠ 0)
    {l : Fin a → ℕ} {m : ℕ} {k : Fin a → ℤ} (hl : ∀ j : Fin a, (l j : ℤ) = m + k j) :
    rootCoeffEval (univ.val.map r) (genericSchur l) * (of fun i j : Fin a ↦ r i ^ (j : ℤ)).det =
      univ.prod r ^ m * (of fun i j : Fin a ↦ r i ^ k j).det := by
  have h_exponents :
      (of fun i j : Fin a ↦ r i ^ l j) = of fun i j : Fin a ↦ r i ^ ((m : ℤ) + k j) := by
    simp_rw [← zpow_natCast, hl]
  have h_vandermonde : vandermonde r = of fun i j : Fin a ↦ r i ^ (j : ℤ) := by
    simp [vandermonde]
  rw [← h_vandermonde, rootCoeffEval_genericSchur_mul_det, h_exponents, det_zpow_add h_ne,
    zpow_natCast]

open scoped Classical in
/-- Weyl's character formula for a twist of `weylRep κ.1 κ.2`, for `a` odd. At the places `v` with
`p v` the regular element `y` enters through `Φ v y⁻¹`, at the others through the transpose of
its conjugate. The character, times the `m`-th power of the norm of `det y`, is the product of the
values of `q σ` at the eigenvalues of `σ y`. Above each place one `q σ` gives `det ^ m`; the other
is a Schur polynomial whose exponents come from those, `u v`, of Weyl's formula. -/
lemma New.Variety.mul_trace_weylRep_eq_prod_rootCoeffEval {E : Type} [Field E] [CMType E] {a : ℕ}
    [NeZero a]
    (ha : Odd a) (κ : Weight E) (p : InfinitePlace E → Prop) {u : InfinitePlace E → Fin a → ℤ}
    (hu : ∀ (v : InfinitePlace E) (j : Fin a),
      u v j = κ.2 v + ↑(diagramWeight (rankAt fun _ : InfinitePlace E ↦ Fin a) κ.1 (v, j.rev) + j))
    {q : (E →+* ℂ) → MvPolynomial (Fin a) ℤ} {l : (E →+* ℂ) → Fin a → ℕ} {m : ℕ}
    (hl_pos : ∀ v : InfinitePlace E, p v → ∀ j : Fin a, (l (Φ v) j : ℤ) = m + (a - 1 - u v j.rev))
    (hq_pos : ∀ v : InfinitePlace E, p v → q (Φ v) = genericSchur (l (Φ v)))
    (hq_conj_pos : ∀ v : InfinitePlace E, p v → q (star (Φ v)) = (-.X 0) ^ m)
    (hl_neg : ∀ v : InfinitePlace E, ¬p v → ∀ j : Fin a, (l (star (Φ v)) j : ℤ) = m + u v j)
    (hq_neg : ∀ v : InfinitePlace E, ¬p v → q (Φ v) = (-.X 0) ^ m)
    (hq_conj_neg : ∀ v : InfinitePlace E, ¬p v → q (star (Φ v)) = genericSchur (l (star (Φ v))))
    {y : GL (Fin a) E} (hy : y.val.charpoly.Separable) :
    (∏ σ : E →+* ℂ, σ y.val.det) ^ m *
        (weylRep κ.1 κ.2 fun v : InfinitePlace E ↦
          if p v then y⁻¹.map (Φ v) else transposeGL (y.map (star (Φ v)))).trace =
      ∏ σ : E →+* ℂ, rootCoeffEval (y.val.charpoly.map σ).roots (q σ) := by
  -- Number the eigenvalues `r σ` of `σ y`, and the eigenvalues `x v` of the component at `v`.
  let r (σ : E →+* ℂ) : Fin a ↪ ℂ := numberedRoots σ y.val.charpoly
  have h_roots (σ : E →+* ℂ) : (y.val.charpoly.map σ).roots = univ.val.map (r σ) :=
    roots_eq_map_numberedRoots hy σ
  have h_ne (σ : E →+* ℂ) (i : Fin a) : r σ i ≠ 0 :=
    spectrum.ne_zero_of_mem_of_unit (mem_spectrum_of_isRoot_charpoly (isRoot_numberedRoots hy σ i))
  have h_det (σ : E →+* ℂ) : σ y.val.det = univ.prod (r σ) := by
    simp [RingHom.map_det, det_eq_prod_roots_charpoly, charpoly_map, h_roots, List.prod_ofFn]
  have hx_inj (v : InfinitePlace E) :
      Function.Injective fun i : Fin a ↦ if p v then (r (Φ v) i.rev)⁻¹ else r (star (Φ v)) i := by
    intro i j
    by_cases hv : p v <;> simp [hv]
  let x (v : InfinitePlace E) : Fin a ↪ ℂ :=
    ⟨fun i ↦ if p v then (r (Φ v) i.rev)⁻¹ else r (star (Φ v)) i, hx_inj v⟩
  have hx_root (v : InfinitePlace E) (i : Fin a) : IsRoot
      (if p v then y⁻¹.map (Φ v) else transposeGL (y.map (star (Φ v)))).val.charpoly (x v i) := by
    by_cases hv : p v
    · -- `coe_units_inv` and `IsRoot.def` are erased because with them simp rewrites the goal past
      -- `mem_spectrum_iff_isRoot_charpoly`.
      simpa [x, hv, -coe_units_inv, -IsRoot.def, ← mem_spectrum_iff_isRoot_charpoly] using
        isRoot_numberedRoots hy (Φ v) i.rev
    · simpa [x, hv] using isRoot_numberedRoots hy (star (Φ v)) i
  -- Multiply by the Vandermonde determinants of the `x v`, apply Weyl's formula, and compare the
  -- factors place by place.
  apply mul_right_cancel₀
    (prod_ne_zero_iff.mpr fun v (_hv : v ∈ univ) ↦ det_vandermonde_ne_zero_iff.mpr (x v).injective)
  -- Weyl's formula turns the trace times the Vandermonde determinants into a product over the
  -- places `v` of determinants in the `x v`, with the exponents `u v`.
  simp_rw [mul_assoc, trace_weylRep _ _ hx_root, ← hu]
  -- The other side is a product over the embeddings; they come in pairs `Φ v`, `star (Φ v)`.
  simp_rw [h_det, h_roots, prod_embeddings_eq_prod_pairs, ← prod_pow, ← prod_mul_distrib]
  refine prod_congr rfl fun v _ ↦ ?_
  rw [show vandermonde (x v) = of fun i j : Fin a ↦ x v i ^ (j : ℤ) by simp [vandermonde]]
  by_cases hv : p v
  · -- Both determinants in the inverted eigenvalues give the same factor `(∏ r) ^ (1 - a)`.
    have h_bialternant : rootCoeffEval (univ.val.map (r (Φ v))) (genericSchur (l (Φ v))) *
        (of fun i j : Fin a ↦ r (Φ v) i ^ (j : ℤ)).det = univ.prod (r (Φ v)) ^ m *
        (of fun i j : Fin a ↦ r (Φ v) i ^ (a - 1 - u v j.rev)).det :=
      rootCoeffEval_genericSchur_mul_det_zpow (h_ne (Φ v)) (hl_pos v hv)
    have h_rev (j : Fin a) : (a - 1 - j.rev : ℤ) = j := by simp [Fin.val_rev]
    simp only [hq_pos v hv, hq_conj_pos v hv, x, hv, ite_true, Function.Embedding.coeFn_mk, h_rev,
      map_pow, map_neg, det_inv_rev_zpow (h_ne (Φ v)), rootCoeffEval_X_zero_of_odd ha, neg_neg,
      prod_mul_distrib]
    -- What is left is `h_bialternant` times the factors that the two sides share.
    linear_combination
      -univ.prod (r (star (Φ v))) ^ m * univ.prod (r (Φ v)) ^ (1 - a : ℤ) * h_bialternant
  · have h_bialternant :
        rootCoeffEval (univ.val.map (r (star (Φ v)))) (genericSchur (l (star (Φ v)))) *
        (of fun i j : Fin a ↦ r (star (Φ v)) i ^ (j : ℤ)).det = univ.prod (r (star (Φ v))) ^ m *
        (of fun i j : Fin a ↦ r (star (Φ v)) i ^ u v j).det :=
      rootCoeffEval_genericSchur_mul_det_zpow (h_ne (star (Φ v))) (hl_neg v hv)
    simp only [hq_neg v hv, hq_conj_neg v hv, x, hv, ite_false, Function.Embedding.coeFn_mk,
      map_pow, map_neg, rootCoeffEval_X_zero_of_odd ha, neg_neg, prod_mul_distrib]
    linear_combination -univ.prod (r (Φ v)) ^ m * h_bialternant

/-- In the representation `weylRep κ.1 κ.2` of weight `κ` (`New.weylRep`), a family whose component
at `v` is the scalar `t ^ ε v` acts by a power of `t`: the exponent is the sum of the `ε v` times
the degree of the weight at `v`. -/
lemma New.Variety.weylRep_of_scalar {E : Type} [Field E] [NumberField E] {a : ℕ} (κ : Weight E)
    {t : ℂ} (ht : t ≠ 0) {ε : InfinitePlace E → ℤ} {g : InfinitePlace E → GL (Fin a) ℂ}
    (hg : ∀ v : InfinitePlace E, (g v).val = t ^ ε v • 1) :
    weylRep κ.1 κ.2 g =
      t ^ (∑ v : InfinitePlace E, ε v * (a * κ.2 v + ∑ h ∈ Finset.range a, h * κ.1 v h)) • 1 := by
  -- On each component the scalar `t ^ ε v` acts through the Schur functor by its degree; the
  -- exponents add up.
  simp [weylRep, hg, schur_smul, Units.smul_def, smul_smul, ← zpow_natCast, ← _root_.zpow_mul,
    ← DiscreteSeries.zpow_sum_of_ne_zero ht, ← zpow_add₀ ht, mul_add, sum_add_distrib, mul_assoc]

open scoped Classical in
/-- The complex embeddings of `QuadField d₀` are `s₀` and its conjugate. -/
lemma New.Variety.pair_star_eq_univ {d₀ : ℕ} [Fact (d₀ % 4 = 3)] (s₀ : QuadField d₀ →+* ℂ) :
    ({star s₀, s₀} : Finset (QuadField d₀ →+* ℂ)) = univ := by
  exact eq_univ_of_card _ (by simp [Embeddings.card, finrank_eq_two])

private lemma New.Variety.eq_star_or_eq {d₀ : ℕ} [Fact (d₀ % 4 = 3)] (s s₀ : QuadField d₀ →+* ℂ) :
    s = star s₀ ∨ s = s₀ := by
  classical
  simpa [← pair_star_eq_univ s₀] using mem_univ s

/-- Exactly one of `s` and its conjugate is `s₀`. -/
lemma New.Variety.conjugate_eq_iff_ne {d₀ : ℕ} [Fact (d₀ % 4 = 3)] (s s₀ : QuadField d₀ →+* ℂ) :
    ComplexEmbedding.conjugate s = s₀ ↔ s ≠ s₀ := by
  change star s = s₀ ↔ s ≠ s₀
  rcases eq_star_or_eq s s₀ with rfl | rfl <;> simp

open scoped Classical in
/-- An embedding of `E` restricts to `s₀` or to its conjugate. -/
lemma New.Variety.apply_eq_ite_comp_eq {E : Type} [Field E] {d₀ : ℕ} [Fact (d₀ % 4 = 3)]
    (i : QuadField d₀ →+* E) (s₀ : QuadField d₀ →+* ℂ) (σ : E →+* ℂ) (x : QuadField d₀) :
    σ (i x) = if σ.comp i = s₀ then s₀ x else star s₀ x := by
  have h_ne : star s₀ ≠ s₀ := by simp
  rw [← RingHom.comp_apply σ i x]
  rcases eq_star_or_eq (σ.comp i) s₀ with h_star | h_self
  · simp [h_star, h_ne]
  · simp [h_self]

open scoped Classical in
/-- An extension to `GL (Fin a) E` of the embedding of the unitary group at the infinite places:
`z` goes to `Φ v z` if `p v` holds, and to the inverse transpose of its conjugate if not. -/
noncomputable def New.Variety.extendedEmbedding {E : Type} [Field E] [CMType E] {a : ℕ}
    (p : InfinitePlace E → Prop) : GL (Fin a) E →* InfinitePlace E → GL (Fin a) ℂ :=
  MonoidHom.mk' (fun z v ↦ if p v then z.map (Φ v) else transposeGL (z⁻¹.map (star (Φ v))))
    (by simp +contextual [funext_iff, apply_ite, Units.ext_iff])

/-- The matrices of weight `κ` along `extendedEmbedding p`, twisted by the `-m`-th power of the
norm of the determinant. -/
noncomputable def New.Variety.twistedWeylMatrix {E : Type} [Field E] [CMType E] {a : ℕ}
    (κ : Weight E) (p : InfinitePlace E → Prop) (m : ℕ) :
    GL (Fin a) E →* Matrix (WeylIndex (Fin a) κ.1) (WeylIndex (Fin a) κ.1) ℂ where
  toFun z := (∏ σ : E →+* ℂ, σ z⁻¹.val.det) ^ m • weylRep κ.1 κ.2 (extendedEmbedding p z)
  map_one' := by simp
  map_mul' := by simp [prod_mul_distrib, smul_smul, mul_pow]

/-- The representation given by the matrices `twistedWeylMatrix κ p m`. -/
noncomputable def New.Variety.twistedWeylRep {E : Type} [Field E] [CMType E] {a : ℕ}
    (κ : Weight E) (p : InfinitePlace E → Prop) (m : ℕ) :
    Representation ℂ (GL (Fin a) E) (WeylIndex (Fin a) κ.1 → ℂ) :=
  toLinAlgEquiv'.toMonoidHom.comp (twistedWeylMatrix κ p m)

/-- For unitary `y`, `twistedWeylRep κ p m y` is the action of `ȳ` in weight `κ`. -/
lemma New.Variety.weightRep_entryConj_eq_twistedWeylRep {E : Type} [Field E] [CMType E] {a : ℕ}
    (κ : Weight E) (p : InfinitePlace E → Prop) (m : ℕ) (y : U (1 : Matrix (Fin a) (Fin a) E)) :
    (stdSpace E (Fin a)).weightRep κ.1 κ.2 (entryConj y) = twistedWeylRep κ p m y.val := by
  -- The determinant has norm one, and both branches of the embedding at `v` are `Φ v y`; on the
  -- other side `entryConj` and `stdSpace_weightRep_apply` each conjugate the entries once.
  have h_unitary : y.val.valᴴ * 1 * y.val.val = 1 := y.prop
  have h_norm (v : InfinitePlace E) :
      Φ v y.val.val.det * starRingEnd ℂ (Φ v y.val.val.det) = 1 := by
    simpa [mul_comm] using congrArg (fun M : Matrix (Fin a) (Fin a) E ↦ Φ v M.det) h_unitary
  have h_embedding : extendedEmbedding p y.val =
      fun v ↦ .map ((Φ v).comp (starRingEnd E)) (entryConj y).val := by
    ext v
    simp [extendedEmbedding, entryConj, invTransposeGL, transposeGL, starRingEnd_apply (R := E),
      apply_ite, Matrix.ite_apply, ← map_inv, inv_eq_left_inv y.prop]
  refine LinearMap.ext fun w ↦ (stdSpace_weightRep_apply (entryConj y) w).trans ?_
  simp [twistedWeylRep, twistedWeylMatrix, prod_embeddings_eq_prod_pairs, h_norm, h_embedding]

/-- Let `E` be a CM field with chosen embeddings `Φ v`, let `i : ℚ(i√d₀) →+* E`, and let `s₀` be a
complex embedding of ℚ(i√d₀). Let `p v` mean that `Φ v` extends `s₀`, and consider the
representation `twistedWeylRep κ p m` of `GL_a(E)` given by the matrices `twistedWeylMatrix κ p m`
for the weight `κ`. Then there is one integer `A` such that, for every `x` in `(QuadField d₀)ˣ`, the
scalar matrix `i(x̄)` acts by `s̄₀ x ^ (-A) * s₀ x ^ (-μ)`, where `μ` is `m * a` times the number of
infinite places of `E`. -/
lemma New.Variety.exists_twistedWeylRep_scalar {E : Type} [Field E] [CMType E] {a d₀ : ℕ}
    [Fact (d₀ % 4 = 3)] (i : QuadField d₀ →+* E) (s₀ : QuadField d₀ →+* ℂ) (κ : Weight E) (m : ℕ) :
    ∃ A : ℤ, ∀ x : (QuadField d₀)ˣ,
      twistedWeylRep κ (fun v : InfinitePlace E ↦ (Φ v).comp i = s₀) m
          (GeneralLinearGroup.scalar (Fin a) (star (x.map i))) =
        (star s₀ x ^ (-A) * s₀ x ^ (-(m * a * Core.numInfPlaces E : ℕ) : ℤ)) • 1 := by
  classical
  -- The twist gives `(s₀ x * star s₀ x)⁻¹ ^ μ`, and the weight gives `star s₀ x ^ B`.
  let p (v : InfinitePlace E) : Prop := (Φ v).comp i = s₀
  let ε (v : InfinitePlace E) : ℤ := if p v then 1 else -1
  let B : ℤ := ∑ v, ε v * (a * κ.2 v + ∑ h ∈ range a, h * κ.1 v h)
  set μ : ℕ := m * a * Core.numInfPlaces E with hμ
  refine ⟨μ - B, fun x ↦ ?_⟩
  set z : GL (Fin a) E := GeneralLinearGroup.scalar (Fin a) (star (x.map i)) with hz
  have h_embedding (v : InfinitePlace E) :
      (extendedEmbedding p z v).val = star s₀ x ^ ε v • 1 := by
    by_cases hv : (Φ v).comp i = s₀ <;>
      simp [extendedEmbedding, hz, ε, p, hv, apply_eq_ite_comp_eq i s₀, conjugate_eq_iff_ne,
        smul_one_eq_diagonal, ← map_inv]
  have h_weight : weylRep κ.1 κ.2 (extendedEmbedding p z) = star s₀ x ^ B • 1 :=
    weylRep_of_scalar κ (by simp) h_embedding
  have h_pair (v : InfinitePlace E) :
      starRingEnd ℂ (Φ v (i x)) * starRingEnd ℂ (star (Φ v) (i x)) = s₀ x * star s₀ x := by
    by_cases hv : (Φ v).comp i = s₀ <;>
      simp [hv, apply_eq_ite_comp_eq i s₀, conjugate_eq_iff_ne, mul_comm]
  have h_norm : ∏ σ : E →+* ℂ, starRingEnd ℂ (σ (i x)) =
      (s₀ x * star s₀ x) ^ Core.numInfPlaces E := by
    simp only [prod_embeddings_eq_prod_pairs, h_pair, Finset.prod_const, card_univ]
  have h_twist : (∏ σ : E →+* ℂ, σ z⁻¹.val.det) ^ m = (s₀ x * star s₀ x)⁻¹ ^ μ := by
    -- With `mul_inv_rev`, simp inverts the product in the other order, against the right side.
    simp [hz, prod_pow, h_norm, hμ, -_root_.mul_inv_rev, ← pow_mul, mul_comm, mul_left_comm,
      mul_assoc]
  have h_exponent :
      (s₀ x * star s₀ x)⁻¹ ^ μ * star s₀ x ^ B = star s₀ x ^ (-(μ - B)) * s₀ x ^ (-μ : ℤ) := by
    simp [zpow_sub₀, div_eq_mul_inv, mul_pow, mul_comm, mul_assoc]
  simp only [twistedWeylRep, twistedWeylMatrix, MonoidHom.comp_apply, MonoidHom.coe_mk,
    OneHom.coe_mk, p, h_weight, h_twist, smul_smul, h_exponent]
  simp

/-- Let `i` embed the imaginary quadratic field `QuadField d₀` in `E`, and let `s₀` be a complex
embedding of `QuadField d₀`. The representation `ξ` extends the weight `κ` to `GL (Fin a) E`. The
centre acts through the exponents `A`, with `A s₀ = μ`. The eigenvalues of the test eigenforms with
coefficients in `ξ` occur in the weights `z + μ`, for `z` a jump of `κ` at an embedding over `s₀`
(`New.Variety.OccursInWeight` with the parameter `N + 1`). -/
structure New.Variety.IsCoefficientSystem {E : Type} [Field E] [CMType E] {a d₀ : ℕ}
    [HasQuadSubfield d₀ E] (i : QuadField d₀ →+* E) (s₀ : QuadField d₀ →+* ℂ) (κ : Weight E)
    (ξ : Representation ℂ (GL (Fin a) E) (WeylIndex (Fin a) κ.1 → ℂ)) (μ N : ℕ)
    (A : (QuadField d₀ →+* ℂ) → ℤ) : Prop where
  /-- The central exponent at `s₀` is `μ`. -/
  exponent_self : A s₀ = μ
  /-- For unitary `y`, `ξ y` is the action of `ȳ` in weight `κ`. -/
  weightRep_entryConj (y : U (1 : Matrix (Fin a) (Fin a) E)) :
    (stdSpace E (Fin a)).weightRep κ.1 κ.2 (entryConj y) = ξ y.val
  /-- For `x` in `(QuadField d₀)ˣ`, the scalar `x̄` acts by `∏ s, s x ^ (-A s)`. -/
  map_scalar (x : (QuadField d₀)ˣ) :
    ξ (GeneralLinearGroup.scalar (Fin a) (star (x.map i))) =
      (∏ s : QuadField d₀ →+* ℂ, s x ^ (-A s)) • 1
  /-- The jumps of `κ` at embeddings over `s₀` are at least `-μ`. -/
  jump_add_nonneg {σ : E →+* ℂ} (hσ : σ.comp i = s₀) {z : ℤ} (hz : z ∈ jumps κ a σ) : 0 ≤ z + μ
  /-- Let `z` be a jump of `κ` at `σ` over `s₀`, for the given CM type. Let `Ψ` be any CM type with
  base place `v₀` whose only embedding over `s₀` is `σ`, at `v₀`. Then the eigenvalues of every
  test eigenform of neat level for `Ψ` occur in weight `z + μ`. -/
  occursInWeight {σ : E →+* ℂ} (hσ : σ.comp i = s₀) {z : ℤ} (hz : z ∈ jumps κ a σ)
    [Ψ : CMBase E] (hv₀ : Ψ.Φ v₀ = σ) (hΨ : ∀ v : InfinitePlace E, v ≠ v₀ → (Ψ.Φ v).comp i ≠ s₀)
    {𝔑 : 𝓞 E} (hN : IsNeat (Fin a) 𝔑) {φ : GL (Fin a) (𝔸f E) → WeylIndex (Fin a) κ.1 → ℂ}
    {θ : SafePlace 𝔑 → ℕ → ℂ} (h_form : IsTestEigenform 𝔑 ξ φ θ) :
    OccursInWeight a (N + 1) θ (z + μ).toNat

open scoped Classical in
/-- The trace of `twistedWeylRep κ p m` at `y⁻¹` is the left side of
`mul_trace_weylRep_eq_prod_rootCoeffEval`: the `m`-th power of the norm of `det y` times the trace
of `weylRep κ.1 κ.2` at the family that is `Φ v y⁻¹` where `p v` holds and the transpose of the
conjugate of `y` elsewhere. -/
private lemma New.Variety.trace_twistedWeylRep_inv {E : Type} [Field E] [CMType E] {a : ℕ}
    (κ : Weight E) (p : InfinitePlace E → Prop) (m : ℕ) (y : GL (Fin a) E) :
    (twistedWeylRep κ p m y⁻¹).trace ℂ (WeylIndex (Fin a) κ.1 → ℂ) =
      (∏ σ : E →+* ℂ, σ y.val.det) ^ m *
        (weylRep κ.1 κ.2 fun v : InfinitePlace E ↦
          if p v then y⁻¹.map (Φ v) else transposeGL (y.map (star (Φ v)))).trace := by
  change (Matrix.toLin' ((∏ σ : E →+* ℂ, σ y.val.det) ^ m • weylRep κ.1 κ.2 fun v ↦
    if p v then y⁻¹.map (Φ v) else transposeGL (y.map (star (Φ v))))).trace ℂ _ = _
  rw [trace_toLin'_eq, trace_smul, smul_eq_mul]

/-- Let `a` be odd, `i` an embedding of the imaginary quadratic field `QuadField d₀` in `E` and `s₀`
a complex embedding of `QuadField d₀`. A weight `κ` extends to a representation `ξ` of
`GL (Fin a) E` on which the scalars from `(QuadField d₀)ˣ` (through `i`) act through exponents `A`
with `A s₀ = μ`, and whose test eigenforms occur in the weights `z + μ` for `z` a jump of `κ` at an
embedding over `s₀`, for some `N` (`New.Variety.IsCoefficientSystem`). The proof compares traces
directly and does not pass through automorphic representations of `GL_n`.

In the literature the same occurrence follows from the description, due to Labesse and to
Moeglin–Waldspurger, of automorphic representations of unitary groups via `GL_n`. -/
lemma New.Variety.exists_isCoefficientSystem {E : Type} [Field E] [CMType E] {a d₀ : ℕ}
    [HasQuadSubfield d₀ E] (ha : Odd a) (i : QuadField d₀ →+* E) (s₀ : QuadField d₀ →+* ℂ)
    (κ : Weight E) :
    ∃ (ξ : Representation ℂ (GL (Fin a) E) (WeylIndex (Fin a) κ.1 → ℂ)) (μ N : ℕ)
      (A : (QuadField d₀ →+* ℂ) → ℤ), IsCoefficientSystem i s₀ κ ξ μ N A := by
  classical
  -- Twist the representation of weight `κ` so that its character is a product over all embeddings
  -- `σ` of polynomials `q σ` in the eigenvalues: a Schur polynomial with natural exponents `l σ` if
  -- `σ` extends `s₀`, and `det ^ m` if not. Then `occursInWeight_of_isTestEigenform` applies.
  have ha_ne : NeZero a := NeZero.of_pos ha.pos
  -- `u v` are the exponents in Weyl's formula, `k σ` the exponents for the eigenvalues at `σ`;
  -- adding a large `m` turns them into natural numbers `l σ`.
  let u (v : InfinitePlace E) (j : Fin a) : ℤ :=
    κ.2 v + ↑(diagramWeight (rankAt fun _ : InfinitePlace E ↦ Fin a) κ.1 (v, j.rev) + j)
  let k (σ : E →+* ℂ) (j : Fin a) : ℤ :=
    if σ = Φ (.mk σ) then a - 1 - u (.mk σ) j.rev else u (.mk σ) j
  obtain ⟨m, hm_bound⟩ := Finite.exists_le (Int.natAbs ∘ k.uncurry)
  let l (σ : E →+* ℂ) (j : Fin a) : ℕ := (m + k σ j).toNat
  have hl (σ : E →+* ℂ) (j : Fin a) : (l σ j : ℤ) = m + k σ j := by
    have h_abs : (k σ j).natAbs ≤ m := hm_bound (σ, j)
    exact Int.toNat_of_nonneg (by omega)
  let p (v : InfinitePlace E) : Prop := (Φ v).comp i = s₀
  let q (σ : E →+* ℂ) : MvPolynomial (Fin a) ℤ :=
    if σ.comp i = s₀ then genericSchur (l σ) else (-.X 0) ^ m
  let ξ : Representation ℂ (GL (Fin a) E) (WeylIndex (Fin a) κ.1 → ℂ) := twistedWeylRep κ p m
  -- The exponents and polynomials at `Φ v` and at its conjugate, as
  -- `mul_trace_weylRep_eq_prod_rootCoeffEval` needs them.
  have hl_pos (v : InfinitePlace E) (_hv : p v) (j : Fin a) :
      (l (Φ v) j : ℤ) = m + (a - 1 - u v j.rev) := by simp [hl, k]
  have hq_conj_pos (v : InfinitePlace E) (hv : p v) : q (star (Φ v)) = (-.X 0) ^ m := by
    simp [q, show (Φ v).comp i = s₀ from hv]
  have hl_neg (v : InfinitePlace E) (_hv : ¬p v) (j : Fin a) :
      (l (star (Φ v)) j : ℤ) = m + u v j := by simp [hl, k]
  have hq_conj_neg (v : InfinitePlace E) (hv : ¬p v) :
      q (star (Φ v)) = genericSchur (l (star (Φ v))) := by
    simp [q, show ¬(Φ v).comp i = s₀ from hv, conjugate_eq_iff_ne]
  have h_char (y : GL (Fin a) E) (hy : y.val.charpoly.Separable) :
      (ξ y⁻¹).trace ℂ (WeylIndex (Fin a) κ.1 → ℂ) =
        ∏ σ, rootCoeffEval (y.val.charpoly.map σ).roots (q σ) := by
    rw [trace_twistedWeylRep_inv κ p m y]
    exact mul_trace_weylRep_eq_prod_rootCoeffEval ha κ p (u := u) (l := l) (fun _ _ ↦ rfl) hl_pos
      (fun _ hv ↦ ite_eq_left hv) hq_conj_pos hl_neg (fun _ hv ↦ ite_eq_right hv) hq_conj_neg hy
  let μ : ℕ := m * a * Core.numInfPlaces E
  obtain ⟨A, h_scalar⟩ := exists_twistedWeylRep_scalar (a := a) i s₀ κ m
  -- Each jump at `σ` is some `k σ j = l σ j - m`, so adding `μ` gives the weight in
  -- `occursInWeight_of_isTestEigenform`.
  have h_jump (σ : E →+* ℂ) : ∀ z ∈ jumps κ a σ, ∃ j : Fin a,
      z + μ = (m * (a - 1 + a * (Core.numInfPlaces E - 1)) + l σ j : ℕ) := by
    refine Multiset.forall_mem_map_iff.mpr fun n hn ↦ ?_
    let n' : Fin a := ⟨n, Multiset.mem_range.mp hn⟩
    refine ⟨if σ = Φ (.mk σ) then n' else n'.rev, ?_⟩
    simp [hl, k, u, μ, n', diagramWeight_apply, Fintype.card_pos]
    -- What is left is index arithmetic with products of casts, which `omega` cannot expand;
    -- `grind` closes it once the context is cleared, and does not finish with the whole context.
    clear * - hn
    grind
  refine ⟨ξ, μ, ∑ σ, (q σ).totalDegree, fun s ↦ if s = s₀ then μ else A,
    { exponent_self := ite_eq_left rfl
      weightRep_entryConj := weightRep_entryConj_eq_twistedWeylRep κ _ m
      map_scalar := fun x ↦ ?_
      jump_add_nonneg := fun _hσ z hz ↦ ?_
      occursInWeight := fun hσ z hz ↦ ?_ }⟩
  · rw [h_scalar, ← pair_star_eq_univ s₀]
    simp [μ, mul_comm]
  · obtain ⟨j, hj⟩ := h_jump _ z hz
    omega
  · obtain ⟨j, hj⟩ := h_jump _ z hz
    rintro Ψ rfl hΨ 𝔑 hN φ θ h_form
    rw [hj, Int.toNat_natCast]
    refine occursInWeight_of_isTestEigenform ha h_char (ite_eq_left hσ) (ite_eq_right ?_)
      (fun v hv ↦ ite_eq_right (hΨ v hv)) hN
      h_form j
    simpa [conjugate_eq_iff_ne] using hσ
