import Lib.General.Geometry.GaloisCovers
import Lib.LocalGL.Shintani.CosetDescent

/-!
# Label characters Ξ_c: orthonormality, central idempotents and twisting by χ∘det

Let k be a finite field, and let T be an injective multiplicative character of an algebraically
closed extension K of k. A label of degree r (`New.IsLabel`) is a monic squarefree polynomial c of
degree r with c(0) ≠ 0. The character Ξ_c = `New.labelChar` T c is the product in `New.Hall`
(parabolic induction) of Green's functions τ_P = `New.greenTau` T P over the irreducible factors P
of c. The file shows that the Ξ_c are orthonormal irreducible characters of GL_r(k). It then studies
the elements e_c = `New.labelIdem` n c of ℂ[GL_n(k)] formed from Ξ_c (0 if c is not a label of
degree |n|), and computes the twist of Ξ_c by χ∘det.

## Main definitions and results

* `New.rankPart_labelChar`, `New.rankInner_labelChar`: Ξ_c lives in dimension r, and the Ξ_c are
  orthonormal.
* `New.IsLabel.isIrreducibleChar_labelChar`: Ξ_c is an irreducible character of GL_r(k).
  `New.lift_labelChar_self` says in the form `New.Lift` that Ξ_c is a genuine character, an
  ℕ-combination of characters. It does not record irreducibility.
* `New.labelIdem_orthogonal`: the e_c are orthogonal idempotents.
* `New.hyperplaneSum_mul_labelIdem`: let l be a nonzero vector. Then e_c kills the sum of χ(det h)⁻¹
  h over the invertible h = 1 + u lᵀ, when the element of kˣ naming χ (`New.charName`) is not a root
  of c.
* `New.tupleIdem`, `New.isCentralProj_tupleIdem`, `New.tupleIdem_orthogonal`: the tensor products
  ⊗_w e_{c_w} over a finite family of fields k_w are orthogonal central idempotents.
* `New.evalGL_labelChar_mul_det`: multiplying the character Ξ_c by `χ ∘ det` scales the roots of `c`
  by the unit x_χ of `k` that corresponds to `χ` under `T`.

Notions from other files:
* `New.charName`: For T injective, the group isomorphism χ ↦ x_χ from the multiplicative characters
  of k to k^×, inverse to a ↦ θ_a restricted to k, with θ_a taken for Q = |k|.
* `New.Hall.rankInner`: For complex functions F, H on similarity classes, the average over GL_n(k)
  of the conjugate of F times H.
* `New.IsIrreducibleChar`: `f` is an irreducible character, stated as three conditions: (a) `f` is a
  character, (b) `New.classInner f f = 1`, and (c) for every class function `h` and every `y`,
  `f 1 * New.classInner f (h (· * y)) = New.classInner f h * f y`.
* `New.IsFaithfulMulChar`: K is algebraically closed and the character T of Kˣ is injective.
* `New.thetaChar`: The character θ_x = T^a of K, where a is a chosen natural number with
  T(x) = exp(2πi/(Q−1))^a.

## Relation to the literature

Known; see `Lib.LocalGL.Green.TauFunctions` for sources.
-/

/-- For `v ≠ 0`, the map `u ↦ u vᵀ` from vectors to matrices is injective. -/
private lemma Matrix.vecMulVec_left_injective_of_ne_zero {m p R : Type*} [Field R] {v : p → R}
    (hv : v ≠ 0) : Function.Injective fun u : m → R ↦ Matrix.vecMulVec u v := by
  intro u u' h_eq
  obtain ⟨j, hj⟩ : ∃ j : p, v j ≠ 0 := Function.ne_iff.mp hv
  funext i
  simpa [Matrix.vecMulVec_apply, hj] using congrFun (congrFun h_eq i) j

/-- For a linear map `g` from a field `R` to itself, `g 1` (its determinant) is minus the
constant coefficient of its characteristic polynomial. -/
private lemma LinearMap.apply_one_eq_neg_charpoly_coeff_zero {R : Type*} [Field R]
    (g : Module.End R R) : g 1 = -(LinearMap.charpoly g).coeff 0 := by
  simp [← LinearMap.det_ring, LinearMap.det_eq_sign_charpoly_coeff]

namespace New

/-!
## Orthonormality and irreducibility of Green's characters

Most proofs go by induction on the irreducible factors of c. Orthonormality uses `New.Hall.skew`,
which is adjoint to multiplication by τ_P and is a derivation.
-/

section LabelCharacters

open Polynomial Hall

variable {k K n : Type*} {r : ℕ} [Field k] [Finite k] [Field K] [Algebra k K] (T : MulChar K ℂ)
  [IsFaithfulMulChar K T] [Fintype n] [DecidableEq n] {c P : k[X]}

/-- Let K be an algebraically closed field over the finite field k, with an injective multiplicative
character T : K → ℂ. For a multiplicative character χ of k, let a ∈ kˣ be its name under T, the
inverse of the isomorphism a ↦ θ_a restricted to k, with θ_a formed with Q = |k|. Then Green's class
function Ξ_{X − a} equals χ∘det on similarity classes of dimension 1 and is zero on all other
classes.

A case of Green's identification of his rank-one characters with the multiplicative characters of
`k`. -/
lemma labelChar_X_sub_C (χ : MulChar k ℂ) :
    labelChar T (X - C (charName T χ).val : k[X]) = (detChar χ).rankPart 1 := by
  -- The left side is minus the rank `1` part of `greenCuspidal k θ`, where `θ` extends `χ`.
  let θ : MulChar K ℂ := thetaChar T (Nat.card k) (algebraMap k K (charName T χ))
  have h_tau : labelChar T (X - C (charName T χ).val : k[X]) =
      (-1 : ℂ) • (greenCuspidal k θ).rankPart 1 := by
    rw [labelChar_eq_greenTau T (irreducible_X_sub_C _) (monic_X_sub_C _), greenTau,
      natDegree_X_sub_C, chosenRoot_X_sub_C, pow_one, pow_one]
  rw [h_tau]
  ext m g
  obtain hm | rfl : m ≠ 1 ∨ m = 1 := ne_or_eq m 1
  · simp [hm]
  -- In rank `1`, `greenCuspidal k θ = -brauerLift k θ`: both `greenCuspidal k θ` and
  -- `1 - constOne` vanish in rank `0`, so their product `greenCuspidal k θ + brauerLift k θ`
  -- vanishes in rank `1`.
  have h_rank_one : greenCuspidal k θ (simClassOf g) = -brauerLift k θ (simClassOf g) := by
    simpa [mul_sub, add_eq_zero_iff_eq_neg] using
      mul_apply_eq_zero_of_dim_lt (greenCuspidal_eq_zero_of_dim_lt_one θ)
        (one_sub_constOne_pow_apply_eq_zero 1) (simClassOf g) (by simp)
  -- The characteristic polynomial is linear, so `brauerLift` has a single term.
  have h_linear : g.charpoly = X + C (g.charpoly.coeff 0) :=
    g.charpoly_monic.eq_X_add_C (by simp [g.charpoly_natDegree])
  have h_roots : g.charpoly.aroots K = {algebraMap k K (-g.charpoly.coeff 0)} := by
    conv_lhs => rw [h_linear]
    simp [aroots]
  -- (`map_neg` and `map_mul` are left out so that `thetaChar_charName` applies to the argument)
  simp [h_rank_one, h_roots, detChar, θ, -map_neg, -map_mul, thetaChar_charName]

/-- A polynomial over the finite field `k` splits over `k` if each of its roots in the
algebraically closed field `K` is fixed by `x ↦ x ^ q`, where `q` is the order of `k`. -/
lemma splits_of_forall_root_pow_card_eq [IsAlgClosed K]
    (h_roots_fixed : ∀ x : K, aeval x c = 0 → x ^ Nat.card k = x) : c.Splits := by
  -- It suffices that each root `x` lies in `k`, that is, that its minimal polynomial is linear.
  refine .of_splits_map_of_injective (algebraMap k K).injective (IsAlgClosed.splits _)
    fun x hx_mem ↦ ?_
  obtain ⟨hc_ne, hx_root⟩ : c ≠ 0 ∧ aeval x c = 0 := mem_aroots.mp hx_mem
  have hx_fixed : x ^ Nat.card k ^ 1 = x := by rw [pow_one, h_roots_fixed x hx_root]
  have h_irred : Irreducible (minpoly k x) :=
    minpoly.irreducible (IsAlgebraic.isIntegral ⟨c, hc_ne, hx_root⟩)
  have h_deg_dvd : (minpoly k x).natDegree ∣ 1 :=
    (root_pow_card_pow_eq_self_iff h_irred (minpoly.aeval k x)).mp hx_fixed
  exact minpoly.natDegree_eq_one_iff.mp (Nat.dvd_one.mp h_deg_dvd)

/-- A label `c` of degree `r` that splits over `k` is the product of the `X - charName T (χ i)`
for some `r` multiplicative characters `χ i` of `k`. -/
lemma IsLabel.exists_eq_prod_charName_of_splits (hc : IsLabel r c) (h_splits : c.Splits) :
    ∃ χ : Fin r → MulChar k ℂ, c = ∏ i : Fin r, (X - C (charName T (χ i) : k)) := by
  -- Induct on the irreducible factors. Each factor `P` splits, so it is `X - a` with `a ≠ 0`,
  -- and every unit `a` is the name of a character.
  refine hc.induction_irreducible_mul K (fun _ ↦ ⟨1, by simp⟩)
    (fun P r' c _ hP_monic hP_irred hP_coeff _ ih h_mul_splits ↦ ?_) h_splits
  obtain ⟨hP_splits, hc_splits⟩ : (P.Splits ∨ c = 0) ∧ (c.Splits ∨ P = 0) :=
    splits_mul'.mp h_mul_splits
  obtain ⟨χ, rfl⟩ := ih (hc_splits.resolve_right hP_irred.ne_zero)
  have hP_deg : P.natDegree = 1 :=
    (hP_splits.resolve_right (monic_prod_X_sub_C _ _).ne_zero).natDegree_eq_one_of_irreducible
      hP_irred
  have hP_linear : P = X + C (P.coeff 0) := hP_monic.eq_X_add_C hP_deg
  rw [hP_deg, hP_linear]
  -- The name of the new character is `-P(0)`.
  refine ⟨Fin.append ![(charName T).symm (-Units.mk0 (P.coeff 0) hP_coeff)] χ, ?_⟩
  simp [Fin.prod_univ_add]

/-- `IsLabel.exists_eq_prod_charName_of_splits` with the splitting of `c` tested on its roots in
`K`: each is fixed by `x ↦ x ^ q`, where `q` is the order of `k`. -/
lemma IsLabel.exists_eq_prod_charName_of_root_pow_card_eq (hc : IsLabel r c)
    (h_roots_fixed : ∀ x : K, aeval x c = 0 → x ^ Nat.card k = x) :
    ∃ χ : Fin r → MulChar k ℂ, c = ∏ i : Fin r, (X - C (charName T (χ i) : k)) :=
  hc.exists_eq_prod_charName_of_splits T (splits_of_forall_root_pow_card_eq h_roots_fixed)

/-- For a label `c` of degree `r`, the character `New.labelChar T c` lives in dimension `r`: its
part of rank `r` is the whole of it. -/
lemma rankPart_labelChar (hc : IsLabel r c) : (labelChar T c).rankPart r = labelChar T c := by
  refine hc.induction_irreducible_mul K (Hall.ext (by simp))
    fun P r c _ξ hP_monic hP_irred _hP_coeff _hP_root ih ↦ Hall.ext fun m g ↦ ?_
  rw [map_mul, labelChar_eq_greenTau T hP_irred hP_monic, rankPart, ite_eq_left_iff,
    mul_simClassOf]
  intro h_dim_ne
  -- In a term of the product at `g`, the dimensions of the subspace `U` and of the quotient add up
  -- to that of `g`; so one differs from `P.natDegree` or the other from `r`, and a factor vanishes.
  refine (finsum_eq_zero_of_forall_eq_zero fun U ↦ ?_).symm
  have h_dim_add :
      (simClassOf U.endOnQuot).dim + (simClassOf U.endOnSub).dim = (simClassOf g).dim := by
    simpa only [dim_simClassOf] using U.val.finrank_quotient_add_finrank
  by_cases h_sub : (simClassOf U.endOnSub).dim = P.natDegree
  · rw [← ih, rankPart, ite_eq_right (by omega), mul_zero]
  · rw [greenTau_eq_zero_of_dim_ne _ h_sub, zero_mul]

/-- Let K be an algebraically closed field over the finite field k, with an injective multiplicative
character T : K → ℂ. A label of degree d is a monic squarefree polynomial of degree d with nonzero
constant term. Let c be a label of degree r, and P an irreducible label of degree d that does not
divide c. Then skewing Ξ_c by τ_P in dimension d gives zero: for every class a, the average over
b ∈ GL_d(k) of conj τ_P(b) times the block average of Ξ_c at (a, b) is 0, where the block average is
the mean, over the corner block x, of Ξ_c at the block triangular matrix with diagonal blocks a, b
and corner x. Here τ_P is Green's class function, (−1)^d times the dimension-d part of Green's
cuspidal function, and Ξ_c is the parabolic-induction product of the τ_Q over the irreducible
factors Q of c. -/
lemma skew_greenTau_labelChar_eq_zero (hc : IsLabel r c) {d : ℕ} (hP : Irreducible P)
    (hP_label : IsLabel d P) (h_not_dvd : ¬P ∣ c) :
    skew d (greenTau T P) (labelChar T c) = 0 := by
  -- Induct on the factors of `c`, using that `skew d (greenTau T P)` is a derivation.
  obtain ⟨hP_monic, -, rfl, hP_coeff⟩ := hP_label
  have h_deriv (F H : Hall k) : skew P.natDegree (greenTau T P) (F * H) =
      skew P.natDegree (greenTau T P) F * H + F * skew P.natDegree (greenTau T P) H :=
    skew_mul isCuspidal_greenTau hP.natDegree_pos.ne'
  refine hc.induction_irreducible_mul K (fun _ ↦ ?_)
    (fun Q _ c _ hQ_monic hQ_irred hQ_coeff _ ih h_not_dvd_mul ↦ ?_) h_not_dvd
  · -- A derivation kills `1`.
    simpa only [map_one, mul_one, one_mul, left_eq_add] using h_deriv 1 1
  · -- For a factor `Q ≠ P` it kills `greenTau T Q`, which is orthogonal to `greenTau T P`.
    have h_ne : P ≠ Q := fun h_eq ↦ h_not_dvd_mul (h_eq.dvd.mul_right c)
    have h_skew_Q : skew P.natDegree (greenTau T P) (greenTau T Q) = 0 := by
      rw [skew_of_isCuspidal isCuspidal_greenTau hP.natDegree_pos.ne',
        (rankInner_greenTau hP hP_coeff hP_monic).left Q hQ_irred hQ_monic hQ_coeff,
        ite_eq_right h_ne, zero_smul]
    rw [map_mul, labelChar_eq_greenTau T hQ_irred hQ_monic, h_deriv, h_skew_Q,
      ih fun h_dvd ↦ h_not_dvd_mul (h_dvd.mul_left Q), zero_mul, mul_zero, add_zero]

/-- Let T be faithful (`New.IsFaithfulMulChar`) and c a label of degree r with c(1) ≠ 0. Then
⟨Ξ_c, A * 1⟩ = ⟨Ξ_c, A⟩ on GL_r(k) for every class function A, where * is parabolic induction and 1
the constant function. -/
lemma rankInner_labelChar_mul_constOne (hc : IsLabel r c) (h_eval_one : c.eval 1 ≠ 0) (A : Hall k) :
    rankInner r (labelChar T c) (A * constOne) = rankInner r (labelChar T c) A := by
  refine hc.induction_irreducible_mul K (fun _ A ↦ by simp [rankInner])
    (fun P r c _ hP_monic hP_irred hP_coeff _ ih h_one A ↦ ?_) h_eval_one A
  obtain ⟨hP_one, hc_one⟩ : P.eval 1 ≠ 0 ∧ c.eval 1 ≠ 0 := by simpa using h_one
  -- Move the factor `greenTau T P` to the other side, where it acts as `skew`.
  rw [map_mul, labelChar_eq_greenTau T hP_irred hP_monic,
    rankInner_mul_eq_rankInner_skew greenTau_eq_zero_of_dim_ne,
    rankInner_mul_eq_rankInner_skew greenTau_eq_zero_of_dim_ne]
  -- `skew` is a derivation (`skew_mul`) that kills `constOne`, as `1` is not a root of `P`.
  have h_skew_mul_constOne : skew P.natDegree (greenTau T P) (A * constOne) =
      skew P.natDegree (greenTau T P) A * constOne := by
    rw [skew_mul isCuspidal_greenTau hP_irred.natDegree_pos.ne',
      (rankInner_greenTau hP_irred hP_coeff hP_monic).right hP_one, mul_zero, add_zero]
  rw [h_skew_mul_constOne, ih hc_one]

open scoped Classical in
/-- Orthonormality: let T : K → ℂ be an injective multiplicative character of an algebraically
closed field K over the finite field k, and let c, c' be labels of degree r, i.e. monic squarefree
polynomials over k of degree r with nonzero constant term. Ξ_c is the product, by parabolic
induction, of Green's class functions τ_P over the monic irreducible factors P of c. Then the
average over GL_r(k) of conj Ξ_c · Ξ_{c'} (`rankInner r`) is 1 if c = c' and 0 otherwise.

A case of Green's theorem that his characters of general linear groups over a finite field are
irreducible and distinct: the class functions Ξ_c attached to labels of one degree are orthonormal.

This corresponds to the Deligne–Lusztig orthogonality formula, restricted to GL_r and to the class
functions Ξ_c of labels of degree r, which are defined by Green's formula rather than by
Deligne–Lusztig induction. -/
lemma rankInner_labelChar (hc : IsLabel r c) (c' : k[X]) (hc' : IsLabel r c') :
    rankInner r (labelChar T c) (labelChar T c') = if c = c' then 1 else 0 := by
  -- Induct on the factors of `c`. A factor `greenTau T P` moves to the right as the derivation
  -- `skew`, which removes `P` from `c'` if `P ∣ c'` and gives `0` otherwise.
  refine hc.induction_irreducible_mul K (fun c' hc' ↦ ?_)
    (fun P r c _ hP_monic hP_irred hP_coeff _ ih c' hc' ↦ ?_) c' hc'
  · obtain ⟨hc'_monic, -, hc'_deg, -⟩ := hc'
    obtain rfl : c' = 1 := hc'_monic.natDegree_eq_zero.mp hc'_deg
    simp [rankInner]
  have hP_label : IsLabel P.natDegree P := ⟨hP_monic, hP_irred.squarefree, rfl, hP_coeff⟩
  rw [map_mul, labelChar_eq_greenTau T hP_irred hP_monic,
    rankInner_mul_eq_rankInner_skew greenTau_eq_zero_of_dim_ne]
  rcases em' (P ∣ c') with h_not_dvd | h_dvd
  · rw [skew_greenTau_labelChar_eq_zero T hc' hP_irred hP_label h_not_dvd,
      ite_eq_right fun h_eq ↦ h_not_dvd ⟨c, h_eq.symm⟩]
    simp [rankInner, finMean]
  · obtain ⟨c'', rfl⟩ := h_dvd
    obtain ⟨h_monic, h_squarefree, h_deg, h_coeff⟩ := hc'
    have hc''_monic : c''.Monic := hP_monic.of_mul_monic_left h_monic
    have hc''_label : IsLabel r c'' := by
      rw [hP_monic.natDegree_mul hc''_monic, add_right_inj] at h_deg
      rw [mul_coeff_zero] at h_coeff
      exact ⟨hc''_monic, h_squarefree.of_mul_right, h_deg, right_ne_zero_of_mul h_coeff⟩
    have h_not_dvd : ¬P ∣ c'' :=
      hP_irred.isRelPrime_iff_not_dvd.mp (squarefree_mul_iff.mp h_squarefree).left
    have h_norm : rankInner P.natDegree (greenTau T P) (greenTau T P) = 1 := by
      rw [(rankInner_greenTau hP_irred hP_coeff hP_monic).left P hP_irred hP_monic hP_coeff,
        ite_eq_left rfl]
    -- Of the two terms of `skew_mul`, the one that acts on `labelChar T c''` vanishes.
    have h_skew : skew P.natDegree (greenTau T P) (labelChar T (P * c'')) = labelChar T c'' := by
      rw [map_mul, labelChar_eq_greenTau T hP_irred hP_monic,
        skew_mul isCuspidal_greenTau hP_irred.natDegree_pos.ne',
        skew_greenTau_labelChar_eq_zero T hc''_label hP_irred hP_label h_not_dvd,
        skew_of_isCuspidal isCuspidal_greenTau hP_irred.natDegree_pos.ne', h_norm, one_smul,
        one_mul, mul_zero, add_zero]
    rw [h_skew, ih c'' hc''_label]
    simp only [mul_right_inj' hP_irred.ne_zero]

/-- This is a case of Green's theorem: let K be an algebraically closed field over the finite field
k, with an injective multiplicative character T : K → ℂ. Let c be a label of degree |n|, i.e. a
monic squarefree polynomial of degree |n| with nonzero constant term. Then Green's class function
Ξ_c, evaluated on GL_n(k), is an irreducible character in the sense of `IsIrreducibleChar`, which
also requires that class functions act by scalars. Ξ_c is the parabolic-induction product of τ_P
over the monic irreducible factors P of c. -/
lemma IsLabel.isIrreducibleChar_labelChar (hc : IsLabel (Fintype.card n) c) :
    IsIrreducibleChar ((labelChar T c).evalGL (n := n)) := by
  -- `labelChar T c` is a virtual character, as it has a lift over `ℤ` along `k/k`: the Brauer lift
  -- has one (`exists_lift_brauerLift`), and each `greenTau T P` and their products are built
  -- from it.
  obtain ⟨F, hF⟩ : ∃ F : Hall k, Lift ℤ (labelChar T c) F := by
    refine hc.induction_irreducible_mul K ⟨1, by simp⟩
      fun P _r c _ξ hP_monic hP_irred _hP_coeff _hP_root ⟨F, hF⟩ ↦ ?_
    obtain ⟨G, hG⟩ : ∃ G : Hall k, Lift ℤ (greenTau T P) G :=
      ⟨_, (exists_lift_brauerLift ..).choose_spec.rankPart_mulMoebius_mul_constOne⟩
    rw [map_mul, labelChar_eq_greenTau T hP_irred hP_monic]
    exact ⟨G * F, hG.mul hF⟩
  have h_virtual : (labelChar T c).evalGL ∈ virtualChars ℤ (GL n k) := hF.evalGL_mem_virtualChars
  have h_norm : classInner ((labelChar T c).evalGL (n := n)) (labelChar T c).evalGL = 1 := by
    simp [classInner_evalGL, rankInner_labelChar T hc c hc]
  have h_degree : 0 ≤ ((labelChar T c).evalGL (n := n) 1).re := (labelChar_degree_bounds K hc).1
  -- With the function itself as test function: norm `1`, a value at `1` with nonnegative real part
  -- and integer inner products with all characters make it irreducible.
  exact (isIrreducibleChar_and_mem_virtualChars_and_exists_mul ℤ isClassFunction_evalGL).left
    (labelChar T c).evalGL
    isClassFunction_evalGL (h_norm.trans_ne one_ne_zero) h_norm h_degree
    fun χ hχ _ _ ↦ hχ.exists_classInner_eq h_virtual

/-- Green's function with label `c` is a character of `GL n k` for every `n`. -/
lemma IsLabel.isChar_labelChar (hc : IsLabel r c) : IsChar ((labelChar T c).evalGL (n := n)) := by
  -- `labelChar T c` is an irreducible character in dimension `r` and vanishes in the others.
  obtain rfl | h_card_ne := eq_or_ne (Fintype.card n) r
  · exact (hc.isIrreducibleChar_labelChar (n := n) T).left
  · have h_zero : (labelChar T c).evalGL (n := n) = 0 := by
      rw [← rankPart_labelChar T hc]
      funext g
      simp [Hall.evalGL, h_card_ne]
    simpa [h_zero] using isChar_of_mem_virtualChars (zero_mem _)

/-- Green's function with label `c` lifts to itself over `ℕ` along the trivial extension `k/k`. This
is `IsLabel.isChar_labelChar` in terms of `Lift`: for each m, Ξ_c on GL_m(k) is an ℕ-combination of
characters. -/
lemma lift_labelChar_self (hc : IsLabel r c) : Lift ℕ (labelChar T c) (labelChar T c) := by
  intro m
  exact hasCommonLift_of_gal_trivial Subsingleton.eq_one
    (hc.isChar_labelChar (n := Fin m) T).mem_virtualChars fun g ↦ by simp

/-- If x_χ = `New.charName` T χ is not a root of the label c, then the skewing operator of the
character χ of GL_1(k) kills Ξ_c. -/
lemma skew_detChar_labelChar_eq_zero (hc : IsLabel r c) {χ : MulChar k ℂ}
    (h_not_root : c.eval (charName T χ : k) ≠ 0) :
    skew 1 ((detChar χ).rankPart 1) (labelChar T c) = 0 := by
  -- `(detChar χ).rankPart 1` is `greenTau T P` for the linear `P = X - charName T χ`.
  let a : k := charName T χ
  have h_irred : Irreducible (X - C a) := irreducible_X_sub_C a
  have h_label : IsLabel 1 (X - C a) :=
    ⟨monic_X_sub_C a, h_irred.squarefree, natDegree_X_sub_C a, by simp [a]⟩
  rw [← labelChar_X_sub_C T, labelChar_eq_greenTau T h_irred (monic_X_sub_C a)]
  exact skew_greenTau_labelChar_eq_zero T hc h_irred h_label (mt dvd_iff_isRoot.mp h_not_root)

end LabelCharacters

/-!
## Label idempotents and hyperplane sums

For a polynomial `c` over `k`, `New.labelIdem n c` is the element
`e_c = ∑ (Ξ_c(1) / |G|) · conj Ξ_c(g) · g` of `ℂ[G]`, `G = GL_n(k)`, where `Ξ_c` is Green's
character with label `c` (`New.labelChar`); it is `0` unless `c` is a label of degree `|n|`.
-/

section LabelIdempotents

open Matrix Finset Hall LinearMap Function Submodule MonoidAlgebra Representation

attribute [local instance low] Fintype.ofFinite

variable {n ι : Type _} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι] {k : Type _}
  [Field k] [Finite k]

/-- Each polynomial c over k gives an element e_c of ℂ[G], where G = GL_n(k). If c is a label of
degree |n| (monic, squarefree, nonzero constant term), e_c = ∑_g (Ξ_c(1)/|G|)·conj Ξ_c(g)·g, with
Green's class function Ξ_c formed with a fixed faithful character. If c is not such a label,
e_c = 0. The family (e_c), indexed by all polynomials c, consists of idempotents, and those of
distinct polynomials have product zero. -/
lemma labelIdem_orthogonal : OrthogonalIdempotents (labelIdem (k := k) n) := by
  classical
  refine OrthogonalIdempotents.iff_mul_eq.mpr fun c d ↦ ?_
  obtain h_not_labels | ⟨hc, hd⟩ := em' (IsLabel (Fintype.card n) c ∧ IsLabel (Fintype.card n) d)
  · -- If `c` or `d` is not a label of degree `|n|`, one factor is `0`.
    aesop (add simp labelIdem)
  ext x
  let Ξ (c : Polynomial k) : GL n k → ℂ := (labelChar (faithfulChar k) c).evalGL
  obtain ⟨hc_isChar, -, -⟩ := hc.isIrreducibleChar_labelChar (n := n) (faithfulChar k)
  -- The convolution identity of the irreducible character `Ξ d` (last clause of
  -- `IsIrreducibleChar`); the inner product of `Ξ d` and `Ξ c` on its right side is `1` or `0` by
  -- `rankInner_labelChar`.
  have h_conv : Ξ d 1 * ((∑ t, starRingEnd ℂ (Ξ d t) * Ξ c (t * x⁻¹)) / Fintype.card (GL n k)) =
      (if d = c then 1 else 0) * Ξ d x⁻¹ := by
    obtain ⟨-, -, h_conv⟩ := hd.isIrreducibleChar_labelChar (n := n) (faithfulChar k)
    simpa only [Ξ, classInner_evalGL, rankInner_labelChar _ hd c hc, finMean,
      finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card] using h_conv (Ξ c) isClassFunction_evalGL
        x⁻¹
  -- The coefficient at `x` of the product is `Ξ c 1 / |GL n k|` times the left side of `h_conv`.
  suffices h_coeff : Ξ c 1 / Fintype.card (GL n k) * (Ξ d 1 / Fintype.card (GL n k)) *
      ∑ t, Ξ c (t * x⁻¹) * starRingEnd ℂ (Ξ d t) =
        if d = c then Ξ c 1 / Fintype.card (GL n k) * Ξ c x⁻¹ else 0 by
    simpa [hc, hd, apply_ite (coeff · x), eq_comm (a := c),
      ← hc_isChar.apply_inv, mul_mul_mul_comm _ _ (_ / _), ← mul_sum, labelIdem,
      coeff_mul_apply_right, Finsupp.sum_fintype] using h_coeff
  grind

/-- The coefficients of `e_c = New.labelIdem n c` form a class function on `GL_n(k)`: they are
constant on conjugacy classes. -/
lemma isClassFunction_labelIdem_coeff (c : Polynomial k) :
    IsClassFunction (labelIdem n c).coeff := by
  aesop (add simp [labelIdem, isClassFunction_evalGL])

/-- Let χ be a multiplicative character of k whose name x_χ ∈ kˣ (`New.charName`) is not a root of
the polynomial c, and let l be a nonzero vector. Here e_c = `labelIdem n c` is ∑ (Ξ_c(1)/|G|)·conj
Ξ_c(g)·g in ℂ[G], G = GL_n(k), with Ξ_c formed with `New.faithfulChar` k, a fixed injective
multiplicative character of an algebraically closed field over k (`New.IsFaithfulMulChar`), when c
is a label of degree
|n|, and is 0 otherwise. Then the sum of χ(det h)⁻¹ h over the invertible h = 1 + u lᵀ (the matrices
that fix the hyperplane l ⬝ᵥ x = 0 pointwise), multiplied on the right by e_c, is zero. -/
lemma hyperplaneSum_mul_labelIdem {c : Polynomial k} {χ : MulChar k ℂ}
    (hχ : ¬c.IsRoot (charName (faithfulChar k) χ)) {l : n → k} (hl : l ≠ 0) :
    hyperplaneSum χ l * labelIdem n c = 0 := by
  -- Let `N` be the group of invertible `1 + u lᵀ`. The character of `c` restricted to `N` is
  -- orthogonal to `χ ∘ det`: in a suitable basis `N` consists of the block triangular matrices with
  -- diagonal blocks a scalar and `1`, so the inner product is a value of the skew function, which
  -- vanishes by `skew_detChar_labelChar_eq_zero`.
  rw [IsClassFunction.commute (isClassFunction_labelIdem_coeff c)]
  obtain hc | hc := em' (IsLabel (Fintype.card n) c)
  · -- If `c` is not a label of degree `|n|`, then `e_c = 0`.
    simp [hc, labelIdem]
  let N : Submonoid (GL n k) :=
    { carrier := {g : GL n k | ∃ u : n → k, g.val = 1 + vecMulVec u l}
      mul_mem' := by
        simp_all [mul_add, mul_vecMulVec, add_assoc, ← add_vecMulVec, add_mulVec]
        tauto
      one_mem' := by simp }
  -- A finite submonoid of a group is a group: `N` inherits left cancellation from `GL n k`.
  let inst_cancel : LeftCancelMonoid N := {}
  let inst_group : Group N := LeftCancelMonoid.groupOfFinite
  -- Split `n → k` as `k` times a copy of the hyperplane `l ⬝ᵥ u = 0`.
  obtain ⟨L, hL⟩ := (ker (dotProductEquiv k n l)).exists_isCompl
  have h_range_dot : LinearMap.range (dotProductEquiv k n l) = ⊤ := by
    simpa [range_eq_top, surjective_iff_ne_zero]
  let e : (n → k) ≃ₗ[k] k × ((n → k) ⧸ L) :=
    (dotProductEquiv k n l).equivProdOfSurjectiveOfIsCompl L.mkQ h_range_dot L.range_mkQ
      (by simpa using hL)
  -- `1 + (E u).1` and `(E u).2` are the scalar block and the off-diagonal block of `1 + u lᵀ`.
  let E : (n → k) ≃ₗ[k] (k →ₗ[k] k) × (k →ₗ[k] (n → k) ⧸ L) :=
    e ≪≫ₗ .symm (prodEquiv k ≪≫ₗ ringLmapEquivSelf k k (k × ((n → k) ⧸ L)))
  have h_det (u : n → k) : (1 + vecMulVec u l).det = (1 + (E u).1).det := by
    simp [E, e, vecMulVec_eq Unit, det_one_add_mul_comm]
  have h_cls (u : n → k) : simClassOf (.id + (vecMulVec u l).toLin') =
      simClassOf (blockTriangularEnd 1 (1 + (E u).1) (E u).2) :=
    simClassOf_eq_of_equiv e (by simp [E, e, vecMulVec_mulVec, add_comm])
  -- `N` is parametrized by an invertible scalar block `g` and an arbitrary off-diagonal block `x`.
  let param (g : (Module.End k k)ˣ) (x : k →ₗ[k] (n → k) ⧸ L) : N :=
    ⟨.mk'' (1 + vecMulVec (E.symm (g.val - 1, x)) l)
      (by simpa [h_det] using g.isUnit.map LinearMap.det), _, rfl⟩
  have h_param : Bijective (uncurry param) := by
    refine ⟨?_, fun ⟨g, u, hu⟩ ↦ ⟨(g.det • 1, (E u).2), ?_⟩⟩
    · rintro ⟨g, x⟩ ⟨g', x'⟩ h_param_eq
      have h_vecMulVec_eq :
          vecMulVec (E.symm (g.val - 1, x)) l = vecMulVec (E.symm (g'.val - 1, x')) l := by
        simpa [param, Units.ext_iff] using h_param_eq
      simpa [Units.ext_iff] using E.symm.injective
        (vecMulVec_left_injective_of_ne_zero hl h_vecMulVec_eq)
    · simp_all [param, E, Units.smul_def, Units.ext_iff]
  -- `ρ` is the one-dimensional representation `χ⁻¹ ∘ det` of `N`.
  let ρ : Representation ℂ N ℂ :=
    .comp .smulOneHom { toFun g := χ⁻¹ g.val.det, map_one' := by simp, map_mul' := by simp }
  let Ξ : GL n k → ℂ := (labelChar (faithfulChar k) c).evalGL
  obtain ⟨h_isChar, -, -⟩ := hc.isIrreducibleChar_labelChar (n := n) (faithfulChar k)
  have h_orth : finMean (Ξ ∘ N.subtype * ρ.character) = 0 := by
    -- Through `param`, the mean over `N` becomes the mean over the scalar block `g` of `χ⁻¹(det g)`
    -- times the block average over `x`: a value of the skew function of `χ ∘ det`.
    have h_skew : skew (Module.finrank k k) ((detChar χ).rankPart (Module.finrank k k))
        (labelChar (faithfulChar k) c) = 0 := by
      simpa using skew_detChar_labelChar_eq_zero (faithfulChar k) hc hχ
    have h_skew_at : (finMean fun g : (Module.End k k)ˣ ↦
        starRingEnd ℂ ((detChar χ).rankPart (Module.finrank k k) (simClassOf g.val)) *
          finMean fun x : k →ₗ[k] (n → k) ⧸ L ↦
            labelChar (faithfulChar k) c (simClassOf (blockTriangularEnd 1 g.val x))) = 0 := by
      simpa only [skew, rankInner_eq_classInner_simClassOf, classInner, blockAverage_simClassOf,
        Hall.zero_apply] using congrFun h_skew (simClassOf (1 : Module.End k ((n → k) ⧸ L)))
    have h_term (g : (Module.End k k)ˣ) (x : k →ₗ[k] (n → k) ⧸ L) :
        (Ξ ∘ N.subtype * ρ.character) (param g x) =
          starRingEnd ℂ ((detChar χ).rankPart (Module.finrank k k) (simClassOf g.val)) *
            labelChar (faithfulChar k) c (simClassOf (blockTriangularEnd 1 g.val x)) := by
      simp [Ξ, ρ, param, mul_comm (labelChar _ c _), h_det, h_cls, ← χ.star_apply', Hall.evalGL,
        LinearMap.apply_one_eq_neg_charpoly_coeff_zero, character, detChar]
    rw [finMean_equiv (.ofBijective _ h_param) (fun p ↦ h_term p.1 p.2), finMean_prod]
    simpa only [finMean_const_mul] using h_skew_at
  -- Orthogonality kills every translate of the character, hence every coefficient of the product.
  ext x
  -- The coefficient at `x` is `Ξ 1 / |GL n k|` times this sum, which simp writes over the subtype
  -- of the `g` with `g = 1 + u lᵀ`: that is `N` with its definition unfolded.
  have h_sum_zero : ∑ g : {g : GL n k // ∃ u : n → k, (g : Matrix n n k) = 1 + vecMulVec u l},
      (labelChar (faithfulChar k) c).evalGL (g.val * x⁻¹) * χ⁻¹ g.val.val.det = 0 := by
    change ∑ g : N, Ξ (g.val * x⁻¹) * χ⁻¹ (g : GL n k).val.det = 0
    simpa [ρ, asAlgebraHom_eq_sum, LinearMap.ext_ring_iff] using
      h_isChar.asAlgebraHom_groupAlgElem_eq_zero N.subtype x⁻¹ h_orth
  simp [hc, sum_ite, ← sum_subtype_eq_sum_filter, ← h_isChar.apply_inv, mul_assoc, ← mul_sum,
    labelIdem, hyperplaneSum, coeff_mul_apply_right, Finsupp.sum_fintype, h_sum_zero]

variable {k : ι → Type _} [∀ w : ι, Field (k w)] [∀ w : ι, Finite (k w)]
  (c : ∀ w : ι, Polynomial (k w))

variable (n) in
/-- For a tuple (c_w) of polynomials over the fields k_w, the tensor product of the label
idempotents e_{c_w} in the group algebra of ∏ GL_n(k_w). -/
noncomputable def tupleIdem : MonoidAlgebra ℂ ((i : ι) → GL n (k i)) :=
  piTensorElem fun w ↦ labelIdem n (c w)

/-- Let `c = (c_w)` be a tuple of polynomials over the finite fields `k w`, and let `tupleIdem n c`
be the tensor product of the label idempotents `e_{c_w}`, an element of the complex group algebra of
`∏_w GL_n(k w)`. This element is a central idempotent (`New.IsCentralProj`): it is idempotent and
its coefficients form a class function on `∏_w GL_n(k w)`. -/
lemma isCentralProj_tupleIdem : IsCentralProj (tupleIdem n c) :=
  .piTensorElem fun w ↦ ⟨labelIdem_orthogonal.idem (c w), isClassFunction_labelIdem_coeff (c w)⟩

/-- For each tuple (c_w) of polynomials over the finite fields k_w, `tupleIdem` is the tensor
product ⊗_w e_{c_w} of the label idempotents of the group algebras of GL_n(k_w). It lies in the
group algebra of ∏_w GL_n(k_w). These elements are idempotents, and those of distinct tuples have
product zero. -/
lemma tupleIdem_orthogonal : OrthogonalIdempotents (tupleIdem (k := k) n) := by
  refine ⟨fun c ↦ (isCentralProj_tupleIdem c).left, fun c d hcd ↦ ?_⟩
  -- Distinct tuples differ at some `w`, where the label idempotents are orthogonal.
  obtain ⟨w, hw⟩ : ∃ w : ι, c w ≠ d w := ne_iff.mp hcd
  exact piTensorElem_mul_eq_zero w (labelIdem_orthogonal.ortho hw)

/-- Let `tupleIdem n c` be the tensor product of the label idempotents `e_{c_w}` for a tuple
`c = (c_w)` of polynomials over the finite fields `k w`, an element of the complex group algebra of
`∏_w GL_n(k w)`. For any finite set `s` of such tuples, the sum of `tupleIdem n c` over `c ∈ s` is a
central idempotent of this algebra (`New.IsCentralProj`): it is idempotent and its coefficients form
a class function. -/
lemma isCentralProj_sum_tupleIdem {s : Finset ((w : ι) → Polynomial (k w))} :
    IsCentralProj (∑ c ∈ s, tupleIdem (k := k) n c) :=
  -- A sum of class functions is a class function.
  ⟨tupleIdem_orthogonal.isIdempotentElem_sum, by simp [(isCentralProj_tupleIdem _).right]⟩

end LabelIdempotents

/-!
## Twisting by χ∘det and distinct conjugates of powers of a generator

* `New.scaleRootsEquiv`, `New.IsLabel.scaleRoots`: scaling the roots of a label by a unit `a` of `k`
  is multiplicative and preserves labels.
* `New.injOn_Iio_pow_card_pow_of_isPrimitiveRoot`: for `9 ∣ |k| - 1`, a power `ξ ^ l ^ a`, with `l`
  prime, of a primitive `(|k| ^ 3 ^ (e + 1) - 1)`-th root of unity has `3 ^ (e + 1)` distinct
  conjugates over `k`.
* `New.evalGL_labelChar_mul_det`: twisting `Ξ_c` by `χ ∘ det` scales the roots of `c` by the name of
  `χ`.
-/

section LabelTwist

open Polynomial Hall Matrix Finset Finite Nat Function

variable {k K n : Type*} {r : ℕ} [Field k] [Finite k] [Field K] [Fintype n]
  {T : MulChar K ℂ} [IsFaithfulMulChar K T] {c : k[X]} (a : kˣ)

/-- For nonzero a in k, the multiplicative bijection of k[X] to itself scaling the roots of a
polynomial by a, with inverse scaling by a⁻¹. -/
noncomputable def scaleRootsEquiv : k[X] ≃* k[X] where
  toFun P := P.scaleRoots a
  invFun P := P.scaleRoots a⁻¹
  left_inv P := by simp [← scaleRoots_mul]
  right_inv P := by simp [← scaleRoots_mul]
  map_mul' P Q := mul_scaleRoots_of_noZeroDivisors P Q a

omit [Finite k] in
/-- Scaling the roots of a label `c` of degree `r` (`New.IsLabel`: monic, squarefree, of degree `r`,
with nonzero constant term) by a unit `a` of `k` gives a label of degree `r`. -/
lemma IsLabel.scaleRoots (hc : IsLabel r c) : IsLabel r (c.scaleRoots a) := by
  obtain ⟨h_monic, h_sqfree, h_deg, h_coeff⟩ := hc
  refine ⟨(monic_scaleRoots_iff _).mpr h_monic, ?_, by simpa using h_deg, by simpa using h_coeff⟩
  -- `scaleRootsEquiv a` is a multiplicative isomorphism, so it preserves squarefreeness.
  refine (scaleRootsEquiv a).surjective.forall.mpr fun x hx ↦ (h_sqfree x ?_).map _
  rw [← map_dvd_iff (scaleRootsEquiv a), map_mul]
  exact hx

/-- Let `q = Nat.card k ≡ 1 mod 9` (`h_nine`), `r = 3 ^ (e + 1)`, `ξ` a primitive `(q ^ r - 1)`-th
root of unity in `K` and `l` a prime. Then `ξ ^ l ^ a` has `r` distinct conjugates: its `q ^ i`-th
powers, `0 ≤ i < r`, are distinct. -/
lemma injOn_Iio_pow_card_pow_of_isPrimitiveRoot {ξ : K} {e l : ℕ} (a : ℕ)
    (h_nine : 9 ∣ Nat.card k - 1)
    (hξ : IsPrimitiveRoot ξ (Nat.card k ^ 3 ^ (e + 1) - 1)) (hl : Nat.Prime l) :
    (Set.Iio (3 ^ (e + 1))).InjOn fun i : ℕ ↦ (ξ ^ l ^ a) ^ Nat.card k ^ i := by
  -- The period of `ξ ^ l ^ a` under `x ↦ x ^ Nat.card k` divides `3 ^ (e + 1)`; it is enough to see
  -- that it does not divide `3 ^ e`.
  have h_one_lt_card : 1 < Nat.card k := one_lt_card
  obtain ⟨s, hs_sub⟩ : 9 ∣ Nat.card k ^ 3 ^ e - 1 :=
    h_nine.trans (sub_one_dvd_pow_sub_one _ (3 ^ e))
  have hs : Nat.card k ^ 3 ^ e = 9 * s + 1 := by grind
  obtain ⟨hξ_ne, hξ_fixed⟩ : ξ ≠ 0 ∧ ξ ^ Nat.card k ^ 3 ^ (e + 1) = ξ := by
    simpa [pow_pred_eq_one_iff, succ_le_iff, h_one_lt_card] using hξ.pow_eq_one
  -- `(9 * s + 1) ^ 3 - 1 = 9 * s * b`, so `ξ ^ (9 * s)` has order `b`
  set b : ℕ := s * (81 * s + 27) + 3
  have h_order_eq : Nat.card k ^ 3 ^ (e + 1) - 1 = 9 * s * b := by
    rw [pow_succ, pow_mul, hs]
    lia
  have h_primitive : IsPrimitiveRoot (ξ ^ (9 * s)) b := hξ.pow (by simpa) h_order_eq
  -- `b` is no power of `l`: it is divisible by `3`, not by `9`, and `b ≠ 3` as `s ≠ 0`
  have h_not_dvd : ¬b ∣ l ^ a := by
    intro h_dvd_pow
    have h_three_dvd_b : 3 ∣ b := by lia
    obtain rfl : 3 = l := prime_eq_prime_of_dvd_pow prime_three hl (h_three_dvd_b.trans h_dvd_pow)
    obtain ⟨i, hi_le, hb_eq⟩ : ∃ i ≤ a, b = 3 ^ i := (dvd_prime_pow hl).mp h_dvd_pow
    -- `b ≥ 3`, `b = 3` would force `s = 0`, and `9` divides `3 ^ (i + 2)` but not `b`.
    rcases i with _ | _ | i <;> grind [one_lt_pow]
  have h_period : minimalPeriod (fun x : K ↦ x ^ Nat.card k) (ξ ^ l ^ a) = 3 ^ (e + 1) := by
    refine minimalPeriod_eq_prime_pow ?_ ?_
    · -- `ξ ^ l ^ a` is not fixed by `x ↦ x ^ Nat.card k ^ 3 ^ e`: that would make
      -- `(ξ ^ (9 * s)) ^ l ^ a = 1`, so `b ∣ l ^ a`.
      have h_pow_ne_one : ¬(ξ ^ (9 * s)) ^ l ^ a = 1 :=
        mt (h_primitive.dvd_of_pow_eq_one _) h_not_dvd
      simpa [IsPeriodicPt, IsFixedPt, hs, pow_right_comm ξ (l ^ a), pow_succ ξ, mul_pow, hξ_ne]
        using h_pow_ne_one
    · simp [IsPeriodicPt, IsFixedPt, pow_right_comm ξ (l ^ a), hξ_fixed]
  simpa [h_period] using
    iterate_injOn_Iio_minimalPeriod (f := fun x : K ↦ x ^ Nat.card k) (x := ξ ^ l ^ a)

/-- Let T be faithful, let c be a label of degree r (monic squarefree, with nonzero constant term)
and let χ be a multiplicative character of k. Then Ξ_c(g)·χ(det g) = Ξ_{c'}(g) for g in GL_n(k), for
any n, where c' = `c.scaleRoots x_χ` has roots x_χ times those of c. Here Ξ_c = `labelChar T c` is
the parabolic-induction product of the τ_P over the irreducible factors P of c, and
x_χ = `charName T χ` ∈ kˣ. A case of the compatibility of Green's characters with twisting by
χ∘det. -/
lemma evalGL_labelChar_mul_det [Algebra k K]
    [DecidableEq n] (hc : IsLabel r c) (χ : MulChar k ℂ) (g : GL n k) :
    (labelChar T c).evalGL g * χ g.val.det =
      (labelChar T (c.scaleRoots (charName T χ))).evalGL g := by
  -- `θ` extends `χ` to `K` (`thetaChar_charName`), so `χ (det g)` is the value `w` of `θ` at the
  -- product of the eigenvalues of `g` in `K`. It is multiplicative in stable subspace and quotient,
  -- so by induction on `c` it is enough to twist each factor `labelChar T P`.
  let a : kˣ := charName T χ
  let θ : MulChar K ℂ := thetaChar T (.card k) (algebraMap k K a)
  let w (x : SimClass k) : ℂ := θ (x.charpoly.aroots K).prod
  have h_det_eq : χ g.val.det = w (simClassOf g.val.toLin') := by
    rw [← thetaChar_charName T, RingHom.map_det, det_eq_prod_roots_charpoly,
      RingHom.mapMatrix_apply, charpoly_map, ← charpoly_toLin', ← charpoly_simClassOf]
  have h_w_mul {m : ℕ} {f : Module.End k (Fin m → k)} (W : StableSubspace f) :
      w (simClassOf f) = w (simClassOf W.endOnSub) * w (simClassOf W.endOnQuot) := by
    simp [w, ← charpoly_endOnSub_mul_endOnQuot _ W, aroots_mul,
      (LinearMap.charpoly_monic _).ne_zero]
  have h_scale_irred {P : k[X]} {y : K} (hP_monic : P.Monic) (hP_irred : Irreducible P)
      (hP_coeff : P.coeff 0 ≠ 0) (hy : P.aeval y = 0) :
      labelChar T (P.scaleRoots a) = fun x ↦ labelChar T P x * w x := by
    ext m f
    have hP_irred_scaled : Irreducible (P.scaleRoots a) := hP_irred.map (scaleRootsEquiv a)
    -- `greenTau` may be computed with any root: take `y` for `P` and `a * y` for the scaled `P`.
    rw [labelChar_eq_greenTau T hP_irred_scaled ((monic_scaleRoots_iff _).mpr hP_monic),
      labelChar_eq_greenTau T hP_irred hP_monic, greenTau_eq hP_irred hP_coeff hy,
      greenTau_eq hP_irred_scaled (by simpa) (scaleRoots_aeval_eq_zero hy)]
    suffices h_cusp : m = P.natDegree →
      greenCuspidal k (thetaChar T (.card k ^ P.natDegree) (algebraMap k K a * y)) (simClassOf f) =
        w (simClassOf f) * greenCuspidal k (thetaChar T (.card k ^ P.natDegree) y) (simClassOf f) by
      -- Both sides vanish unless `m = P.natDegree`, where `h_cusp` applies.
      by_cases hm : m = P.natDegree <;> simp_all [mul_comm (w (simClassOf f)), mul_assoc]
    -- By `greenCuspidal_simClassOf_eq_mul`, compare the two characters at `z` when the eigenvalues
    -- of `f` are the `z ^ q ^ i`, `i < deg P`, `q = |k|`. Then `w (simClassOf f)` is `θ` at the
    -- norm of `z`, which is the value at `z` of the character named by `a` for `q ^ deg P`
    -- (`thetaChar_eq_apply_norm_pow`).
    refine fun hm ↦ greenCuspidal_simClassOf_eq_mul _ _ fun z ↦ ?_
    by_cases hz : z = 0
    · -- At `z = 0` both sides vanish.
      simp_all [w, θ, ← range_val, MulChar.map_zero, mul_comm, prod_pow_eq_pow_sum]
    · simp_all [w, θ, thetaChar_mul, root_pow_card_pow_pred_eq_one hP_irred hP_coeff hy,
        ← range_val, thetaChar_eq_apply_norm_pow T one_lt_card _ _ rfl (pow_one _), mul_comm,
        prod_pow_eq_pow_sum, root_pow_card_pow_eq_self_iff (irreducible_X_sub_C a.val)]
  have h_scaleRoots_eq : labelChar T (c.scaleRoots a) = fun x ↦ labelChar T c x * w x := by
    refine hc.induction_irreducible_mul K ?_ fun P _ c y hP_monic hP_irred hP_coeff hy ih ↦
      Hall.ext fun _ f ↦ ?_
    · -- The constant `1`: both sides are read in dimension `0`.
      funext x
      simp_all [w, eq_simClassOf_zero_of_dim_eq_zero]
    simp only [mul_scaleRoots_of_noZeroDivisors, map_mul, ih, mul_simClassOf, finsum_mul]
    refine finsum_congr fun W ↦ ?_
    rw [h_scale_irred hP_monic hP_irred hP_coeff hy, h_w_mul W, mul_mul_mul_comm]
  simp [h_det_eq, h_scaleRoots_eq, a, Hall.evalGL]

end LabelTwist

end New
