import Lib.ClassField.Global.CMSplittingCharacters

/-!
# Sums of two squares, Landherr's theorem and the Hasse principle for unitary cocycles

Let `E` be a CM field with `New.HasPrimitiveRoot5040 E`, and let `F` be its maximal real subfield.
The file starts with a result on sums of two squares in quadratic algebras over `F`. It then proves
Landherr's theorem: a hermitian space that has an orthonormal frame at the finite places is
determined up to rational isometry by its signs at the infinite places. Finally it proves the Hasse
principle for cocycles of a cyclic Galois group of prime order in the definite unitary group, which
is used for base change. There `E' / E` is a Galois extension of CM fields of prime degree, and
`σ ≠ 1` generates its group.

## Main definitions and results

* `New.exists_sq_add_sq_quadraticAlgebra`: for `E` with a CM type, a totally positive `p` in `F` is
  a sum of two squares in `F[X] / (X² - (q p - B²))` for every `B` in `F`. This holds when `p` has
  valuation `1` outside a set `S` of finite places of `E`, and `q` has valuation `1` at the places
  of `S` and at their complex conjugates.
* `New.Core.exists_form_eq_one`: a hermitian matrix representing `1` over the adeles does so over
  `E`.
* `New.Core.exists_rat_frame_of_adelic`: the same for a diagonal matrix of signs, by induction on
  the columns.
* `New.Space.landherr`, `New.Space.exists_x_eq_and_ratEmbed_conj_eq`: two spaces with the same signs
  differ by a rational change of basis and by moving the point.
* `New.U.hasse_principle_coboundary`: a cocycle that splits over the finite adeles splits
  rationally; the proof combines Hilbert 90 for `GL n` with Landherr's theorem `New.Space.landherr`.

Notions from other files:
* `New.CMType`: makes the field `E` a CM number field with a chosen complex embedding `Φ w` of `E`
  for each infinite place `w`.
* `New.𝔸`: the product of one copy of `ℂ` for each infinite place of `E` and the finite adeles
  `𝔸f E`; this is the adele ring of `E` when `E` is totally complex.
* `New.Space`: a hermitian space with a point. It is a matrix `J` over `E` and `x : GL n (𝔸 E)`
  with `xᴴ J x` equal to `New.stdForm E s`, which is `diag(s)` at the infinite places and `1` at
  the finite places.

## Relation to the literature

Known result: Landherr's Hasse principle for hermitian forms. The Hasse principle is proved only
for adelically unimodular spaces of equal signature over a CM field containing the roots of unity of
order 5040. It uses Hasse's norm theorem and strong approximation for the adeles instead of
Hasse-Minkowski. Source: W.
Landherr, Äquivalenz Hermitescher Formen über einem beliebigen algebraischen Zahlkörper, Abh. Math.
Sem. Hamburg 11 (1936) 245-248; M. Kneser, Lectures on Galois cohomology of classical groups, TIFR
47 (1969), §5.5.
-/

/-!
## A totally positive number as a sum of two squares

Here `QuadraticAlgebra F μ 0` is `F[X] / (X² - μ)`.
-/

section SumOfTwoSquares

open Algebra QuadraticAlgebra Set NumberField

/-- Hasse principle for sums of two squares: a totally positive element `x` of a number field `M`
that is a limit of sums of two squares in the completion at each finite place is a sum of two
squares. Sums of two squares are written as norms from `M[X] / (X² + 1)`. -/
lemma New.exists_norm_eq_of_forall_mem_closure {M : Type} [Field M] [NumberField M] {x : M}
    (hx_pos : IsTotallyPositive x)
    (h_local : ∀ w : FinPlace M, algebraMap M (LocField w) x ∈
      closure (range fun z : QuadraticAlgebra M (-1) 0 ↦ algebraMap M (LocField w) z.norm)) :
    ∃ z : QuadraticAlgebra M (-1) 0, z.norm = x := by
  -- If `-1` is a square in `M`, every element is a sum of two squares.
  obtain ⟨r, hr⟩ | h_square := Classical.em (∃ r : M, r ^ 2 = -1 + 0 * r)
  · refine ⟨⟨x + 4⁻¹, (x - 4⁻¹) * r⟩, ?_⟩
    rw [norm_def]
    linear_combination (x - 4⁻¹) ^ 2 * hr
  obtain rfl | hx_ne := eq_or_ne x 0
  · exact ⟨0, by simp⟩
  -- Otherwise `M(√-1)` is a quadratic extension of `M`, and Hasse's norm theorem applies.
  have : Fact (∀ r : M, r ^ 2 ≠ -1 + 0 * r) := ⟨not_exists.1 h_square⟩
  have : NumberField (QuadraticAlgebra M (-1) 0) := .of_module_finite M _
  have : IsQuadraticExtension M (QuadraticAlgebra M (-1) 0) := .mk (finrank_eq_two (-1 : M) 0)
  have norm_eq (z : QuadraticAlgebra M (-1) 0) : norm M z = z.norm := det_toLinearMap_eq_norm z
  obtain ⟨z, hz⟩ : ∃ z : (QuadraticAlgebra M (-1) 0)ˣ, z.map (norm M) = .mk0 x hx_ne :=
    hasse_norm _ (by simpa [norm_eq] using h_local) hx_pos
  exact ⟨z, (norm_eq z).symm.trans (congrArg Units.val hz)⟩

/-- Let `E` be a CM field with a primitive root of unity of order `5040` and maximal real subfield
`F`. The norm to `F` of an element of `E` is a sum of two squares in `F`. -/
lemma New.exists_norm_eq_sq_add_sq {E : Type} [Field E] [NumberField E] [IsCMField E]
    [HasPrimitiveRoot5040 E] (x : E) :
    ∃ a b : maximalRealSubfield E, norm (maximalRealSubfield E) x = a ^ 2 + b ^ 2 := by
  -- As `E = F(I)` with `I² = -1`, the norm of `x = a + b I` is `a² + b²`, with `a = T x` and
  -- `-b = T (x * I)`.
  obtain ⟨I, hI, hI_star⟩ := HasPrimitiveRoot5040.exists_mul_self_eq_neg_one (E := E)
  have hI_sq : (I : E) * I = -1 := by simpa using congrArg (algebraMap (𝓞 E) E) hI
  have hI_conj : star (I : E) = -I := by simpa using congrArg (algebraMap (𝓞 E) E) hI_star
  let T (y : E) : maximalRealSubfield E := trace (maximalRealSubfield E) E (y / 2)
  have hT (y : E) : (T y : E) = (y + star y) / 2 := by
    simp [T, trace_maximalRealSubfield_eq_add_star, add_div]
  refine ⟨T x, T (x * I), Subtype.ext ?_⟩
  push_cast
  rw [norm_maximalRealSubfield_eq_mul_star, hT, hT, star_mul', hI_conj]
  linear_combination (-(x - star x) ^ 2 / 4) * hI_sq

/-- Let `E` be a CM field with a primitive root of unity of order `5040` and maximal real subfield
`F`, and let `u` be a finite place of `E` above the place `v` of `F`. Let `a` be a finite adele of
`E` that is fixed by conjugation and is a unit at every place. If the component of `a` at `u` is an
element `s` of `F`, then `s` is a limit of norms from `E` in the completion of `F` at `v`. -/
lemma New.mem_closure_range_norm_of_apply_eq {E : Type} [Field E] [NumberField E] [IsCMField E]
    [HasPrimitiveRoot5040 E] {a : 𝔸f E} (ha_real : star a = a)
    (ha_unit : ∀ w : FinPlace E, Valued.v (a w) = 1) {u : FinPlace E}
    {v : FinPlace (maximalRealSubfield E)}
    (hu : u.comap (algebraMap (maximalRealSubfield E) E) = v) {s : maximalRealSubfield E}
    (ha_u : a u = algebraMap E (u.adicCompletion E) (algebraMap (maximalRealSubfield E) E s)) :
    algebraMap (maximalRealSubfield E) (LocField v) s ∈ closure (range fun x : E ↦
      algebraMap (maximalRealSubfield E) (LocField v) (norm (maximalRealSubfield E) x)) := by
  -- The adele `a` is a norm `ȳ y`, so `s` is the component at `v` of the norm of `ȳ` to `F`.
  obtain ⟨y, hy⟩ := exists_unit_star_mul_self_eq ha_real ha_unit
  have norm_y : adeleNorm (maximalRealSubfield E) E (star y) v =
      algebraMap (maximalRealSubfield E) (LocField v) s := by
    apply (locMap _ hu).injective
    simp [hy, ha_u, ← adeleMap_apply, Cohomology.finAdeleIncl_adeleNorm_eq_mul_star]
  rw [← norm_y]
  exact adeleNorm_mem_closure

/-- Let `E` be a CM field with a CM type and a primitive root of unity of order `5040`, and let `p`,
`q`, `B` lie in its maximal real subfield `F`. Suppose that `p` is totally positive and has
valuation `1` at every finite place of `E` outside `S`. Suppose also that `q` has valuation `1` at
every place of `S` and at its complex conjugate. Then `p` is a sum of two squares in
`F[X] / (X² - (q p - B²))`: it is the norm of an element of the extension of this algebra by a
square root of `-1`. -/
lemma New.exists_sq_add_sq_quadraticAlgebra {E : Type} [Field E] [CMType E] [HasPrimitiveRoot5040 E]
    (p q B : maximalRealSubfield E) {S : Set (FinPlace E)} (hp_pos : IsTotallyPositive p)
    (hp_unit : ∀ w ∉ S, w.valuation E p = 1) (hq_unit : ∀ w ∈ S.conjClosure, w.valuation E q = 1) :
    ∃ z : QuadraticAlgebra (QuadraticAlgebra (maximalRealSubfield E) (q * p - B ^ 2) 0) (-1) 0,
      z.norm = ⟨p, 0⟩ := by
  classical
  -- In a number field `M` over `E⁺` with a square root of `μ = q p - B²`, the element `p` is
  -- everywhere locally a sum of two squares, hence globally by Hasse's norm theorem.
  set μ : maximalRealSubfield E := q * p - B ^ 2
  suffices key : ∀ {M : Type} [Field M] [NumberField M] (i : maximalRealSubfield E →+* M) (m : M),
      m * m = i μ → ∃ z : QuadraticAlgebra M (-1) 0, z.norm = i p by
    -- Apply this to `E⁺` if `μ` is a square there, and to the field `E⁺(√μ)` if not.
    obtain ⟨r, hr⟩ | h_square := Classical.em (∃ r : maximalRealSubfield E, r ^ 2 = μ + 0 * r)
    · obtain ⟨z, hz⟩ := key (.id _) r (by simpa [sq] using hr)
      exact ⟨⟨.C z.re, .C z.im⟩, by ext <;> simp_all [norm_def]⟩
    · have : Fact (∀ r : maximalRealSubfield E, r ^ 2 ≠ μ + 0 * r) := ⟨not_exists.1 h_square⟩
      have : NumberField (QuadraticAlgebra _ μ 0) := .of_module_finite (maximalRealSubfield E) _
      exact key (algebraMap _ (QuadraticAlgebra _ μ 0)) ω omega_mul_omega_eq_mk
  intro M _ _ i m hm
  refine exists_norm_eq_of_forall_mem_closure (fun σ ↦ hp_pos (σ.comp i)) fun w ↦ ?_
  -- Let `u` be a place of `E` above the place of `E⁺` below `w`.
  obtain ⟨u, hu⟩ := FinPlace.comap_surjective (algebraMap (maximalRealSubfield E) E) (w.comap i)
  -- The adele `a` that is `q⁻¹` on `S.conjClosure` and `p` elsewhere is a real unit, and its
  -- component at `u` is `s`.
  let a : 𝔸f E := algebraMap E (𝔸f E) (q⁻¹ - p) * idem S.conjClosure + algebraMap E (𝔸f E) p
  have ha_real : star a = a := by simp [a, mem_maximalRealSubfield_iff_star_eq.1]
  have ha_unit (v : FinPlace E) : Valued.v (a v) = 1 := by
    by_cases hv : v ∈ S.conjClosure
    · simp [a, hv, hq_unit v hv]
    · simp [a, hv, hp_unit v (hv ∘ .inl)]
  let s : maximalRealSubfield E := if u ∈ S.conjClosure then q⁻¹ else p
  have ha_u : a u = algebraMap E (u.adicCompletion E) (algebraMap (maximalRealSubfield E) E s) := by
    change a u = algebraMap E (𝔸f E) s u
    by_cases h : u ∈ S.conjClosure <;> simp [a, s, h]
  -- On `S.conjClosure`, `p = (B² + m²) q⁻¹` because `q p = B² + μ`; elsewhere `p = 1 * p`.
  obtain ⟨z, hz⟩ : ∃ z : QuadraticAlgebra M (-1) 0, z.norm * i s = i p := by
    by_cases h : u ∈ S.conjClosure
    · have hq_ne : i q ≠ 0 := (map_ne_zero i).2 fun hq ↦ by simpa [hq] using hq_unit u h
      exact ⟨⟨i B, m⟩, by simp [s, h, norm_def, hm, μ, field]⟩
    · exact ⟨1, by simp [s, h]⟩
  -- So `s` is a limit of norms from `E` at the place below `w`. Pass to the completion of `M` at
  -- `w` and multiply by `z.norm`: this continuous map sends `s` to `p`, and norms from `E`, which
  -- are sums of two squares, to sums of two squares.
  let f (t : LocField (w.comap i)) : LocField w :=
    algebraMap M (LocField w) z.norm * locMap i rfl t
  have hf_apply (t : maximalRealSubfield E) :
      f (algebraMap _ _ t) = algebraMap M (LocField w) (z.norm * i t) := by simp [f]
  rw [← hz, ← hf_apply]
  refine map_mem_closure ((continuous_locMap i rfl).const_mul _)
    (mem_closure_range_norm_of_apply_eq ha_real ha_unit hu ha_u) ?_
  rintro _ ⟨x, rfl⟩
  obtain ⟨b, c, hbc⟩ := exists_norm_eq_sq_add_sq x
  have h_norm : (z * ⟨i b, i c⟩).norm = z.norm * i (norm (maximalRealSubfield E) x) := by
    rw [map_mul, hbc]
    simp [norm_def, sq]
  exact ⟨z * ⟨i b, i c⟩, by simp only [h_norm, hf_apply]⟩

end SumOfTwoSquares

/-!
## Landherr's theorem

Vectors are one-column matrices `Matrix n Unit _`.
-/

namespace New

open NumberField Matrix Cohomology Complex Set Function

-- `s` gives the signs of a space at the infinite places.
variable {E : Type} {n : Type*} {s : n → ℤˣ} [Field E] [CMType E] [Fintype n] [DecidableEq n]

/-- Let `E` be a CM field and `σ` an adele of `E`, written as a `1 × 1` matrix. Then there are
adeles `a` and `b = 1 + σ a` of the same norm: `ā a = b̄ b`. -/
lemma Core.exists_norm_eq_norm_one_add_mul (σ : Matrix Unit Unit (𝔸 E)) :
    ∃ a b : Matrix Unit Unit (𝔸 E), 1 + σ * a = b ∧ aᴴ * a = bᴴ * b := by
  -- At a complex place take `a = b = (1 - x)⁻¹`, or `a = -1/2`, `b = 1/2` if `x = 1`.
  have h_inf (x : ℂ) : ∃ a b : ℂ, 1 + x * a = b ∧ star a * a = star b * b := by
    by_cases hx : x = 1
    · exact ⟨-2⁻¹, 2⁻¹, by norm_num [hx], by simp⟩
    · exact ⟨(1 - x)⁻¹, (1 - x)⁻¹, by field [sub_ne_zero.2 (Ne.symm hx)], rfl⟩
  have h_fin (x : 𝔸f E) : ∃ a b : 𝔸f E, 1 + x * a = b ∧ star a * a = star b * b := by
    -- Patch `x (1 - x)` and `1 + x` along an idempotent `e` to an adele `d` dividing both.
    obtain ⟨e, d, p, q, he, hd, hp, hq⟩ : ∃ e d p q : 𝔸f E, e * e = e ∧
        d = x * (1 - x) - e * (x * (1 - x) - (1 + x)) ∧ x * (1 - x) = d * p ∧ 1 + x = d * q := by
      obtain ⟨e, he, ⟨p, -, hp⟩, -, q, -, hq⟩ := by
        simpa [-IsIdempotentElem.mul_one_sub_self] using isValuationPair_Ô (x * (1 - x)) (1 + x)
      exact ⟨e, _, p, q, he, rfl, hp, hq⟩
    -- As `(2 - x) (1 + x) - x (1 - x) = 2` is a unit, so is `d`, with inverse `z`.
    obtain ⟨t, ht⟩ : ∃ t : 𝔸f E, t * 2 = 1 :=
      mod_cast (isUnit_natCast_finAdele (E := E) two_ne_zero).exists_left_inv
    set z : 𝔸f E := t * ((2 - x) * q - p)
    have hz : z * d = 1 := by linear_combination ht - t * (2 - x) * hq + t * hp
    refine ⟨z * (x * (1 - e) - star e), z * (x * (1 - star e) + e), ?_, ?_⟩
    · -- The second bracket minus `x` times the first is `d`.
      linear_combination (-1 : 𝔸f E) * hz + z * hd
    · -- Both brackets have norm `x x̄ (1 - e) (1 - ē) + e ē`, because `e` and `ē` are idempotent.
      have he_star : star e * star e = star e := by rw [← star_mul, he]
      simp only [star_mul', star_sub, star_add, star_one, star_star]
      linear_combination star z * z * (x + star x) * (he_star + he)
  choose a b hab using h_inf
  obtain ⟨a', b', h_shear, h_norm⟩ := h_fin (σ () ()).2
  refine ⟨of fun _ _ ↦ (fun w ↦ a ((σ () ()).1 w), a'),
    of fun _ _ ↦ (fun w ↦ b ((σ () ()).1 w), b'), ?_, ?_⟩
  · simp [← ext_iff, mul_apply, Prod.ext_iff, hab, h_shear, funext_iff]
  · simpa [← ext_iff, mul_apply, Prod.ext_iff, h_norm, funext_iff] using fun w ↦ (hab _).2

/-- Let `K` be a matrix over `E` that represents `1` over the adeles, into which `toAdele` embeds
`E`, and let `S` be finite. Then the value of `K` at some rational vector has positive real part
under each embedding `Φ w` of the CM type and is a unit at `S.conjClosure`, the places of `S` and
their conjugates. -/
lemma Core.exists_form_pos_and_unit {K : Matrix n n E} (z : Matrix n Unit (𝔸 E))
    (hz : zᴴ * K.map toAdele * z = 1) {S : Set (FinPlace E)} (hS : S.Finite) :
    ∃ u : Matrix n Unit E,
      (∀ w : InfinitePlace E, 0 < (Φ w ((uᴴ * (K * u)) () ())).re) ∧
      ∀ w ∈ S.conjClosure, w.valuation E ((uᴴ * (K * u)) () ()) = 1 := by
  -- Both conditions define an open set `U` of adeles that contains `1`.
  let U : Set (𝔸 E) := (univ.pi fun _ : InfinitePlace E ↦ {c : ℂ | 0 < c.re}) ×ˢ
    ⋂ w ∈ S.conjClosure, evalAt w ⁻¹' {x : LocField w | Valued.v.restrict x = 1}
  have hU_open : IsOpen U :=
    (isOpen_set_pi finite_univ fun _ _ ↦ isOpen_re_gt 0).prod <|
      hS.conjClosure.isOpen_biInter fun w _ ↦
      (Valued.isOpen_sphere _ one_ne_zero).preimage (continuous_evalAt w)
  -- Strong approximation: approximate `z` by a rational `u` plus a term supported off `S` and
  -- its conjugate.
  obtain ⟨⟨u, y⟩, h_mem⟩ :=
    (Exchange.denseRange_rat_matrix_add hS.conjClosure.infinite_compl.nonempty 1).exists_mem_open
      (hU_open.preimage (f := fun x : Matrix n Unit (𝔸 E) ↦ (xᴴ * K.map toAdele * x) () ())
        (by fun_prop)) ⟨z, by simp [U, hz]⟩
  refine ⟨u, fun w ↦ ?_, fun w hw ↦ ?_⟩
  · -- At the infinite places the second term is `0`.
    simpa [U, ← Matrix.map_mul, Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul] using
      h_mem.1 w (mem_univ w)
  · -- It is `0` at `w` and at its conjugate as well.
    have hw_conj : star w ∈ S.conjClosure := by simpa [conjClosure, or_comm] using hw
    simpa [U, hw, hw_conj, idem_apply, -compl_union, -mem_union, ← Matrix.map_mul,
      Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul] using mem_iInter₂.1 h_mem.2 w hw

/-- Hasse principle for representing `1`: let `E` satisfy `New.HasPrimitiveRoot5040` and let `K` be
a hermitian matrix over `E`, possibly degenerate. If `zᴴ K z = 1` for an adelic vector `z`, then
`wᴴ K w = 1` for a vector `w` over `E`. -/
lemma Core.exists_form_eq_one [HasPrimitiveRoot5040 E]
    (K : Matrix n n E) (hK : Kᴴ = K) (z : Matrix n Unit (𝔸 E))
    (hz : zᴴ * K.map toAdele * z = 1) : ∃ w : Matrix n Unit E, wᴴ * K * w = 1 := by
  let N (u : Matrix n Unit E) : maximalRealSubfield E :=
    ⟨(uᴴ * (K * u)) () (), mem_maximalRealSubfield_iff_star_eq.2
      (star_dotProduct_mulVec_comm hK _ _)⟩
  -- First `u` with `N u` positive at infinity, then `v` with `N v` a unit at the finitely many
  -- places where `N u` is not, and at their conjugates.
  obtain ⟨u, hu_pos, -⟩ := exists_form_pos_and_unit z hz finite_empty
  have hu : (N u : E) ≠ 0 := fun h_zero ↦ by
    simpa [show (uᴴ * (K * u)) () () = 0 from h_zero] using hu_pos Classical.ofNonempty
  let S : Set (FinPlace E) := {w | w.valuation E (N u : E) ≠ 1}
  have hS : S.Finite := by simpa [S] using finite_setOf_valued_val_ne_one
                             (principalIdele (.mk0 _ hu))
  obtain ⟨v, -, hv_unit⟩ := exists_form_pos_and_unit z hz hS
  -- Each real embedding of `E⁺` is the restriction of some `Φ w`.
  have h_tot : IsTotallyPositive (N u) := fun φ ↦ by
    obtain ⟨w, hw⟩ := bijective_cmType_restrict.surjective (ofRealHom.comp φ)
    exact (hu_pos w).trans_eq (congrArg re (RingHom.congr_fun hw (N u)))
  -- With `2 B = uᴴ K v + vᴴ K u` and `μ = N v * N u - B²`, write `N u` as a sum of the two squares
  -- `(p + r √μ)²` and `(q + s √μ)²`.
  let B : maximalRealSubfield E := (N (u + v) - N u - N v) / (1 + 1)
  let μ : maximalRealSubfield E := N v * N u - B ^ 2
  obtain ⟨p, q, r, s, h_re, h_im⟩ : ∃ p q r s : maximalRealSubfield E,
      p * p + q * q + μ * (r * r + s * s) = N u ∧ p * r + q * s = 0 := by
    obtain ⟨⟨x, y⟩, hxy⟩ :=
      exists_sq_add_sq_quadraticAlgebra (N u) (N v) B h_tot (fun _ ↦ not_not.1) hv_unit
    obtain ⟨h_re, h_im⟩ : x.re * x.re + μ * x.im * x.im + (y.re * y.re + μ * y.im * y.im) = N u ∧
        x.re * x.im + x.im * x.re + (y.re * y.im + y.im * y.re) = 0 := by
      simpa [QuadraticAlgebra.norm_def, QuadraticAlgebra.ext_iff] using hxy
    exact ⟨x.re, y.re, x.im, y.im, by linear_combination h_re, by linear_combination h_im / 2⟩
  obtain ⟨i, hi_sq, hi_star⟩ := HasPrimitiveRoot5040.exists_mul_self_eq_neg_one (E := E)
  -- Let `α = p + i q` and `β = i (r + i s)`. The vector `(α / N u) u + β (v - (B / N u) u)` has
  -- norm `(ᾱ α + μ β̄ β) / N u = 1`. The cross terms cancel because `ᾱ β` is real (as
  -- `p r + q s = 0`) and `uᴴ K (v - (B / N u) u)` is skew.
  let form (x y : Matrix n Unit E) : E := (xᴴ * (K * y)) () ()
  have h_expand (a b : E) : form (a • u + b • v) (a • u + b • v) =
      star a * a * N u + star a * b * form u v + star b * a * form v u + star b * b * N v := by
    simp [form, N, Matrix.add_mul, Matrix.mul_add]
    ring
  have hB : form u v + form v u = 2 * B := by
    simp [form, B, N, Matrix.add_mul, Matrix.mul_add]
    ring
  have hI_sq : (i : E) * i = -1 := by simpa using congrArg (algebraMap (𝓞 E) E) hi_sq
  have hI_star : star (i : E) = -i := by simpa using congrArg (algebraMap (𝓞 E) E) hi_star
  have h_real (x : maximalRealSubfield E) : star (x : E) = x :=
    mem_maximalRealSubfield_iff_star_eq.1 x.2
  have h_re_coe : (p * p + q * q + (N v * N u - B ^ 2) * (r * r + s * s) : E) = N u :=
    congrArg Subtype.val h_re
  have h_im_coe : (p * r + q * s : E) = 0 := congrArg Subtype.val h_im
  obtain ⟨α, β, hα, hβ, h_cross⟩ : ∃ α β : E, star α * α = p * p + q * q ∧
      star β * β = r * r + s * s ∧ star β * α = star α * β := by
    refine ⟨p + q * i, r * i - s, ?_⟩
    simp only [star_add, star_sub, star_mul', h_real, hI_star]
    exact ⟨by linear_combination -(q * q : E) * hI_sq, by linear_combination -(r * r : E) * hI_sq,
      by linear_combination -(2 * i : E) * h_im_coe⟩
  let w : Matrix n Unit E := ((α - β * B) / N u) • u + β • v
  have h_norm : form w w = 1 := by
    simp only [w, h_expand, star_div₀, star_sub, star_mul', h_real]
    field_simp
    linear_combination h_re_coe + hα + (N v * N u - B ^ 2 : E) * hβ
      + (star α * β - star β * β * B) * hB + (form v u - B) * h_cross
  exact ⟨w, ext fun _ _ ↦ by simpa only [form, Matrix.mul_assoc, one_apply_eq] using h_norm⟩

/-- If `uᴴ u = 1`, and `u` and `uᴴ` are eigenvectors of `D` with eigenvalue `c`, then shearing by
`1 + u ρ` adds `c (u ρ + (u ρ)ᴴ + ρᴴ ρ)` to `D`. -/
private lemma Core.conjTranspose_one_add_mul_mul_self {R : Type*} [CommRing R] [StarRing R] {c : R}
    {D : Matrix n n R} {u : Matrix n Unit R} (hu : uᴴ * u = 1) (h_column : D * u = c • u)
    (h_row : uᴴ * D = c • uᴴ) (ρ : Matrix Unit n R) :
    (1 + u * ρ)ᴴ * D * (1 + u * ρ) = D + c • (u * ρ + (u * ρ)ᴴ + ρᴴ * ρ) := by
  simp [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, ← Matrix.mul_assoc D u,
    ← Matrix.mul_assoc uᴴ u, h_column, h_row, hu]
  abel

/-- Let `J` be hermitian, `c * c = 1`, `wᴴ (c J) w = 1`, and let `J'` be `J` projected to the
orthogonal complement of `w`. For a matrix `A` there is `A'`, namely `A` with its columns projected
to that complement and `w` added to column `j`, with `A'ᴴ J A' = Aᴴ J' A + c eⱼ eⱼᵀ`. -/
private lemma Core.exists_gram_eq_gram_compl_add_single {J : Matrix n n E} (hJ : Jᴴ = J) {c : E}
    (hc_star : star c = c) (hc : c * c = 1) {w : Matrix n Unit E} (hw : wᴴ * (c • J) * w = 1)
    (A : Matrix n n E) (j : n) :
    ∃ A' : Matrix n n E,
      A'ᴴ * J * A' = Aᴴ * (J - c • J * w * wᴴ * J) * A + Matrix.single j j c := by
  let J' : Matrix n n E := J - c • J * w * wᴴ * J
  let β : Matrix Unit n E := -c • wᴴ * J * A + Matrix.single () j 1
  have hw_norm : wᴴ * J * w = c • 1 := by simp [← hw, smul_smul, hc]
  have hJ'_w : J' * w = 0 := by
    simp [J', Matrix.sub_mul, Matrix.mul_assoc, hw_norm, smul_smul, hc]
  have hw_J' : wᴴ * J' = 0 := by
    simp [J', Matrix.mul_sub, ← Matrix.mul_assoc, hw_norm, smul_smul, hc]
  have h_pair : wᴴ * J * (A + w * β) = c • Matrix.single () j 1 := by
    simp [Matrix.mul_add, ← Matrix.mul_assoc, hw_norm, β, smul_smul, hc]
  use A + w * β
  calc _ = (A + w * β)ᴴ * J' * (A + w * β) +
          c • ((wᴴ * J * (A + w * β))ᴴ * (wᴴ * J * (A + w * β))) := by
        simp [J', hJ, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    _ = Aᴴ * J' * A + Matrix.single j j c := by
        simp [h_pair, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, hJ'_w, hw_J', hc, hc_star,
          ← Matrix.mul_assoc J' w]

variable [HasPrimitiveRoot5040 E]

/-- Hasse principle for partial frames: let `E` satisfy `New.HasPrimitiveRoot5040`, let `J` be
hermitian over `E`, possibly degenerate, let `s` be a family of signs indexed by `n`, and let `D` be
the diagonal matrix with the sign `s i` at `i ∈ t` and `0` elsewhere. If `Xᴴ J X = D` for a square
matrix `X` over the adeles `𝔸 E`, into which `toAdele` embeds `E`, then `Aᴴ J A = D` for a square
matrix `A` over `E`. -/
lemma Core.exists_rat_frame_of_adelic (t : Finset n) {J : Matrix n n E} {X : Matrix n n (𝔸 E)}
    (hJ : Jᴴ = J) (hX : Xᴴ * J.map toAdele * X = ∑ i ∈ t, Matrix.single i i (s i : 𝔸 E)) :
    ∃ A : Matrix n n E, Aᴴ * J * A = ∑ i ∈ t, Matrix.single i i (s i : E) := by
  -- Induction on `t`: split off a rational vector `w` of norm `s j` and pass to its complement.
  induction t using Finset.induction generalizing J X with
  | empty => exact ⟨0, by simp⟩
  | insert j t hj ih =>
    -- `X * u`, column `j` of `X` times the sign `c`, has norm `1` for `c • J`; so has some
    -- rational `w`.
    let c : E := s j
    let u : Matrix n Unit (𝔸 E) := Matrix.single j () (toAdele c)
    set D : Matrix n n (𝔸 E) := ∑ i ∈ insert j t, Matrix.single i i (s i : 𝔸 E)
    have h_column : D * u = toAdele c • u := by
      simp +contextual [D, Matrix.sum_mul, Finset.sum_eq_single j, u, c]
    have hu : uᴴ * u = 1 := by simp [u, c, ← ext_iff, ← Int.cast_mul]
    have h_Xu_norm : (X * u)ᴴ * (c • J).map toAdele * (X * u) = 1 :=
      calc _ = toAdele c • (uᴴ * (Xᴴ * J.map toAdele * X * u)) := by
            simp [map_smul', Matrix.mul_assoc]
        _ = 1 := by simp [hX, h_column, hu, smul_smul, c, ← Int.cast_mul]
    obtain ⟨w, hw⟩ : ∃ w : Matrix n Unit E, wᴴ * (c • J) * w = 1 :=
      exists_form_eq_one (c • J) (by simp [c, hJ]) (X * u) h_Xu_norm
    -- Shear `X` to `X'`: column `j` becomes `0`, and `a * r i` times `X * u` is added to column
    -- `i ≠ j`. Here `r i` is the product of `w` with that column, and `a` has the same norm as
    -- `b = 1 + wᴴ J X u a`.
    let v : Matrix Unit n (𝔸 E) := (wᴴ * J).map toAdele
    let r : Matrix Unit n (𝔸 E) := v * X * (1 + -u * uᴴ)
    obtain ⟨a, b, hb, h_norm⟩ := exists_norm_eq_norm_one_add_mul (v * X * u)
    let ρ : Matrix Unit n (𝔸 E) := a * r + -uᴴ
    let X' : Matrix n n (𝔸 E) := X + X * u * ρ
    have h_pair : v * X' = b * r := by
      simp [← hb, X', ρ, r, Matrix.mul_add, Matrix.mul_assoc, Matrix.add_mul]
      abel
    have h_row : uᴴ * D = toAdele c • uᴴ := by
      simpa [D, conjTranspose_sum, c] using congrArg Matrix.conjTranspose h_column
    have hD : D = (∑ i ∈ t, Matrix.single i i (s i : 𝔸 E)) + toAdele c • (u * uᴴ) := by
      simp [D, u, c, hj, add_comm, ← Int.cast_mul]
    have h_shear : X'ᴴ * J.map toAdele * X' =
        (∑ i ∈ t, Matrix.single i i (s i : 𝔸 E)) + toAdele c • (rᴴ * (aᴴ * a) * r) :=
      calc _ = (1 + u * ρ)ᴴ * D * (1 + u * ρ) := by
            simp [← hX, X', Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
        _ = D + toAdele c • (u * ρ + (u * ρ)ᴴ + ρᴴ * ρ) :=
            conjTranspose_one_add_mul_mul_self hu h_column h_row ρ
        _ = _ := by
            simp [hD, ρ, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
            abel
    -- Let `J'` be `J` projected to the orthogonal complement of `w`. The shear adds `c rᴴ aᴴ a r`
    -- to the Gram matrix for `t`, and the projection subtracts `c rᴴ bᴴ b r`, which is the same.
    let J' : Matrix n n E := J - c • J * w * wᴴ * J
    have h_frame : X'ᴴ * J'.map toAdele * X' = ∑ i ∈ t, Matrix.single i i (s i : 𝔸 E) :=
      calc _ = X'ᴴ * J.map toAdele * X' - toAdele c • ((v * X')ᴴ * (v * X')) := by
            simp [J', v, hJ, Matrix.map_sub, map_smul', Matrix.mul_sub, Matrix.sub_mul,
              Matrix.mul_assoc]
        _ = _ := by simp [h_shear, h_pair, h_norm, Matrix.mul_assoc]
    obtain ⟨A, hA⟩ := ih (by simp [J', c, hJ, Matrix.mul_assoc]) h_frame
    -- Project the columns of `A` to the orthogonal complement of `w` and add `w` to column `j`.
    rw [Finset.sum_insert hj, add_comm, ← hA]
    exact exists_gram_eq_gram_compl_add_single hJ (by simp [c]) (by simp [c, ← Int.cast_mul]) hw A j

/-- A case of Landherr's theorem. Let `E` be a CM field containing a primitive root of unity of
order `5040`, and let a `Space E n s` be a Hermitian matrix `J` over `E` together with an adelic
`x : GL n (𝔸 E)` such that `xᴴ J x` is `diag(s)` at the infinite places and `1` at the finite
places. Then any two such spaces `V`, `W` with the same signs `s` are equivalent over `E`: there is
`a : GL n E` with `aᴴ V.J a = W.J`. -/
lemma Space.landherr (V W : Space E n s) : ∃ a : GL n E, a.valᴴ * V.J * a = W.J := by
  -- The matrix of a space with signs `s` is adelically, so rationally, equivalent to `diag(s)`.
  have h_diag (Y : Space E n s) : ∃ a : GL n E, a.valᴴ * Y.J * a = (signedSpace E s).J := by
    let X : GL n (𝔸 E) := Y.x * (signedSpace E s).x⁻¹
    have h_adelic : X.valᴴ * Y.J.map toAdele * X.val = (signedSpace E s).J.map toAdele :=
      gram_mul_of_gram_eq Y.gram_point (gram_inv_of_gram_eq (signedSpace E s).gram_point)
    obtain ⟨A, hA⟩ : ∃ A : Matrix n n E, Aᴴ * Y.J * A = (signedSpace E s).J := by
      simpa [signedSpace, sum_single_eq_diagonal] using Core.exists_rat_frame_of_adelic (s := s)
        Finset.univ Y.isHermitian_J (h_adelic.trans (by simp [signedSpace, sum_single_eq_diagonal]))
    exact ⟨(isUnit_of_mul_isUnit_right (x := Aᴴ * Y.J)
      (by simp [hA, signedSpace, Pi.isUnit_iff])).unit, hA⟩
  obtain ⟨a, ha⟩ := h_diag V
  obtain ⟨b, hb⟩ := h_diag W
  exact ⟨a * b⁻¹, gram_mul_of_gram_eq ha (gram_inv_of_gram_eq hb)⟩

/-- Landherr's theorem for spaces with a point, for a CM field `E` satisfying
`New.HasPrimitiveRoot5040`. A space `Space E n s` is a Hermitian matrix `J` over `E` with a point
`x : GL n (𝔸 E)` such that `xᴴ J x` is `diag(s)` at the infinite places and `1` at the finite
places. Two spaces `V`, `W` with the same signs `s` differ by a rational change of basis `a` and by
moving the point by some `g` in the adelic unitary group `G E s`: `aᴴ V.J a = W.J`,
`W.x = a⁻¹ V.x g`, and under the embeddings `New.Space.ratEmbed` into `G E s` (sending `γ` to
`x⁻¹ γ x`), the map `γ ↦ a γ a⁻¹` from `U W.J` to `U V.J` becomes conjugation by `g`. Here
`g.toUnitary` is `g` as a matrix over `𝔸 E`, and `toAdele` embeds `E` in `𝔸 E`. -/
lemma Space.exists_x_eq_and_ratEmbed_conj_eq (V W : Space E n s) :
    ∃ (a : GL n E) (g : G E s) (h : a.valᴴ * V.J * a = W.J),
      W.x = (a.map toAdele)⁻¹ * V.x * g.toUnitary ∧
      ∀ γ : U W.J, V.ratEmbed (U.conj a h γ) = g * W.ratEmbed γ * g⁻¹ := by
  obtain ⟨a, ha⟩ := V.landherr W
  -- `a * W.x` is a second frame of `V.J`, so `V.x⁻¹ * a * W.x` preserves the standard form.
  have h_unitary : V.x⁻¹ * (a.map toAdele * W.x) ∈ U (stdForm E s) :=
    gram_mul_of_gram_eq (gram_inv_of_gram_eq V.gram_point)
      (gram_mul_of_gram_eq (by simp [← ha, Matrix.mul_assoc]) W.gram_point)
  refine ⟨a, G.toUnitary.symm ⟨_, h_unitary⟩, ha, by simp [mul_assoc], fun γ ↦ ?_⟩
  simp [ratEmbed, toRatCoords, U.map, MulEquiv.symm_apply_eq, mul_assoc, Subtype.ext_iff]

end New

/-!
## Galois descent and the Hasse principle for unitary cocycles

`New.twistedNorm τ p δ` is the twisted norm `δ · τ δ ⋯ τ^(p-1) δ`; `New.U.mapEnd` and `New.galoisGf`
are the entrywise actions of `σ` on rational and finite adelic unitary matrices.
-/

section UnitaryHassePrinciple

open NumberField Matrix Polynomial UniqueFactorizationMonoid ComplexOrder ComplexEmbedding
  Module Function IsGalois

namespace New

variable {E E' n : Type} [Field E] [NumberField E] [Field E'] [NumberField E']
  [Algebra E E'] [IsGalois E E'] [Fintype n] [DecidableEq n] {σ : Gal(E'/E)}

open scoped Classical in
/-- A normal matrix over a CM field (one commuting with its conjugate transpose) is killed by
the radical of its characteristic polynomial. -/
@[simp]
lemma aeval_radical_charpoly [IsCMField E] {M : Matrix n n E} [IsStarNormal M] :
    aeval M (radical M.charpoly) = 0 := by
  -- The value `N` of the radical at `M` is nilpotent (Cayley–Hamilton) and commutes with `Nᴴ`, so
  -- the trace of `Nᴴ * N` is nilpotent, hence zero; under a complex embedding it is the sum of the
  -- squared norms of the entries of `N`.
  set N : Matrix n n E := aeval M (radical M.charpoly)
  obtain ⟨k, hk⟩ := exists_dvd_radical_self_pow M.charpoly_monic.ne_zero
  have h_nil : IsNilpotent N := ⟨k, by simpa [aeval_self_charpoly] using map_dvd (aeval M) hk⟩
  have h_trace : (Nᴴ * N).trace = 0 := (isNilpotent_trace_of_isNilpotent
    ((commute_conjTranspose_aeval M).isNilpotent_mul_left h_nil)).eq_zero
  simpa [AddMonoidHom.map_trace, conjTranspose_map _ (map_star_complex _), ← ext_iff,
    trace_conjTranspose_mul_self_eq_zero_iff] using congrArg (Φ Classical.ofNonempty) h_trace

/-- For E'/E a Galois extension of number fields of prime degree and σ ≠ 1 in its Galois group,
every element of E' fixed by σ lies in E. -/
lemma mem_range_algebraMap_of_fixed_of_prime (hσ : σ ≠ 1) [Fact (finrank E E').Prime] ⦃x : E'⦄
    (hx : σ x = x) :
    x ∈ (algebraMap E E').range := by
  -- The group has prime order, so every element is a power of `σ`.
  rw [RingHom.mem_range, ← Set.mem_range, mem_range_algebraMap_iff_fixed,
    (bijective_pow_of_ne_one_of_prime_finrank hσ).surjective.forall]
  simp [iterate_fixed hx]

/-- For E'/E a Galois extension of number fields of prime degree and σ ≠ 1 in its Galois group,
every finite adele of E' fixed by σ comes from a finite adele of E. Here `adeleMap σ` is the action
of σ on the finite adeles `𝔸f E'` and `finAdeleIncl E E'` includes the finite adeles of E in
these. -/
lemma mem_range_finAdeleIncl_of_adeleMap_eq (hσ : σ ≠ 1) [Fact (finrank E E').Prime] ⦃x : 𝔸f E'⦄
    (hx : adeleMap σ x = x) : x ∈ (finAdeleIncl E E').range := by
  rw [mem_range_finAdeleIncl_iff, (bijective_pow_of_ne_one_of_prime_finrank hσ).surjective.forall]
  simp [← adeleMap_gal_pow, iterate_fixed hx]

/-- Hasse principle for `H¹(⟨σ⟩, U(n))`, with `U(n) = {g | gᴴ g = 1}`, where `E' / E` is a Galois
extension of CM fields of prime degree `p` and `σ ≠ 1` is in its Galois group. Let `s` be a point
over `E'` such that `s = u σ(u)⁻¹` for a point `u` over the finite adeles of `E'` and the twisted
norm `s σ(s) ⋯ σ^(p-1)(s)` is `1`. Then `s = g σ(g)⁻¹` for a point `g` over `E'`, written as
`σ(g) = s⁻¹ g`. Here `Gf E' n` is the unitary group over the finite adeles, `map` takes `s` into it,
and `U.mapEnd` and `galoisGf` apply `σ` to each entry, `map_star_CM` saying that `σ` commutes with
complex conjugation. Landherr's theorem needs that `E` has a CM type and a primitive root of unity
of order `5040` (`CMType`, `New.HasPrimitiveRoot5040`). -/
lemma U.hasse_principle_coboundary [IsCMField E']
    {E : Type} [Field E] [CMType E] [Algebra E E'] [IsGalois E E']
    {σ : Gal(E'/E)} (hσ : σ ≠ 1) [Fact (finrank E E').Prime]
    [HasPrimitiveRoot5040 E] {s : U (1 : Matrix n n E')} (u : Gf E' n)
    (hs : map (algebraMap E' (𝔸f E')) (fun x : E' ↦ (star_algebraMap_finAdele x).symm)
      (one_map_ringHom (algebraMap E' (𝔸f E'))) s = u * (galoisGf σ u)⁻¹)
    (hs_norm : twistedNorm (mapEnd (map_star_CM σ)) (finrank E E') s = 1) :
    ∃ g : U (1 : Matrix n n E'), mapEnd (map_star_CM σ) g = s⁻¹ * g := by
  -- Hilbert 90 for `GL n` gives `s = g σ(g)⁻¹`. The form `gᴴ g` descends to a matrix `J` over `E`
  -- that is everywhere locally isometric to the standard form, hence globally (Landherr):
  -- `lᴴ J l = 1`. Then `g l` is unitary and still splits `s`.
  let a : E' →+* 𝔸f E' := algebraMap E' (𝔸f E')
  have h_norm : twistedNorm (GeneralLinearGroup.map (σ : E' →+* E')) (orderOf σ) s.1 = 1 := by
    rw [orderOf_eq_prime (p := finrank E E') (by simp [← card_aut_eq_finrank]) hσ,
      ← map_one (U (1 : Matrix n n E')).subtype, ← hs_norm]
    exact (map_twistedNorm (U (1 : Matrix n n E')).subtype (fun _ ↦ rfl) _ s).symm
  -- Hilbert 90 at level `1`, where the congruence condition always holds
  obtain ⟨g, -, hg : s.1.1 * g.1.map (σ : E' →+* E') = g.1, -⟩ :=
    (isTameAtLevel_gal σ).hilbert90_gl (Y := s.1.1 - 1) (.inl inferInstance) s.1
      (by simp) h_norm
  -- `u⁻¹ g` is fixed by `σ`, since `s` is split by both `u` and `g`; so it comes from `E`.
  have hs_mat : s.1.1.map a = (u * (galoisGf σ u)⁻¹).1.1 := congrArg (fun x : Gf E' n ↦ x.1.1) hs
  have h_fixed_adelic : (u.1⁻¹ * g.map a).map (adeleMap σ) = u.1⁻¹ * g.map a := by
    have hg_adelic : (u⁻¹).1.1 * (s.1.1 * g.1.map (σ : E' →+* E')).map a =
        (u⁻¹).1.1 * g.1.map a := by rw [hg]
    -- `using!` identifies the inverse in `Gf E' n` with that in `GL n (𝔸f E')`.
    exact Units.ext <| by simpa [a, hs_mat, comp_def, mul_assoc] using! hg_adelic
  obtain ⟨y, hy⟩ : ∃ y : GL n (𝔸f E), y.map (adeleMap (algebraMap E E')) = u.1⁻¹ * g.map a :=
    exists_gl_map_eq_of_fixed (adeleMap_injective _) (mem_range_finAdeleIncl_of_adeleMap_eq hσ)
      h_fixed_adelic
  -- `gᴴ g` is fixed by `σ`, since `s` is unitary; so it comes from `E` too.
  have h_fixed_form : (star g * 1 * g).map (σ : E' →+* E') = star g * 1 * g := by
    refine Units.ext ?_
    simpa [star, conjTranspose_map _ (map_star_CM _), ← inv_val_eq_conjTranspose, mul_assoc,
      -RingHom.coe_coe] using congrArg (fun M : Matrix n n E' ↦ Mᴴ * M) hg
  obtain ⟨J, hJ⟩ : ∃ J : GL n E, J.map (algebraMap E E') = star g * 1 * g :=
    exists_gl_map_eq_of_fixed (RingHom.injective _) (mem_range_algebraMap_of_fixed_of_prime hσ)
      h_fixed_form
  have hJ_mat : g.1ᴴ * 1 * g.1 = J.1.map (algebraMap E E') := congrArg Units.val hJ.symm
  -- Local isometries: `g` at the infinite places, `y` at the finite places.
  have h_infinite (w : InfinitePlace E) :
      (g.map (lift E' (Φ w))).1ᴴ * signMatrix (1 : n → ℤˣ) * (g.map (lift E' (Φ w))).1 =
        J.1.map (Φ w) := by
    simpa [← ext_iff, mul_apply] using congrArg (Matrix.map · (lift E' (Φ w))) hJ_mat
  have h_adelic : (g.map a).1ᴴ * 1 * (g.map a).1 = J.1.map (a ∘ algebraMap E E') := by
    simpa [← ext_iff, mul_apply, a] using congrArg (Matrix.map · a) hJ_mat
  have h_finite : y.1ᴴ * 1 * y.1 = J.1.map (algebraMap E (𝔸f E)) := by
    apply map_injective (adeleMap_injective (algebraMap E E'))
    -- `y` becomes `u⁻¹ g` over `E'`, and `u⁻¹` is unitary.
    simpa [← hy, comp_def, ↓map_conjTranspose_mul_mul, adeleMap_star] using!
      gram_mul_of_gram_eq u⁻¹.2 h_adelic
  -- Landherr's theorem compares the space of `J` with the standard space `stdSpace E n`.
  let V : Space E n 1 := ⟨J, _, gram_mkAdelicGL (fun w ↦ gram_inv_of_gram_eq (h_infinite w))
    (gram_inv_of_gram_eq h_finite)⟩
  obtain ⟨l, hl : l.1ᴴ * J.1 * l.1 = (stdSpace E n).J⟩ := V.landherr (stdSpace E n)
  refine ⟨⟨g * l.map (algebraMap E E'), gram_mul_of_gram_eq hJ_mat ?_⟩, eq_inv_mul_of_mul_eq ?_⟩
  · simp [← map_conjTranspose_mul_mul, map_star_CM, hl, stdSpace]
  · -- `σ` fixes `l`, so `s σ(g l) = s σ(g) l = g l`.
    ext
    simp only [RingHom.coe_coe] at hg
    simp [U.map, ← mul_assoc, comp_def, hg]

end New

end UnitaryHassePrinciple
