import Lib.GaloisRep.BaseChange.PrimeDegreeTransfer
import Lib.GaloisRep.LocalGlobal.LocalFormTypes
import Lib.LocalGL.Iwahori.HeckeDegrees

/-!
# Hilbert 90 for the pro-p Iwahori group and base change of Iwahori eigenforms

`F` is a valued field with compact ring of integers, and `σ` is an isometric endomorphism with
`σ ^ p = 1`. `New.proIwahori` is the pro-`p` Iwahori subgroup of `GL n F`, the matrices that are
upper unitriangular modulo the maximal ideal. `New.twistedNorm τ p δ = δ * τ δ * ⋯ * τ ^ (p - 1) δ`
is the twisted norm. The file proves a Hilbert 90 statement and a matching of dominant double cosets
for this group. These local results give matching local data at a place with exactly one place above
it.

## Main definitions and results

* `New.exists_coboundary_proIwahori`: if some integer of `F` has `σ`-trace `1`, an element of
  `New.proIwahori` of norm `1` is a coboundary `t * (σ t)⁻¹` with `t` in `New.proIwahori`.
* `New.proIwahori_doubleCoset_match`: the double cosets of a strictly dominant diagonal matrix over
  `F` and of its norm over the fixed field correspond under `γ ↦ z γ` for a polynomial `z`
  (`New.IsIwahoriMatchingPolynomial`).
* `New.isLocalMatching_proIwahori`: the indicator functions of the double cosets `K N(t) K` at `w`
  and `K' t K'` at `u` are matching local data (`New.IsLocalMatching`). It globalises
  `New.proIwahori_doubleCoset_match` and `New.exists_coboundary_proIwahori`.
* `New.exists_baseChange_isIwahoriEigen`: feeding these into
  `New.exists_isWeakBaseChange_of_matching` gives a base change whose eigencharacter at `u` is that
  of `f` at `w` composed with `N`.

Notions from other files:
* `New.IsStep E' μ`: a step `E'/E`. The field `E` contains a primitive `5040`-th root of unity,
  `E'` is a CM field Galois over `E` of prime degree with an integer of trace `1`, and `μ` is the
  character of the finite ideles of `E` that goes with the extension.
* `New.locIdele`: the homomorphism that sends `x` in the units of the completion at `v` to the
  finite idele with component `x` at `v` and `1` elsewhere.
* `New.iwahoriDoubleCoset t`: the double coset `K t K` of the diagonal matrix `t`, where `K` is
  `New.proIwahori`.
* `New.diagGL t`: the diagonal matrix with the units `t i` on the diagonal, as an element of `GL`.

## Relation to the literature

Known; see `Lib.GaloisRep.BaseChange.PrimeDegreeTransfer` for sources.
-/

namespace New

/-!
## Hilbert 90 and matching of dominant double cosets

The matching uses that such a double coset is `σ`-conjugate into the torus
(`New.exists_inv_mul_mul_map_eq_diagGL_mul`) and that the eigenvalues are told apart by their
valuations.
-/

section IwahoriMatching

open Matrix WithZero Valued Polynomial GeneralLinearGroup DoubleCoset Finset Function

variable {F F' : Type*}
  {N : ℕ} [Field F] [Valued F ℤᵐ⁰] [Field F'] [Valued F' ℤᵐ⁰]
  [CompactSpace 𝒪[F']] {σ : F →+* F} {p : ℕ}

/-- Let `σ` be an endomorphism of `F` that keeps the valuation. Then `g ∈ GL N F` lies in the
pro-`p` Iwahori subgroup `New.proIwahori` exactly when `σ g`, with `σ` applied to the entries,
does. -/
lemma map_mem_proIwahori_iff_of_isometry (hv : ∀ x : F, v (σ x) = v x) {g : GL (Fin N) F} :
    g.map σ ∈ proIwahori ↔ g ∈ proIwahori :=
  map_mem_proIwahori_iff_of_isEquiv (.of_eq (Valuation.ext hv : v.comap σ = v))

lemma v_ringHom_pow_apply (hv : ∀ x : F, v (σ x) = v x) (i : ℕ) (x : F) :
    v ((σ ^ i) x) = v x := by
  rw [RingHom.coe_pow]
  induction i with
  | zero => rfl
  | succ i ih => rw [iterate_succ_apply', hv, ih]

/-- Hilbert 90 for the pro-`p` Iwahori subgroup `New.proIwahori` of `GL N F`. Let `σ` be an
endomorphism of `F` that keeps the valuation, with `σ ^ p = 1`, and let `c` be an integer of `F`
with trace `∑ i < p, σ ^ i c = 1`. If `s ∈ proIwahori` has twisted norm
`s * σ s * ⋯ * σ ^ (p - 1) s = 1` (`New.twistedNorm`, with `σ` acting on the entries), then
`s * σ t = t` for some `t ∈ proIwahori`. -/
lemma exists_coboundary_proIwahori (hv : ∀ x : F, v (σ x) = v x) (hσ : σ ^ p = 1) {c : F}
    (hc_int : v c ≤ 1) (hc_trace : ∑ i ∈ range p, (σ ^ i) c = 1)
    {s : GL (Fin N) F} (hs_mem : s ∈ proIwahori) (hs_norm : twistedNorm (.map σ) p s = 1) :
    ∃ t ∈ proIwahori, s * t.map σ = t := by
  -- Take `t = ∑ l < p, σ ^ l c • n l`, where `n l` is the partial twisted norm of `s` of length
  -- `l`. Every `n l` lies in `proIwahori`, which gives three conditions on its entries.
  have h_partial (l : ℕ) :
      (∀ i j : Fin N, v (twistedNorm (.map σ) l s i j) ≤ 1) ∧
      (∀ i : Fin N, ∀ j < i, v (twistedNorm (.map σ) l s i j) < 1) ∧
      ∀ i : Fin N, v (twistedNorm (.map σ) l s i i - 1) < 1 :=
    mem_proIwahori.mp <| twistedNorm_mem (GeneralLinearGroup.map σ) l
      (fun _ ↦ (map_mem_proIwahori_iff_of_isometry hv).mpr) hs_mem
  let a (l : ℕ) : Matrix (Fin N) (Fin N) F := (σ ^ l) c • (twistedNorm (.map σ) l s).val
  let M : Matrix (Fin N) (Fin N) F := ∑ l ∈ range p, a l
  choose hn_int hn_below hn_diag using h_partial
  have hc_pow (l : ℕ) : v ((σ ^ l) c) ≤ 1 := by rwa [v_ringHom_pow_apply hv]
  have h_int (i j : Fin N) : v (M i j) ≤ 1 := by
    simp only [M, a, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    exact v.map_sum_le fun l _ ↦ (v.map_mul _ _).trans_le (mul_le_one' (hc_pow l) (hn_int l i j))
  -- Modulo the maximal ideal `M` is upper triangular, with diagonal entries `∑ σ ^ l c = 1`.
  have h_below (i j : Fin N) (hij : j < i) : v (M i j) < 1 := by
    simp only [M, a, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    exact v.map_sum_lt one_ne_zero fun l _ ↦
      (v.map_mul _ _).trans_lt (mul_lt_of_le_one_of_lt (hc_pow l) (hn_below l i j hij))
  have h_diag (i : Fin N) : v (M i i - 1) < 1 := by
    have h_sub : M i i - 1 = ∑ l ∈ range p, (σ ^ l) c * (twistedNorm (.map σ) l s i i - 1) := by
      simp [M, a, Matrix.sum_apply, mul_sub_one, hc_trace, -RingHom.coe_pow]
    rw [h_sub]
    exact v.map_sum_lt one_ne_zero fun l _ ↦
      (v.map_mul _ _).trans_lt (mul_lt_of_le_one_of_lt (hc_pow l) (hn_diag l i))
  obtain ⟨t, ht, htM⟩ : ∃ t ∈ proIwahori, t.val = M :=
    exists_proIwahori_coe_eq_of_residue_unitriangular M h_int h_below h_diag
  -- The map `τ : m ↦ s * σ m` sends the term `a l` of `M` to `a (l + 1)`, and `a p = a 0` as
  -- `σ ^ p = 1` and `s` has norm `1`; so `τ` fixes the sum `M`.
  let τ : Matrix (Fin N) (Fin N) F →+ Matrix (Fin N) (Fin N) F :=
    (AddMonoidHom.mulLeft s.val).comp σ.mapMatrix.toAddMonoidHom
  have h_period : a p = a 0 := by
    simp only [a, hσ, hs_norm]
    simp [twistedNorm]
  have h_succ (l : ℕ) : a (l + 1) = τ (a l) := by
    simp [a, τ, pow_succ', twistedNorm_succ', map_smul', -RingHom.coe_pow]
  refine ⟨t, ht, Units.ext ?_⟩
  change τ t.val = t.val
  rw [htM, fixed_sum τ a h_period h_succ]

/-- Let `σ` be a continuous endomorphism of `F` that keeps the valuation, with `σ ^ p = 1` for some
`p > 0`, and let `t` be diagonal with `v (t i)` strictly increasing. Let `K` be the pro-`p` Iwahori
subgroup `New.proIwahori`. Every `δ` in the double coset `K t K` (`New.iwahoriDoubleCoset t`) is
`σ`-conjugate to `t * d` for some `d` diagonal in `K`: `k⁻¹ * δ * σ k = t * d` with `k ∈ K`. The
same `k` conjugates the twisted norm of `δ` (`New.twistedNorm`) to that of `t * d`. -/
private lemma exists_twisted_conj_diag_and_twistedNorm_conj [CompactSpace 𝒪[F]]
    (hv : ∀ x : F, v (σ x) = v x)
    (hσ : σ ^ p = 1) (hp : 0 < p) (hσ_cont : Continuous σ) {t : Fin N → Fˣ}
    (ht_mono : StrictMono fun i : Fin N ↦ v (t i).val) {δ : GL (Fin N) F}
    (hδ : δ ∈ iwahoriDoubleCoset t) :
    ∃ k ∈ proIwahori, ∃ d : Fin N → Fˣ, diagGL d ∈ proIwahori ∧
      k⁻¹ * δ * k.map σ = diagGL (t * d) ∧
      k⁻¹ * twistedNorm (.map σ) p δ * k = twistedNorm (.map σ) p (diagGL (t * d)) := by
  -- As `σ ^ p = 1` with `p > 0`, `σ` acts on `GL N F` with period `p`, hence onto.
  have h_iterate (i : ℕ) (k : GL (Fin N) F) : (map (n := Fin N) σ)^[i] k = k.map (σ ^ i) := by
    induction i generalizing k with
    | zero => rfl
    | succ i ih => exact ih (k.map σ)
  have h_period (k : GL (Fin N) F) : (map (n := Fin N) σ)^[p] k = k := by
    simp [h_iterate, hσ, RingHom.one_def]
  obtain ⟨k, hk, d, hd, h_conj⟩ := exists_inv_mul_mul_map_eq_diagGL_mul ht_mono σ hv hσ_cont
    (fun k ↦ periodicPts_subset_range ⟨p, hp, h_period k⟩) hδ
  refine ⟨k, hk, d, hd, h_conj, ?_⟩
  -- A twisted conjugation by `k`, which is fixed by `σ ^ p`, conjugates twisted norms.
  rw [← h_conj, twistedNorm_conj (GeneralLinearGroup.map σ) p (h_period k)]

/-- A point `x` of the double coset `K' s K'` over `F'` (`New.iwahoriDoubleCoset s`) is sent by `ι`
to a conjugate, by some `k ∈ New.proIwahori`, of the twisted norm (`New.twistedNorm`) of
`diagGL (t * d)` with `diagGL d ∈ New.proIwahori`. This uses that `ι s` is the twisted norm of
`diagGL t` (`hs_norm`) and that the `1`-units of `F'` are norms of `1`-units of `F` (`h_norms`). -/
private lemma exists_conj_map_eq_twistedNorm_diagGL {ι : F' →+* F} (h_val : (v.comap ι).IsEquiv v)
    (h_norms : ∀ x : F', v (ι x - 1) < 1 → ∃ y : Fˣ,
      v (y.val - 1) < 1 ∧ ∏ i ∈ range p, (σ ^ i) y = ι x)
    {t : Fin N → Fˣ} {s : Fin N → F'ˣ} (hs_mono : StrictMono fun i : Fin N ↦ v (s i).val)
    (hs_norm : (diagGL s).map ι = twistedNorm (GeneralLinearGroup.map σ) p (diagGL t))
    {x : GL (Fin N) F'} (hx : x ∈ iwahoriDoubleCoset s) :
    ∃ k ∈ proIwahori, ∃ d : Fin N → Fˣ, diagGL d ∈ proIwahori ∧
      k⁻¹ * x.map ι * k = twistedNorm (.map σ) p (diagGL (t * d)) := by
  -- With the trivial twist, `x` is conjugate to `diagGL (s * e)` with `e` diagonal in `K'`. The
  -- entries of `ι e` are norms of units `d i`, and then `ι (s * e)` is the twisted norm of
  -- `diagGL (t * d)`.
  obtain ⟨k, hk, e, he_mem, h_conj⟩ :=
    exists_inv_mul_mul_map_eq_diagGL_mul hs_mono (1 : F' →+* F') (by simp) continuous_id
      surjective_id hx
  have he_sub_one (i : Fin N) : v (ι (e i : F') - 1) < 1 := by
    simpa using h_val.lt_one_iff_lt_one.mpr (diagGL_mem_proIwahori.mp he_mem i)
  choose d hd hd_norm using fun i : Fin N ↦ h_norms (e i) (he_sub_one i)
  refine ⟨k.map ι, (map_mem_proIwahori_iff_of_isEquiv h_val).mpr hk, d,
    diagGL_mem_proIwahori.mpr hd, Units.ext ?_⟩
  -- Apply `ι` to `k⁻¹ * x * k = diagGL (s * e)` and compare the diagonal entries.
  rw [twistedNorm_diagGL]
  simpa [Units.ext_iff, hs_norm, hd_norm, prod_mul_distrib, -RingHom.coe_pow] using
    congrArg (GeneralLinearGroup.map ι) h_conj

/-- Let `σ` be an endomorphism of `F` that keeps the valuation, let `p > 0`, let `t` be diagonal
with `v (t i)` strictly increasing, and let `d`, `d'` be diagonal in the pro-`p` Iwahori subgroup
`New.proIwahori`. If the norms `∏ l < p, σ ^ l (t i * d i)` and `∏ l < p, σ ^ l (t j * d' j)` agree,
then `i = j`, since the valuation of the first is `v (t i) ^ p`. -/
private lemma eq_of_prod_ringHom_pow_apply_eq (hv : ∀ x : F, v (σ x) = v x) (hp : 0 < p)
    {t d d' : Fin N → Fˣ} (ht_mono : StrictMono fun i : Fin N ↦ v (t i).val)
    (hd : diagGL d ∈ proIwahori) (hd' : diagGL d' ∈ proIwahori) (i j : Fin N)
    (h_eq : ∏ l ∈ range p, (σ ^ l) ((t * d) i : F) = ∏ l ∈ range p, (σ ^ l) ((t * d') j : F)) :
    i = j := by
  have h_unit {e : Fin N → Fˣ} (he_mem : diagGL e ∈ proIwahori) (m : Fin N) : v (e m : F) = 1 := by
    simpa using v_diag_eq_one_of_mem_proIwahori he_mem m
  refine ht_mono.injective (show v (t i : F) = v (t j : F) from ?_)
  simpa [hp.ne', h_unit hd, h_unit hd', v_ringHom_pow_apply hv, -RingHom.coe_pow] using
    congrArg v h_eq

omit [Valued F ℤᵐ⁰] in
/-- Let `σ ^ p = 1`, and let the values `c i = ∏ l < p, σ ^ l (e i)` be distinct. If the polynomial
`z` takes the value `e i` at `c i` for every `i`, then the characteristic polynomial
`∏ i, (X - c i)` of `diagonal c` divides `N(z) - X`, where `N(z) = ∏ l < p, σ ^ l z` is the
twisted norm (`New.twistedNorm`) of `z`. -/
private lemma charpoly_diagonal_dvd_twistedNorm_sub_X (hσ : σ ^ p = 1) {c e : Fin N → F}
    (hc_inj : Injective c) (hc : ∀ i : Fin N, c i = ∏ l ∈ range p, (σ ^ l) (e i)) {z : F[X]}
    (hz : ∀ i : Fin N, z.eval (c i) = e i) :
    (diagonal c).charpoly ∣ twistedNorm (Polynomial.map σ) p z - X := by
  -- The roots `c i` are distinct, so it suffices that each is a root of `N(z) - X`. As `c i` is a
  -- norm, it is fixed by `σ`, so `(σ ^ l z) (c i) = σ ^ l (z (c i)) = σ ^ l (e i)`.
  rw [charpoly_diagonal]
  refine Fintype.prod_dvd_of_coprime (pairwise_coprime_X_sub_C hc_inj) fun i ↦ ?_
  have h_eval_map (l : ℕ) : (z.map (σ ^ l)).eval (c i) = (σ ^ l) (e i) := by
    rw [← hz, ← eval_map_apply, σ.coe_pow, hc, (isFixedPt_prod_range_pow_apply hσ).iterate]
  have h_eval_norm : (twistedNorm (Polynomial.map σ) p z).eval (c i) = c i := by
    rw [twistedNorm_map_eq_prod, eval_prod]
    exact (prod_congr rfl fun l _ ↦ h_eval_map l).trans (hc i).symm
  rw [dvd_iff_isRoot, IsRoot.def, eval_sub, eval_X, h_eval_norm, sub_self]

omit [Valued F ℤᵐ⁰] in
/-- Let `γ` have the characteristic polynomial of the diagonal matrix `diagonal c`, and let
`k⁻¹ * γ * k = diagonal c'`, where `c' i = c l` holds only for `i = l`. Then for every polynomial
`z` the matrix `z γ` is `k * diagonal (z ∘ c) * k⁻¹`. -/
private lemma aeval_eq_conj_diagonal_eval {c c' : Fin N → F} {k γ : GL (Fin N) F}
    (hγ : γ.val.charpoly = (diagonal c).charpoly) (h_conj : (k⁻¹ * γ * k).val = diagonal c')
    (h_inj : ∀ i l : Fin N, c' i = c l → i = l) (z : F[X]) :
    aeval γ.val z = k.val * diagonal (fun i : Fin N ↦ z.eval (c i)) * k⁻¹.val := by
  -- Each `c' i` is a root of the characteristic polynomial of `γ`, so it is some `c l`, and then
  -- `l = i`. So `k` intertwines `diagonal c` with `γ`, hence `z (diagonal c)` with `z γ`.
  have h_charpoly : (diagonal c').charpoly = (diagonal c).charpoly := by
    simp only [← h_conj, Units.val_mul, coe_units_inv, charpoly_units_conj', hγ]
  have h_eq : c' = c := by
    funext i
    have h_root : (diagonal c).charpoly.eval (c' i) = 0 := by
      simp [← h_charpoly, charpoly_diagonal, eval_prod, prod_eq_zero_iff, sub_eq_zero]
    obtain ⟨l, hl⟩ : ∃ l : Fin N, c' i = c l := by
      simpa [charpoly_diagonal, eval_prod, prod_eq_zero_iff, sub_eq_zero] using h_root
    rw [hl, h_inj i l hl]
  have h_semi : k.val * diagonalAlgHom F c = γ.val * k.val := by
    simp [← h_eq, ← h_conj, ← mul_assoc]
  have h_aeval_diag : aeval (diagonalAlgHom F c) z = diagonal fun i : Fin N ↦ z.eval (c i) := by
    rw [aeval_algHom_apply, diagonalAlgHom_apply, aeval_pi_apply]
    simp
  rw [← h_aeval_diag, aeval_semiconj h_semi z, mul_assoc, Units.mul_inv, mul_one]

omit [CompactSpace 𝒪[F']] in
/-- Descent for clause (a) of `New.proIwahori_doubleCoset_match`. Let `σ` preserve `v` and let the
`σ`-fixed elements of `F` lie in the range of `ι : F' →+* F`, with `v ∘ ι` equivalent to `v`. Let
`ι (diagGL s)` be the twisted norm (`New.twistedNorm`, over `σ`, `p` factors) of `diagGL t`, and let
`k, diagGL d ∈ New.proIwahori`, `a = k * diagGL (t * d₀) * k⁻¹` and
`k⁻¹ * a * σ k = diagGL (t * d)`. If `k⁻¹ * ι x * k` is the twisted norm of `diagGL (t * d)`, then
`x` lies in `I₁ diag(s) I₁` over `F'` (`New.iwahoriDoubleCoset s`). -/
private lemma mem_iwahoriDoubleCoset_of_conj_map_eq_twistedNorm (hv : ∀ x : F, v (σ x) = v x)
    {ι : F' →+* F} (h_range : ∀ x : F, σ x = x → x ∈ ι.range) (h_val : (v.comap ι).IsEquiv v)
    {t : Fin N → Fˣ} {s : Fin N → F'ˣ}
    (hs_norm : (diagGL s).map ι = twistedNorm (GeneralLinearGroup.map σ) p (diagGL t))
    {k a : GL (Fin N) F} (hk : k ∈ proIwahori) {d₀ d : Fin N → Fˣ} (hd : diagGL d ∈ proIwahori)
    (h_twist : k⁻¹ * a * k.map σ = diagGL (t * d)) (ha : k * diagGL (t * d₀) * k⁻¹ = a)
    {x : GL (Fin N) F'} (hx : k⁻¹ * x.map ι * k = twistedNorm (.map σ) p (diagGL (t * d))) :
    x ∈ iwahoriDoubleCoset s := by
  -- Let `e` be the diagonal of `k`. As `σ` multiplies each column of `k` by a scalar,
  -- `k * diagGL e⁻¹` is fixed by `σ`, so it is `ι g` for some `g` over `F'`. Then `x = g * s * r`,
  -- where `ι r = diagGL e * N(diagGL d) * k⁻¹` lies in `proIwahori`, as the twisted norm
  -- `N(t * d)` is `N(t) * N(d) = ι s * N(d)`.
  have hk_map : k.map σ = k * ((diagGL (t * d₀))⁻¹ * diagGL (t * d)) := by
    rw [← h_twist, ← ha]
    group
  have hσk (i j : Fin N) : σ (k i j) = k i j * (((t * d₀) j : F)⁻¹ * (t * d) j) := by
    simpa [← map_inv, mul_assoc] using congrArg (fun g : GL (Fin N) F ↦ g i j) hk_map
  have hk_diag (i : Fin N) : k i i ≠ 0 :=
    v.ne_zero_iff.mp (by simp [v_diag_eq_one_of_mem_proIwahori hk i])
  let e (i : Fin N) : Fˣ := .mk0 (k i i) (hk_diag i)
  obtain ⟨-, -, hk_diag_one⟩ := mem_proIwahori.mp hk
  have he_mem : diagGL e ∈ proIwahori := diagGL_mem_proIwahori.mpr hk_diag_one
  have h_fixed : (k * diagGL e⁻¹).map σ = k * diagGL e⁻¹ := by
    -- `map_inv` is left out: it would turn the diagonal of inverses into a matrix inverse.
    simp [Units.ext_iff, ← ext_iff, -map_inv, hσk, e, mul_assoc]
  obtain ⟨g, hg⟩ : ∃ g : GL (Fin N) F', g.map ι = k * diagGL e⁻¹ :=
    exists_gl_map_eq_of_fixed ι.injective h_range h_fixed
  have h_map_r : ((g * diagGL s)⁻¹ * x).map ι =
      ((diagGL s).map ι)⁻¹ * (diagGL e * (k⁻¹ * x.map ι * k)) * k⁻¹ := by
    simp only [map_mul, map_inv, hg]
    group
  -- The diagonal matrices `diagGL e`, `N(t)` and `N(d)` commute, and `N(t * d) = N(t) * N(d)`.
  have h_diag_eq : diagGL e * twistedNorm (.map σ) p (diagGL (t * d)) =
      (diagGL s).map ι * (diagGL e * twistedNorm (.map σ) p (diagGL d)) := by
    simp only [hs_norm, Units.ext_iff, Units.val_mul, twistedNorm_diagGL]
    simp [prod_mul_distrib, mul_left_comm]
  have hr : ((g * diagGL s)⁻¹ * x).map ι = diagGL e * twistedNorm (.map σ) p (diagGL d) * k⁻¹ := by
    rw [h_map_r, hx, h_diag_eq, inv_mul_cancel_left]
  have hg_mem : g ∈ proIwahori := by
    rw [← map_mem_proIwahori_iff_of_isEquiv h_val, hg, map_inv]
    exact mul_mem hk (inv_mem he_mem)
  have hr_mem : (g * diagGL s)⁻¹ * x ∈ proIwahori := by
    rw [← map_mem_proIwahori_iff_of_isEquiv h_val, hr]
    exact mul_mem (mul_mem he_mem (twistedNorm_mem (GeneralLinearGroup.map σ) p
      (fun _ ↦ (map_mem_proIwahori_iff_of_isometry hv).mpr) hd)) (inv_mem hk)
  exact mem_doubleCoset.mpr ⟨g, hg_mem, _, hr_mem, (mul_inv_cancel_left _ x).symm⟩

/-- Let `σ` be an endomorphism of `F` that keeps the valuation, let `k`, `diagGL d₀` and `diagGL d`
lie in the pro-`p` Iwahori subgroup `New.proIwahori`, and let `k⁻¹ * δ * σ k = diagGL (t * d)` and
`a = k * diagGL (t * d₀) * k⁻¹`. Then `a⁻¹ * δ = k * diagGL (d₀⁻¹ * d) * (σ k)⁻¹` lies in
`New.proIwahori`. -/
private lemma inv_mul_mem_proIwahori_of_twisted_conj (hv : ∀ x : F, v (σ x) = v x)
    {t d₀ d : Fin N → Fˣ} {k a δ : GL (Fin N) F} (hk : k ∈ proIwahori)
    (hd₀ : diagGL d₀ ∈ proIwahori) (hd : diagGL d ∈ proIwahori)
    (h_twist : k⁻¹ * δ * k.map σ = diagGL (t * d)) (ha : k * diagGL (t * d₀) * k⁻¹ = a) :
    a⁻¹ * δ ∈ proIwahori := by
  have h_quot : a⁻¹ * δ = k * ((diagGL d₀)⁻¹ * diagGL d) * (k.map σ)⁻¹ := by
    rw [← ha, ← inv_mul_cancel_left (diagGL t) (diagGL d), ← map_mul, ← h_twist, map_mul]
    group
  rw [h_quot]
  exact mul_mem (mul_mem hk (mul_mem (inv_mem hd₀) hd))
    (inv_mem ((map_mem_proIwahori_iff_of_isometry hv).mpr hk))

variable (σ p) in
/-- The polynomial `z` over `F` matches the double cosets `K' s K'` over `F'` and `K t K` over `F`
at the polynomial `P`. Here `K`, `K'` are the pro-`p` Iwahori subgroups `New.proIwahori`, the
double cosets are `New.iwahoriDoubleCoset`, twisted norms (`New.twistedNorm`) are taken with the
endomorphism `σ` of `F` and length `p`, and `ι : F' →+* F`. In the last two fields `γ` has
characteristic polynomial `P` and `a = z γ`. -/
structure IsIwahoriMatchingPolynomial (ι : F' →+* F) (s : Fin N → F'ˣ) (t : Fin N → Fˣ)
    (P z : F[X]) : Prop where
  /-- The twisted norm `z * σ z * ⋯ * σ ^ (p - 1) z` is `X` modulo `P`. -/
  dvd_twistedNorm_sub_X : P ∣ twistedNorm (Polynomial.map σ) p z - X
  /-- If `γ = ι x` and `γ` is the twisted norm of `a`, then `x ∈ K' s K'` exactly when
  `a ∈ K t K`. -/
  mem_iwahoriDoubleCoset_iff : ∀ γ a : GL (Fin N) F, γ.val.charpoly = P → a.val = aeval γ.val z →
    ∀ x : GL (Fin N) F', x.map ι = γ → twistedNorm (GeneralLinearGroup.map σ) p a = γ →
      (x ∈ iwahoriDoubleCoset s ↔ a ∈ iwahoriDoubleCoset t)
  /-- Every `δ ∈ K t K` with twisted norm `γ` has `a⁻¹ * δ ∈ K`, so it lies in the coset `a K`. -/
  inv_mul_mem_proIwahori : ∀ γ a : GL (Fin N) F, γ.val.charpoly = P → a.val = aeval γ.val z →
    ∀ δ ∈ iwahoriDoubleCoset t, twistedNorm (GeneralLinearGroup.map σ) p δ = γ →
      a⁻¹ * δ ∈ proIwahori

/-- Matching at pro-`p` Iwahori level. Let `σ` be a continuous endomorphism of `F` that keeps the
valuation, with `σ ^ p = 1` and `p > 0`. Let `ι : F' →+* F` be a map whose image holds the points
fixed by `σ` (`h_range`), along which `v` restricts to a valuation equivalent to that of `F'`
(`h_val`), and such that every `x` with `v (ι x - 1) < 1` has `ι x = ∏ i < p, σ ^ i y` for a unit
`y` with `v (y - 1) < 1` (`h_norms`). Let `t` over `F` and `s` over `F'` have strictly increasing
valuations, with `ι (diagGL s)` the twisted norm (`New.twistedNorm`) of `diagGL t`. Let `P` be the
characteristic polynomial of `ι x` for `x` in `K' s K'`, or of the twisted norm of a point of
`K t K` (`New.iwahoriDoubleCoset`, with `K`, `K'` the groups `New.proIwahori`). Then some polynomial
`z` matches the two double cosets at `P` (`New.IsIwahoriMatchingPolynomial`): its twisted norm is
`X` modulo `P`, and for `γ` with characteristic polynomial `P` and `a = z γ`, (a) if `γ = ι x` is
the twisted norm of `a`, then `x ∈ K' s K' ↔ a ∈ K t K`; (b) every `δ ∈ K t K` with twisted norm `γ`
lies in `a K`. -/
lemma proIwahori_doubleCoset_match [CompactSpace 𝒪[F]]
    (hv : ∀ x : F, v (σ x) = v x) (hσ : σ ^ p = 1) (hp : 0 < p)
    (hσ_cont : Continuous σ) {ι : F' →+* F}
    (h_range : ∀ x : F, σ x = x → x ∈ ι.range) (h_val : (v.comap ι).IsEquiv v)
    (h_norms : ∀ x : F', v (ι x - 1) < 1 → ∃ y : Fˣ,
      v (y.val - 1) < 1 ∧ ∏ i ∈ range p, (σ ^ i) y = ι x)
    {t : Fin N → Fˣ} {s : Fin N → F'ˣ} (ht_mono : StrictMono fun i : Fin N ↦ v (t i).val)
    (hs_mono : StrictMono fun i : Fin N ↦ v (s i).val)
    (hs_norm : (diagGL s).map ι = twistedNorm (GeneralLinearGroup.map σ) p (diagGL t)) (P : F[X])
    (hP : P ∈ (fun γ : GL (Fin N) F ↦ γ.val.charpoly) ''
      (GeneralLinearGroup.map ι '' iwahoriDoubleCoset s ∪
        twistedNorm (GeneralLinearGroup.map σ) p '' iwahoriDoubleCoset t)) :
    ∃ z : F[X], IsIwahoriMatchingPolynomial σ p ι s t P z := by
  -- Points of `iwahoriDoubleCoset s` and norms from `iwahoriDoubleCoset t` are conjugate under
  -- `proIwahori` to diagonal matrices `ν d`, the norms of `diagGL (t * d)` with
  -- `diagGL d ∈ proIwahori`. The entries `ρ d i` of `ν d` are told apart by their valuations, so
  -- `P` determines them, and `z` interpolates from the entries of `ν d₀` to those of `t * d₀`.
  let ν (d : Fin N → Fˣ) : GL (Fin N) F := twistedNorm (.map σ) p (diagGL (t * d))
  let ρ (d : Fin N → Fˣ) (i : Fin N) : F := ∏ l ∈ range p, (σ ^ l) ((t * d) i)
  have hν (d : Fin N → Fˣ) : ν d = diagonal (ρ d) := twistedNorm_diagGL (t * d) p
  -- A norm `γ` of `δ ∈ K t K` is conjugated to `ν d` by the `k` that twists `δ` to `t * d`.
  have h_of_norm {γ δ : GL (Fin N) F} (hδ : δ ∈ iwahoriDoubleCoset t)
      (hδ_norm : twistedNorm (.map σ) p δ = γ) : ∃ k ∈ proIwahori, ∃ d : Fin N → Fˣ,
        diagGL d ∈ proIwahori ∧ k⁻¹ * δ * k.map σ = diagGL (t * d) ∧ k⁻¹ * γ * k = ν d := by
    subst hδ_norm
    exact exists_twisted_conj_diag_and_twistedNorm_conj hv hσ hp hσ_cont ht_mono hδ
  -- Conjugation keeps the characteristic polynomial, so `P` is that of some `ν d₀`.
  obtain ⟨γ₀, hγ₀_mem, rfl⟩ := hP
  obtain ⟨k₀, -, d₀, hd₀, h_conj₀⟩ : ∃ k ∈ proIwahori, ∃ d : Fin N → Fˣ, diagGL d ∈ proIwahori ∧
      k⁻¹ * γ₀ * k = ν d := by
    rcases hγ₀_mem with ⟨x, hx, rfl⟩ | ⟨δ, hδ, rfl⟩
    · exact exists_conj_map_eq_twistedNorm_diagGL h_val h_norms hs_mono hs_norm hx
    · obtain ⟨k, hk, d, hd, -, h_norm⟩ := h_of_norm hδ rfl
      exact ⟨k, hk, d, hd, h_norm⟩
  have hP : γ₀.val.charpoly = (diagonal (ρ d₀)).charpoly := by
    simp only [← hν, ← h_conj₀, Units.val_mul, coe_units_inv, charpoly_units_conj']
  have h_inj {d : Fin N → Fˣ} (hd : diagGL d ∈ proIwahori) :
      ∀ i l : Fin N, ρ d i = ρ d₀ l → i = l :=
    eq_of_prod_ringHom_pow_apply_eq hv hp ht_mono hd hd₀
  obtain ⟨z, hz⟩ : ∃ z : F[X], ∀ i : Fin N, z.eval (ρ d₀ i) = (t * d₀) i :=
    (exists_eval_eq_iff (ρ d₀) _).mpr fun i j h_eq ↦ by rw [h_inj hd₀ i j h_eq]
  -- If `k` conjugates `γ` to `ν d`, then `k` conjugates `a = z γ` to
  -- `z (ν d₀) = diagGL (t * d₀)`.
  have h_root {γ a : GL (Fin N) F} (hγ : γ.val.charpoly = (diagonal (ρ d₀)).charpoly)
      (ha : a.val = aeval γ.val z) {d : Fin N → Fˣ} (k : GL (Fin N) F)
      (hd : diagGL d ∈ proIwahori) (h_conj : k⁻¹ * γ * k = ν d) :
      k * diagGL (t * d₀) * k⁻¹ = a := by
    have h_diag : (k⁻¹ * γ * k).val = diagonal (ρ d) := by rw [h_conj, hν]
    rw [Units.ext_iff, ha, aeval_eq_conj_diagonal_eval hγ h_diag (h_inj hd) z, funext hz,
      Units.val_mul, Units.val_mul, coe_diagGL]
  simp only [hP]
  refine ⟨z, charpoly_diagonal_dvd_twistedNorm_sub_X hσ (h_inj hd₀) (fun i ↦ rfl) hz,
    ?_, fun γ a hγ ha δ hδ hδ_norm ↦ ?_⟩
  · rintro _ a hγ ha x rfl ha_norm
    refine ⟨fun hx_mem ↦ ?_, fun ha_mem ↦ ?_⟩
    · -- (a), left to right: `a = k * diagGL t * (diagGL d₀ * k⁻¹)`.
      obtain ⟨k, hk, d, hd, h_conj⟩ :=
        exists_conj_map_eq_twistedNorm_diagGL h_val h_norms hs_mono hs_norm hx_mem
      refine mem_doubleCoset.mpr ⟨k, hk, diagGL d₀ * k⁻¹, mul_mem hd₀ (inv_mem hk), ?_⟩
      simp only [← h_root hγ ha k hd h_conj, map_mul, mul_assoc]
    · -- (a), right to left.
      obtain ⟨k, hk, d, hd, h_twist, h_norm⟩ := h_of_norm ha_mem ha_norm
      exact mem_iwahoriDoubleCoset_of_conj_map_eq_twistedNorm hv h_range h_val hs_norm hk hd
        h_twist (h_root hγ ha k hd h_norm) h_norm
  · -- (b): `δ` lies in the coset `a K`.
    obtain ⟨k, hk, d, hd, h_twist, h_norm⟩ := h_of_norm hδ hδ_norm
    exact inv_mul_mem_proIwahori_of_twisted_conj hv hk hd₀ hd h_twist (h_root hγ ha k hd h_norm)

end IwahoriMatching

/-!
## Base change of Iwahori eigenforms at a place with one place above

Base change of Iwahori eigenforms along a step `E'/E` (`New.IsStep E' μ`), at a split place `w` of
`E` where `μ` is trivial and that has exactly one place `u` of `E'` above it, also split. `N` is the
local norm from `(LocField u)ˣ` to `(LocField w)ˣ`.

`New.proIwahori` is the pro-`p` Iwahori subgroup; `New.dominantTorus` the diagonal `t` with
non-decreasing absolute values; `New.IsIwahoriEigen ρ ξ f` says that `f ≠ 0` is fixed by
`New.proIwahori` and that the average of `ρ t f` over it is `ξ t • f` for dominant `t`. For a family
`θ` of `r` characters, `New.torusChar θ` is the character `t ↦ ∏ i, θ i (t i) * |t i| ^ (r - 1 - i)`
of the diagonal torus.
-/

section BaseChangeEigenchar

open Matrix Polynomial Valued Finset Patching

variable {E E' : Type} [Field E] [CMType E] [Field E'] [Algebra E E'] [CMTypeOver E E'] {m : Type _}
  {μ : (𝔸f E)ˣ →* ℂˣ} [Fintype m] [DecidableEq m] {u : FinPlace E'} [hμ : IsStep E' μ]
  {hw : (u.below E).IsSplit} (hu : u.IsSplit)

/-- At a place `u` of `E'` fixed by `τ`, the component at `u` of the `i`-th iterate of `τ` on
finite adeles is the `i`-th iterate of the local action `locMap τ hs` of `τ` on the completion at
`u`, applied to the component at `u`. -/
lemma iterate_adeleMap_apply {τ : Gal(E'/E)} (hs : u.comap τ = u) (i : ℕ) (x : 𝔸f E') :
    (adeleMap τ)^[i] x u = (locMap (τ : E' →+* E') hs)^[i] (x u) :=
  (Function.Semiconj.iterate_right (f := fun x : 𝔸f E' ↦ x u) (adeleMap_apply _ hs) i).eq x

/-- Local norms are onto the `1`-units at a place with one place above. Let `E'/E` be a step, `u`
the only place of `E'` above `w = u.below E` (`h_unique`), and `τ ≠ 1` fix `u`. Then every `x` at
`w` with `v (x - 1) < 1` is a norm `∏ i < [E' : E], (σ ^ i) y` of a unit `y` at `u` with
`v (y - 1) < 1`, where `σ = locMap τ hs` is the action of `τ` on the completion at `u`. -/
lemma exists_local_norm_eq
    (h_unique : ∀ u' : FinPlace E', FinPlace.below E u' = u.below E ↔ u' = u)
    {μ : (𝔸f E)ˣ →* ℂˣ} [IsStep E' μ] {τ : Gal(E'/E)} (hτ : τ ≠ 1)
    (hs : u.comap τ = u) (x : LocField (u.below E))
    (hx : v (locMap (algebraMap E E') rfl x - 1 : LocField u) < 1) :
    ∃ y : (LocField u)ˣ,
      v (y.val - 1) < 1 ∧
      ∏ i ∈ range (Module.finrank E E'), (locMap (τ : E' →+* E') hs ^ i) y =
        locMap (algebraMap E E') rfl x := by
  -- The integral adele `a` that is `x - 1` at `u` and `0` elsewhere is fixed by `τ` and reduces to
  -- `0` at every place, so `τ` is tame at level `a`; then `1 + a` is a norm of some `z ≡ 1`.
  obtain ⟨C, -, h_tame⟩ := exists_isTameAtLevel_intAdeleMap hτ
  set ι : LocField (u.below E) →+* LocField u := locMap (algebraMap E E') rfl
  let a : Ô E' :=
    ⟨singleAdele u (ι x - 1), by simpa +contextual [mem_Ô, ← and_forall_ne u] using hx.le⟩
  have ha_red : ∀ o : FinPlace E', reduceAt o a = 0 := by
    simp +contextual [hx, a, ← and_forall_ne u]
  -- `a` comes from the adele of `E` that is `x - 1` at `w`, as `u` is the only place above `w`
  have ha_range : a.val ∈ (finAdeleIncl E E').range := by
    refine ⟨singleAdele _ (x - 1), ?_⟩
    simp +contextual [DFunLike.ext_iff, ← and_forall_ne u, a, ι, h_unique, adeleMap_apply]
  have ha_fixed : intAdeleMap (τ : E' →+* E') a = a :=
    Subtype.ext (mem_range_finAdeleIncl_iff.mp ha_range τ)
  have h_unit : IsUnit (1 + a) := by
    simp [v.map_one_add_of_lt, ← reduceAt_eq_zero, ha_red]
  obtain ⟨z, hz_one, -, hz⟩ := (h_tame a ha_fixed fun o _ _ ↦
    ha_red o).exists_prod_range_pow_apply_eq
    (.inr isProfiniteRing_intAdeles) h_unit (by simp [ha_fixed]) (by simp)
  refine ⟨z.map ((evalAt u).domRestrict (Ô E')).toMonoidHom, ?_, ?_⟩
  · -- `z ≡ 1` modulo `a`, and `a` reduces to `0` at `u`
    have h_red : reduceAt u a ∣ reduceAt u ((z : Ô E') - 1) := map_dvd (reduceAt u) hz_one
    rw [ha_red u, zero_dvd_iff, reduceAt_eq_zero] at h_red
    simpa using h_red
  · -- read the norm equation `∏ (τ ^ i) z = 1 + a` at `u`
    simpa [iterate_adeleMap_apply hs, a] using congrArg (fun b : Ô E' ↦ evalAt u (b : 𝔸f E')) hz

include hμ in
/-- At a place `u` of `E'` fixed by `τ`, the local action `locMap τ hs` of `τ` on the completion
at `u` has order dividing `[E' : E]`. -/
private lemma locMap_pow_finrank_eq_one {τ : Gal(E'/E)} (hs : u.comap τ = u) :
    locMap (τ : E' →+* E') hs ^ Module.finrank E E' = 1 := by
  -- Read `adeleMap τ ^ [E' : E] = 1` at `u` on the adele that is `x` at `u` and `0` elsewhere.
  refine RingHom.ext fun x ↦ ?_
  simpa [iterate_adeleMap_apply hs] using congrArg
    (fun φ : 𝔸f E' →+* 𝔸f E' ↦ φ (singleAdele u x) u) (adeleMap_pow_finrank_eq_one (σ := τ))

include hμ in
/-- Fixed points of the local action come from below. Let `E'/E` be a step (so Galois of prime
degree), `u` the only place of `E'` above `w = u.below E` (`h_unique`), and `τ ≠ 1` fix `u`. Then
every `x` in the completion at `u` fixed by the local action `locMap τ hs` of `τ` is the image of an
element of the completion at `w`. -/
private lemma mem_range_locMap_of_locMap_eq_self
    (h_unique : ∀ u' : FinPlace E', FinPlace.below E u' = u.below E ↔ u' = u) {τ : Gal(E'/E)}
    (hτ : τ ≠ 1) (hs : u.comap τ = u) {x : LocField u} (hx : locMap (τ : E' →+* E') hs x = x) :
    x ∈ (locMap (algebraMap E E') rfl : LocField (u.below E) →+* LocField u).range := by
  -- The adele that is `x` at `u` and `0` elsewhere is fixed by `τ`, as `τ` fixes `u` and moves
  -- no other place onto `u`. So it comes from a finite adele `y` of `E`, and `x` is the image of
  -- the component of `y` at `w`.
  have h_single : adeleMap (τ : E' →+* E') (singleAdele u x) = singleAdele u x := by
    ext1 o
    obtain rfl | ho := eq_or_ne o u
    · simp [hx, hs, adeleMap_apply]
    · have h_comap_ne : FinPlace.comap (τ : E' →+* E') o ≠ u := by
        rwa [Ne, ← h_unique, below_comap, h_unique]
      simp [h_comap_ne, ho, adeleMap_apply]
  obtain ⟨y, hy⟩ : singleAdele u x ∈ (finAdeleIncl E E').range :=
    mem_range_finAdeleIncl_of_adeleMap_eq hτ h_single
  exact ⟨y (u.below E), by simp_all [← adeleMap_apply]⟩

include hμ in
/-- The local norm as a product of conjugates. At a place `u` of `E'` fixed by `τ ≠ 1`, along a step
`E'/E`, the local norm of `y`, mapped into the completion at `u`, is the product of the conjugates
`(σ ^ i) y`, `i < [E' : E]`, where `σ = locMap τ hs`. -/
private lemma locMap_localNorm_eq_prod {τ : Gal(E'/E)} (hτ : τ ≠ 1) (hs : u.comap τ = u)
    (y : (LocField u)ˣ) :
    locMap (algebraMap E E') rfl (localNorm E u y : LocField (u.below E)) =
      ∏ i ∈ range (Module.finrank E E'), (locMap (τ : E' →+* E') hs ^ i) (y : LocField u) := by
  -- The local norm is the component at `w` of the adelic norm of the idele `y` at `u`, and the
  -- adelic norm is the product of the Galois conjugates, which are the powers of `τ`.
  have h_unfold : (localNorm E u y : LocField (u.below E)) =
      adeleNorm E E' (locIdele u y : 𝔸f E') (u.below E) := rfl
  rw [h_unfold, ← adeleMap_apply, finAdeleIncl_adeleNorm, ← evalAt_apply, map_prod (evalAt u),
    prod_range, ← (bijective_pow_of_ne_one_of_prime_finrank hτ).prod_comp]
  simp [← adeleMap_gal_pow, iterate_adeleMap_apply hs]

include hμ in
/-- Cocycles split at pro-`p` Iwahori level at a place `u` fixed by `τ ≠ 1`, along a step `E'/E`.
Let `ρ` be a retraction of `embedAtSplit hu` at the places above `u.below E` and its conjugate
(`New.IsLocalRetraction`) that carries `galoisGf τ` to the entrywise action of `σ = locMap τ hs`.
Then at the level of the `δ` with `ρ δ ∈ proIwahori`, every `galoisGf τ`-cocycle is a coboundary on
those places (`New.CocyclesSplit`). -/
private lemma cocyclesSplit_comap_proIwahori {τ : Gal(E'/E)} (hτ : τ ≠ 1) (hs : u.comap τ = u)
    {ρ : Gf E' m →* GL (Fin (Fintype.card m)) (LocField u)}
    (hρ_retr : IsLocalRetraction (embedAtSplit hu) ρ (placesAbove E' {u.below E}))
    (hρ_gal : ∀ δ : Gf E' m, ρ (galoisGf τ δ) = (ρ δ).map (locMap (τ : E' →+* E') hs)) :
    CocyclesSplit (Module.finrank E E') (idem (placesAbove E' {u.below E})) (proIwahori.comap ρ)
      (galoisGf τ) := by
  -- Tameness at level `0` gives an integral adele `c` of trace `1`, so the component of `c` at `u`
  -- has `σ`-trace `1`, and a cocycle at `u` is a coboundary `t` there
  -- (`exists_coboundary_proIwahori`). Then `embedAtSplit hu t` splits the cocycle.
  intro δ hδ h_cocycle
  set σ : LocField u →+* LocField u := locMap (τ : E' →+* E') hs
  obtain ⟨C, -, h_tame⟩ := exists_isTameAtLevel_intAdeleMap hτ
  obtain ⟨-, ⟨c, hc_dvd⟩, -⟩ := h_tame 0 (by simp) (by simp)
  have hc_sum : ∑ i ∈ range (Module.finrank E E'), (intAdeleMap (τ : E' →+* E') ^ i) c = 1 := by
    rwa [zero_dvd_iff, sub_eq_zero] at hc_dvd
  have h_trace : ∑ i ∈ range (Module.finrank E E'), (σ ^ i) (c.val u) = 1 := by
    simpa [iterate_adeleMap_apply hs] using congrArg (fun b : Ô E' ↦ evalAt u (b : 𝔸f E')) hc_sum
  have hδ_norm : twistedNorm (.map σ) (Module.finrank E E') (ρ δ) = 1 := by
    rw [← map_twistedNorm ρ hρ_gal, h_cocycle, map_one]
  obtain ⟨t, ht, ht_eq⟩ : ∃ t ∈ proIwahori, ρ δ * t.map σ = t :=
    exists_coboundary_proIwahori (v_locMap_eq_of_surjective _ hs τ.surjective)
      (locMap_pow_finrank_eq_one hs) (mem_Ô.mp c.prop u) h_trace hδ hδ_norm
  obtain ⟨h_supp, h_retract, h_ker⟩ := hρ_retr
  refine ⟨embedAtSplit hu t, ?_, ?_, ?_⟩
  · -- `ρ` retracts `embedAtSplit hu`, so the component at `u` is `t ∈ proIwahori`
    rwa [Subgroup.mem_comap, h_retract]
  · -- `embedAtSplit hu t` is `1` off the places above `w`
    rw [← idem_compl, idem_smul_eq_iff_mem_trivialOn]
    simpa [Gf.trivialOn, Gf.supportedOn, Subgroup.mem_iInf] using h_supp t
  · -- above `w`, being trivial means lying in the kernel of `ρ`, and `t⁻¹ * ρ δ * σ t = 1`
    rw [idem_smul_eq_iff_mem_trivialOn, ← h_ker, MonoidHom.mem_ker, map_mul, map_mul, map_inv,
      hρ_gal, h_retract, mul_assoc, ht_eq, inv_mul_cancel]

/-- At a place `u` of `E'` fixed by `τ`, the twisted norm under `τ` of the adelic polynomial
`1 + idem {u} • (y - 1)`, which is `y` at `u` and `1` elsewhere, read at `u`, is the twisted norm
under the local action `locMap τ hs` of `y` read at `u`. -/
private lemma map_evalAt_twistedNorm_one_add_idem_smul {τ : Gal(E'/E)} (hs : u.comap τ = u)
    (p : ℕ) (y : (𝔸f E')[X]) :
    (twistedNorm (.map (adeleMap (τ : E' →+* E'))) p (1 + idem {u} • (y - 1))).map (evalAt u) =
      twistedNorm (.map (locMap (τ : E' →+* E') hs)) p (y.map (evalAt u)) := by
  -- Both sides are products of conjugates; compare them factor by factor and coefficient by
  -- coefficient.
  simp only [twistedNorm_map_eq_prod, Polynomial.map_prod]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  ext k
  simp [iterate_adeleMap_apply hs]

/-- The indicators of `K N(t) K` (through `r`) and of `K t K` (through `ρ`) are a matching pair
above `w = u.below E` (`New.IsMatchingPairAbove`), for `t` with strictly increasing `v (t i)`. Here
`K = proIwahori`, `N(t) = localNorm E u ∘ t`, and `ρ`, `r` are the components at `u` and `w` of the
adelic groups `Gf E' m` and `Gf E m` (`baseChangeGf` maps `Gf E m` into `Gf E' m`), renumbered: `ρ`
carries `galoisGf τ` to `locMap τ hs`, keeps characteristic polynomials, and sends a base change to
`r` followed by the inclusion of the completion at `w`. -/
private lemma isMatchingPairAbove_proIwahori
    (h_unique : ∀ u' : FinPlace E', FinPlace.below E u' = u.below E ↔ u' = u)
    (hμ_loc : ∀ x : (LocField (FinPlace.below E u))ˣ, μ (locIdele (u.below E) x) = 1)
    (hw : (u.below E).IsSplit) {τ : Gal(E'/E)} (hτ : τ ≠ 1) (hs : u.comap τ = u)
    {ρ : Gf E' m →* GL (Fin (Fintype.card m)) (LocField u)}
    {r : Gf E m →* GL (Fin (Fintype.card m)) (LocField (u.below E))}
    (hρ_gal : ∀ δ : Gf E' m, ρ (galoisGf τ δ) = (ρ δ).map (locMap (τ : E' →+* E') hs))
    (hρ_val : ∀ g : Gf E' m, (ρ g).val =
      reindexAlgEquiv (LocField u) (LocField u) (Fintype.equivFin m) (g.atPlace u).val)
    (hρ_charpoly :
      ∀ g : Gf E' m, (ρ g).val.charpoly = (↑↑g : Matrix m m (𝔸f E')).charpoly.map (evalAt u))
    (hρ_baseChange : ∀ x : Gf E m, ρ (baseChangeGf x) = (r x).map (locMap (algebraMap E E') rfl))
    {t : Fin (Fintype.card m) → (LocField u)ˣ}
    (ht : StrictMono fun i : Fin (Fintype.card m) ↦ v (t i : LocField u)) :
    IsMatchingPairAbove (n := m) τ μ {u.below E} (proIwahori.comap ρ)
      ((iwahoriDoubleCoset (localNorm E u ∘ t)).indicator 1 ∘ r)
      ((iwahoriDoubleCoset t).indicator 1 ∘ ρ) := by
  -- At `u`, `τ` acts by an isometry `σ` of order dividing `[E' : E]` whose fixed points come from
  -- the completion at `w`, and the norm of `t` is `N(t)`. So `proIwahori_doubleCoset_match` gives a
  -- local polynomial `z`; its lift `1 + idem {u} • (y - 1)` is a root (`isNormRoot_of_one_side`).
  classical
  set σ : LocField u →+* LocField u := locMap (τ : E' →+* E') hs
  set ι : LocField (u.below E) →+* LocField u := locMap (algebraMap E E') rfl
  have hσ_v (x : LocField u) : v (σ x) = v x := v_locMap_eq_of_surjective _ hs τ.surjective x
  refine ⟨?_, ?_⟩
  · -- The indicator of `iwahoriDoubleCoset t` is invariant under twisted conjugation by
    -- `proIwahori`.
    simp +contextual [hρ_gal, hσ_v, map_mem_proIwahori_iff_of_isometry,
      (isHeckeFunction_doubleCoset isOpen_proIwahori _).2]
  · rintro _ ⟨g, hg, rfl⟩ -
    have hNt_mono : StrictMono fun i ↦ v ((localNorm E u ∘ t) i : LocField (u.below E)) := by
      simpa [StrictMono, ← toNormedField.norm_lt_iff] using ht
    have h_Nm : (diagGL (localNorm E u ∘ t)).map ι =
        twistedNorm (.map σ) (Module.finrank E E') (diagGL t) :=
      Units.ext (by simp [ι, σ, locMap_localNorm_eq_prod hτ hs])
    -- At `u`, the element `g` comes from the double coset of `N(t)` or is a norm from that of `t`.
    have hg_mem : ρ g ∈ .map ι '' iwahoriDoubleCoset (localNorm E u ∘ t) ∪
        twistedNorm (.map σ) (Module.finrank E E') '' iwahoriDoubleCoset t := by
      rcases hg with ⟨x, hx, rfl⟩ | ⟨δ, hδ, rfl⟩
      · exact Or.inl ⟨r x, Set.mem_of_indicator_ne_zero hx, (hρ_baseChange x).symm⟩
      · exact Or.inr ⟨ρ δ, Set.mem_of_indicator_ne_zero hδ, (map_twistedNorm ρ hρ_gal _ δ).symm⟩
    -- So there is a polynomial `z` over `LocField u` of norm `X` modulo the characteristic
    -- polynomial of `ρ g`, such that `γ ↦ z(γ)` matches the two double cosets.
    obtain ⟨z, hz_dvd, hz_iff, hz_coset⟩ :=
      proIwahori_doubleCoset_match hσ_v (locMap_pow_finrank_eq_one hs) hμ.out.pos (by fun_prop)
        (fun x hx ↦ mem_range_locMap_of_locMap_eq_self h_unique hτ hs hx)
        (isEquiv_comap_locMap (algebraMap E E') rfl) (exists_local_norm_eq h_unique hτ hs) ht
        hNt_mono h_Nm _ ⟨ρ g, hg_mem, hρ_charpoly g⟩
    -- Lift `z` to an adelic `y`; `1 + idem {u} • (y - 1)` is `y` at `u` and `1` elsewhere.
    obtain ⟨y, rfl⟩ := map_surjective (evalAt u) (fun x ↦ ⟨singleAdele u x, by simp⟩) z
    have h_dvd : (↑↑g : Matrix m m (𝔸f E')).charpoly.map (evalAt u) ∣
        (twistedNorm (.map (adeleMap τ)) (Module.finrank E E') (1 + idem {u} • (y - 1))).map
          (evalAt u) - X := by
      rwa [map_evalAt_twistedNorm_one_add_idem_smul hs]
    have hz_off : ∀ u' : FinPlace E', u'.below E ∉ ({u.below E} : Set (FinPlace E)) →
        (1 + idem {u} • (y - 1)).map (evalAt u') = 1 := by simp_all
    -- A root at `u` alone is a root above `w` and its conjugate (`h_root`), and the unitary `a`
    -- that it attaches to `γ` has component `y(γ)` at `u` (`h_comp`).
    obtain ⟨h_root, h_comp⟩ :=
      hμ.isNormRoot_of_one_side (n := m) (T := {u.below E}) rfl (by simpa using hμ_loc)
        (by simpa using hw) hz_off (by simpa [h_unique] using h_dvd)
    refine ⟨1 + idem {u} • (y - 1), h_root, fun γ a hγ ha ↦ ?_⟩
    have ha_u : (ρ a).val = aeval (ρ γ).val (y.map (evalAt u)) := by
      rw [hρ_val a, hρ_val γ, aeval_algHom_apply, h_comp γ a ha u rfl]
      simp
    have hγ_u : (ρ γ).val.charpoly = (↑↑g : Matrix m m (𝔸f E')).charpoly.map (evalAt u) := by
      rw [hρ_charpoly, hγ]
    have h_norm_u (b : Gf E' m) (hb : twistedNorm (galoisGf τ) (Module.finrank E E') b = γ) :
        twistedNorm (.map σ) (Module.finrank E E') (ρ b) = ρ γ := by
      rw [← map_twistedNorm ρ hρ_gal, hb]
    refine ⟨fun x hx hNm ↦ ?_, fun δ hδ_norm hδ_ne ↦ ?_⟩
    · -- (a): `x` is in the double coset of `N(t)` at `w` iff `a` is in that of `t` at `u`
      exact if_congr
        (hz_iff _ _ hγ_u ha_u _ (by rw [← hx, hρ_baseChange]) (h_norm_u a hNm)) rfl rfl
    · -- (b): a point `δ` of the double coset of `t` of norm `γ` lies in `a * proIwahori`
      simpa using hz_coset _ _ hγ_u ha_u _ (Set.mem_of_indicator_ne_zero hδ_ne)
        (h_norm_u δ hδ_norm)

/-- Matching local data at a place with one place above. Let `E'/E` be a step, `w = u.below E` split
(`hw`) with `μ` trivial at `w` (`hμ_loc`), and `u` the only place above `w` (`h_unique`), split
(`hu`). Then the indicators of `K N(t) K` at `w` and `K' t K'` at `u`, with `K`, `K'` the pro-`p`
Iwahori subgroups and `N(t) = localNorm E u ∘ t`, are matching local data (`New.IsLocalMatching`)
for the dominant `t` whose valuations `v (t i)` increase strictly. -/
lemma isLocalMatching_proIwahori
    (h_unique : ∀ u' : FinPlace E', FinPlace.below E u' = u.below E ↔ u' = u)
    (hμ_loc : ∀ x : (LocField (FinPlace.below E u))ˣ, μ (locIdele (u.below E) x) = 1) :
    IsLocalMatching (n := m) μ {u.below E} (embedAtSplit hw) (embedAtSplit hu) proIwahori proIwahori
      {t : dominantTorus | StrictMono fun i : Fin (Fintype.card m) ↦ v (t.val i).val}
      (fun t : dominantTorus ↦ (iwahoriDoubleCoset (localNorm E u ∘ t)).indicator 1)
      fun t : dominantTorus ↦ (iwahoriDoubleCoset t.val).indicator 1 := by
  classical
  -- Everything is read at `u`, where some `τ ≠ 1` acts by an isometry of order dividing `[E' : E]`
  -- whose fixed points come from the completion at `w`. The local results
  -- `cocyclesSplit_comap_proIwahori` and `isMatchingPairAbove_proIwahori` then give the splitting
  -- of cocycles and the matching of the two double cosets.
  let ε : m ≃ Fin (Fintype.card m) := Fintype.equivFin m
  -- `ρ` and `r` are the components at `u` and at `w`, renumbered; they retract the embeddings.
  set ρ : Gf E' m →* GL (Fin (Fintype.card m)) (LocField u) :=
    (reindexGL ε).toMonoidHom.comp (Gf.atPlace u)
  set r : Gf E m →* GL (Fin (Fintype.card m)) (LocField (u.below E)) :=
    (reindexGL ε).toMonoidHom.comp (Gf.atPlace (u.below E))
  obtain ⟨h_retr_w, h_retr_u, h_level⟩ := isLocalRetraction_ofSplitPlace m h_unique hu hw
  have hρ_retr : IsLocalRetraction (embedAtSplit hu) ρ (placesAbove E' {u.below E}) := by
    simp_all [IsLocalRetraction, ρ, ε]
  have hr_retr : IsLocalRetraction (embedAtSplit hw) r {u.below E} := by
    simp_all [IsLocalRetraction, r, ε]
  obtain ⟨τ, hτ⟩ := hμ.exists_gal_ne_one (E := E) (E' := E')
  have hs : u.comap τ = u := (h_unique _).mp (below_comap τ u)
  -- `ρ` carries `galoisGf τ` to the entrywise action of `τ` at `u`, and a base change to `r`
  -- followed by the inclusion of the completion at `w`.
  have hρ_gal (δ : Gf E' m) : ρ (galoisGf τ δ) = (ρ δ).map (locMap (τ : E' →+* E') hs) :=
    congrArg (reindexGL ε) (atPlace_galoisGf τ δ hs)
  have hρ_charpoly (g : Gf E' m) :
      (ρ g).val.charpoly = (↑↑g : Matrix m m (𝔸f E')).charpoly.map (evalAt u) :=
    (charpoly_reindex ε (g.atPlace u).val).trans (charpoly_map _ (evalAt u))
  have hρ_baseChange (x : Gf E m) :
      ρ (baseChangeGf x) = (r x).map (locMap (algebraMap E E') rfl) := rfl
  have h_stable (k : Gf E' m) : ρ (galoisGf τ k) ∈ proIwahori ↔ ρ k ∈ proIwahori := by
    rw [hρ_gal]
    exact map_mem_proIwahori_iff_of_isometry (v_locMap_eq_of_surjective _ hs τ.surjective)
  -- The component at `u` of the base change of `g` is the component at `w`, mapped into the
  -- completion at `u`.
  have h_baseChange :
      (Subgroup.comap ρ proIwahori).comap baseChangeGf = Subgroup.comap r proIwahori := by
    ext g
    simp only [Subgroup.mem_comap, hρ_baseChange]
    exact map_mem_proIwahori_iff_of_isEquiv (isEquiv_comap_locMap (algebraMap E E') rfl)
  -- `ρ` is continuous, as renumbering the entries of a matrix is, and `proIwahori` is open
  have h_open : (Subgroup.comap ρ proIwahori).IsOpen := by
    have h_reindex : Continuous fun M : Matrix m m (LocField u) ↦ M.submatrix ε.symm ε.symm := by
      fun_prop
    exact isOpen_proIwahori.preimage (.comp (.units_map _ h_reindex) (by fun_prop))
  have h_le_level : Subgroup.comap ρ proIwahori ≤ localLevel m (placesAbove E' {u.below E}) := by
    rintro g ⟨hg_int, -⟩
    simpa [h_level, mem_intGL, reindex_equiv ε.symm, ρ] using hg_int
  -- Both indicators are bi-invariant, as double cosets of the open group `proIwahori`.
  exact ⟨τ, hτ, r, ρ, ⟨fun t ↦ ⟨isHeckeFunction_doubleCoset isOpen_proIwahori _,
      isHeckeFunction_doubleCoset isOpen_proIwahori _⟩, hr_retr, hρ_retr, Set.finite_singleton _,
      h_stable⟩,
    h_baseChange, h_open, Subgroup.comap ρ proIwahori, ⟨le_rfl, h_le_level⟩,
    cocyclesSplit_comap_proIwahori hu hτ hs hρ_retr hρ_gal, fun t ht ↦
      isMatchingPairAbove_proIwahori h_unique hμ_loc hw hτ hs hρ_gal (fun _ ↦ rfl) hρ_charpoly
        hρ_baseChange ht⟩

/-- The operators of dominant double cosets multiply like the torus. Let `ρ` be a smooth
representation of `GL_N` over the completion of a number field at `o`, and `s`, `t` elements of
`New.dominantTorus`. On vectors `x` fixed by `New.proIwahori`, applying the operator of the double
coset of `t` and then that of `s` is applying that of `s * t`. -/
private lemma heckeFun_iwahoriDoubleCoset_mul {F : Type} [Field F] [NumberField F] {o : FinPlace F}
    {N : ℕ} (ρ : Rep ℂ (GL (Fin N) (LocField o))) [IsSmoothRep ρ.ρ] {s t : Fin N → (LocField o)ˣ}
    (hs : s ∈ dominantTorus) (ht : t ∈ dominantTorus) (x : ρ)
    (hx : x ∈ levelSpace ρ.ρ proIwahori) :
    heckeFun ρ.ρ proIwahori ((iwahoriDoubleCoset s).indicator 1)
        (heckeFun ρ.ρ proIwahori ((iwahoriDoubleCoset t).indicator 1) x) =
      heckeFun ρ.ρ proIwahori ((iwahoriDoubleCoset (s * t)).indicator 1) x := by
  -- Each operator is `iwahoriDegree` times the mean of a translate; the means multiply by
  -- `compactMean_diagGL_compactMean_diagGL`, and the degrees multiply.
  have h_deg : iwahoriDegree t * iwahoriDegree s = iwahoriDegree (s * t) := by
    simp [prod_mul_distrib, div_mul_div_comm, mul_comm]
  simp only [hs, ht, hx, mul_mem, heckeFun_iwahoriDoubleCoset_eq_iwahoriDegree_smul, map_smul,
    compactMean_mem_levelSpace, compactMean_diagGL_compactMean_diagGL, smul_smul, h_deg]

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.univ in
attribute [-simp] mem_levelSpace exists_const MonoidHom.coe_comp in
/-- Base change keeps an Iwahori eigencharacter. Let `E'/E` be a step with `E'` containing a
primitive `5040`-th root of unity (`HasPrimitiveRoot5040`). Let `w = u.below E` be split (`hw`) with
`μ` trivial at `w` (`hμ_loc`), and let `u` be the only place above `w` (`h_unique`), split (`hu`).
If `f`, an element of `localFormRep (stdSpace E m) κ hw` (the forms of weight `κ`, as a
representation of `GL` at `w`), is an Iwahori eigenvector at `w` (`New.IsIwahoriEigen`) with
character `torusChar θ`, some form `f'` over `E'` is (a) an eigenform, (b) a weak base change of `f`
off `w` and its conjugate, and (c) an Iwahori eigenvector at `u` with character
`torusChar (θ i ∘ N)`, `N = localNorm E u`. -/
lemma exists_baseChange_isIwahoriEigen
    (h_unique : ∀ u' : FinPlace E', FinPlace.below E u' = u.below E ↔ u' = u)
    (hμ_loc : ∀ x : (LocField (FinPlace.below E u))ˣ, μ (locIdele (u.below E) x) = 1)
    [HasPrimitiveRoot5040 E'] {κ : Weight E} {f : localFormRep (stdSpace E m) κ hw}
    {θ : Fin (Fintype.card m) → (LocField (u.below E))ˣ →* ℂˣ}
    (hf : IsIwahoriEigen (localFormRep (stdSpace E m) κ hw) (torusChar θ) f) :
    ∃ f' : (stdSpace E' m).forms κ.baseChange, ∃ P : FinPlace E' → ℂ[X],
      -- (a) `f'` is an eigenform
      IsEigenform f'.val P ∧
      -- (b) it is a weak base change of `f` away from the place below `u`
      IsWeakBaseChange μ {u.below E} f.val f'.val ∧
      -- (c) at `u` its characters are those of `f` composed with the local norm
      IsIwahoriEigen (localFormRep (stdSpace E' m) κ.baseChange hu)
        (torusChar fun i : Fin (Fintype.card m) ↦ (θ i).comp (localNorm E u)) f' := by
  -- Apply `exists_isWeakBaseChange_of_matching` to the double cosets of
  -- `isLocalMatching_proIwahori`. For dominant `t`, the operator of the double coset of `t` is
  -- `iwahoriDegree t` times the operator of `IsIwahoriEigen`
  -- (`heckeFun_iwahoriDoubleCoset_eq_iwahoriDegree_smul`), and the local norm keeps absolute
  -- values. Any strictly dominant `t₀` serves as the distinguished index.
  obtain ⟨hf_ne, hf_level, hf_eigen⟩ := hf
  obtain ⟨t₀, ht₀, -⟩ :=
    exists_iwahoriHeckeHom_injective (localFormRep (stdSpace E' m) κ.baseChange hu)
      (v_uniformizer u)
  have h_dom (n : ℕ) (t : Fin n → (LocField u)ˣ) :
      localNorm E u ∘ t ∈ dominantTorus ↔ t ∈ dominantTorus := by
    simp [dominantTorus, Monotone, ← toNormedField.norm_le_iff]
  refine (exists_isWeakBaseChange_of_matching f
    (isLocalMatching_proIwahori (hw := hw) hu h_unique hμ_loc) id
    (fun a ↦ iwahoriDegree a.val * torusChar θ (localNorm E u ∘ a)) ⟨t₀, ht₀.monotone⟩ ht₀
    ?comm ?stable ?trace).imp ?eigen
  case comm =>
    -- the operators of dominant elements multiply like the torus, which is commutative
    intro s t
    have hNs : localNorm E u ∘ s.val ∈ dominantTorus := (h_dom _ s.val).mpr s.prop
    have hNt : localNorm E u ∘ t.val ∈ dominantTorus := (h_dom _ t.val).mpr t.prop
    refine ⟨fun x hx ↦ ?_, fun x hx ↦ ?_⟩
    · rw [heckeFun_iwahoriDoubleCoset_mul (localFormRep (stdSpace E m) κ hw) hNs hNt x hx,
        heckeFun_iwahoriDoubleCoset_mul (localFormRep (stdSpace E m) κ hw) hNt hNs x hx, mul_comm]
    · rw [heckeFun_iwahoriDoubleCoset_mul (localFormRep (stdSpace E' m) κ.baseChange hu) s.prop
          t.prop x hx,
        heckeFun_iwahoriDoubleCoset_mul (localFormRep (stdSpace E' m) κ.baseChange hu) t.prop
          s.prop x hx, mul_comm]
  case stable =>
    -- dominant times strictly dominant is strictly dominant
    intro s t ht
    refine ⟨s * t, ?_, fun x hx ↦ ?_,
      heckeFun_iwahoriDoubleCoset_mul (localFormRep (stdSpace E' m) κ.baseChange hu) s.prop t.prop⟩
    · simpa [Pi.mul_def] using s.prop.mul_strictMono ht (by simp [zero_lt_iff]) (by simp)
    · rw [id_eq, heckeFun_iwahoriDoubleCoset_mul (localFormRep (stdSpace E m) κ hw)
        ((h_dom _ s.val).mpr s.prop) ((h_dom _ t.val).mpr t.prop) x hx]
      simp [Function.comp_def, Pi.mul_def]
  case trace =>
    -- The space contains `f ≠ 0`, and the operator has one non-zero generalised eigenvalue on it.
    intro W hfW _ h_maps
    refine trace_restrict_ne_zero (c := iwahoriDegree t₀ * (torusChar θ (localNorm E u ∘ t₀) : ℂ))
      (by simp [prod_ne_zero_iff]) (fun h0 ↦ ?_) (fun x hx ↦ ?_) h_maps
    · -- `f` lies in the space, being fixed by `proIwahori` and an eigenvector of each operator;
      -- so the space is not `⊥`, as `f ≠ 0`
      apply hf_ne
      rw [← Submodule.mem_bot ℂ, ← h0, Submodule.mem_inf, mem_heckeGenEigenspace]
      refine ⟨⟨hf_level, fun a ↦ ?_⟩, hfW⟩
      rw [Module.End.mem_maxGenEigenspace]
      exact ⟨1, by simp [a.prop, h_dom, hf_level, hf_eigen, mul_smul]⟩
    · exact (mem_heckeGenEigenspace.mp (Submodule.mem_inf.mp hx).1).2 _
  case eigen =>
    -- Cancel `iwahoriDegree t ≠ 0`; the character `torusChar θ (localNorm E u ∘ ·)` is that of the
    -- characters `(θ i).comp (localNorm E u)`.
    rintro f' ⟨P, ⟨hf'_ne, hf'_poly⟩, h_same, ⟨h_fixed, h_val⟩, -⟩
    refine ⟨P, ⟨hf'_ne, hf'_poly⟩, h_same, ne_of_apply_ne Subtype.val hf'_ne, h_fixed, ?_⟩
    simpa [h_fixed, mul_smul, prod_eq_zero_iff, torusChar, Pi.monoidHomMulEquiv,
      MonoidHom.comp_apply, coe_normAbsChar_locField] using h_val

end BaseChangeEigenchar

end New
