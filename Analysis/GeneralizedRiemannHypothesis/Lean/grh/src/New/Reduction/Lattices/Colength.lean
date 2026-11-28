import Lib.General.Algebra.FittingIdealsAndLengths

/-!
# Colength of modules, and endomorphisms surjective up to a bounded colength

A substitute for the colength of one module in another, and the bookkeeping of such colengths under
images, preimages, sums of submodules and products of endomorphisms.

* `New.ColengthDvd`: every finite family in `M` is carried into `N` by a square matrix whose
  determinant divides `z`; read it as "the colength of `N` in `M` divides `z`" or, over a valuation
  ring, "`N` has colength at most `v(z)` in `M`". `N ≤ M` is not required.
* `New.ColengthDvd.comap`, `New.ColengthDvd.map`, `New.ColengthDvd.trans`, `New.ColengthDvd.comp`:
  it passes along linear maps, and the bounds multiply along chains and compositions.
* `New.IsOntoUpToColength`, `New.IsOntoUpToColength.prod`: endomorphisms that keep `M` and are onto
  modulo `p ^ n` up to a colength dividing `p ^ l` with `l ≤ c`; the bounds `c` add under products.
* `New.ColengthDvd.of_det_dvd`: over a valuation domain the image of a square matrix `A` has
  colength dividing every multiple of `det A`, by the Smith normal form.
* `New.ColengthDvd.relLength_le`, `New.IsOntoUpToColength.exists_relLength_le`: over a discrete
  valuation ring `New.ColengthDvd` bounds a length.
-/

namespace New

open Matrix Submodule Finset Pointwise Module

variable {O U V ι : Type*} [CommRing O] [AddCommGroup U] [Module O U] [AddCommGroup V] [Module O V]
  {M N P : Submodule O V} {M' N' : Submodule O U} {z z' a : O}

variable (M N z) in
/-- `New.ColengthDvd M N z`, for submodules `M`, `N` of `V` and `z : O`, is read as "the colength of
`N` in `M` divides `z`" (over a valuation ring: it is at most `v(z)`). It needs no bases and no
inclusion `N ≤ M`: for every finite family `Φ k` (`k : Fin n`) of vectors of `M` there is a square
matrix `m` indexed by `Fin n` with `det m ∣ z` such that all `∑ k, m i k • Φ k` lie in `N`. -/
def ColengthDvd : Prop :=
  ∀ (n : ℕ) (Φ : Fin n → V), (∀ k : Fin n, Φ k ∈ M) → ∃ m : Matrix (Fin n) (Fin n) O,
    det m ∣ z ∧ ∀ i : Fin n, ∑ k : Fin n, m i k • Φ k ∈ N

@[simp]
lemma ColengthDvd.of_le (hMN : M ≤ N) : ColengthDvd M N z := fun _ _ hΦ ↦
  ⟨1, by simp, fun i ↦ by simpa [Matrix.one_apply] using hMN (hΦ i)⟩

lemma ColengthDvd.of_dvd (hMN : ColengthDvd M N z) (hz : z ∣ z') : ColengthDvd M N z' :=
  fun n Φ hΦ ↦ (hMN n Φ hΦ).imp fun _ ⟨h_det, h_mem⟩ ↦ ⟨h_det.trans hz, h_mem⟩

/-- Colength bounds multiply along chains. Let `M`, `N`, `P` be submodules of `V`, with no inclusion
assumed. If every finite family in `M` is carried into `N` by a square matrix whose determinant
divides `z` (this is `ColengthDvd M N z`), and likewise from `N` into `P` with `a`, then every
finite family in `M` is carried into `P` by a square matrix whose determinant divides `z * a`. -/
lemma ColengthDvd.trans (hMN : ColengthDvd M N z) (hNP : ColengthDvd N P a) :
    ColengthDvd M P (z * a) := by
  intro n Φ hΦ
  -- combine `Φ` by `m` into `N`, then combine the results by `m'` into `P`
  obtain ⟨m, hm_det, hm_mem⟩ := hMN n Φ hΦ
  obtain ⟨m', hm'_det, hm'_mem⟩ := hNP n (fun i : Fin n ↦ ∑ k, m i k • Φ k) hm_mem
  have h_assoc (i : Fin n) : ∑ k, (m' * m) i k • Φ k = ∑ j, m' i j • ∑ k, m j k • Φ k := by
    simpa [mul_apply, Finset.sum_smul, Finset.smul_sum, mul_smul] using Finset.sum_comm
  refine ⟨m' * m, ?_, fun i ↦ by simpa only [h_assoc] using hm'_mem i⟩
  simpa [mul_comm z] using mul_dvd_mul hm'_det hm_det

/-- Colength bounds pull back along a linear map `f : U → V`. Let every finite family in `M` be
carried into `N` by a square matrix whose determinant divides `z` (this is `ColengthDvd M N z`). If
`M'`, `N'` are submodules of `U` such that `f (M') ⊆ M` and every `x ∈ M'` with `f x ∈ N` lies in
`N'`, then the same holds for `M'`, `N'` and `z`. -/
lemma ColengthDvd.comap (hMN : ColengthDvd M N z) (f : U →ₗ[O] V) (hM : M' ≤ M.comap f)
    (hN : ∀ x ∈ M', f x ∈ N → x ∈ N') : ColengthDvd M' N' z := by
  intro n Φ hΦ
  obtain ⟨m, hm_det, hm_mem⟩ := hMN n (f ∘ Φ) fun k ↦ hM (hΦ k)
  exact ⟨m, hm_det, fun i ↦ hN _ (sum_smul_mem M' _ fun k _ ↦ hΦ k) (by simpa using hm_mem i)⟩

/-- Colength bounds push forward along a linear map `f : V → U`. Let every finite family in `M` be
carried into `N` by a square matrix whose determinant divides `z` (this is `ColengthDvd M N z`). If
`M'`, `N'` are submodules of `U` such that `M' ⊆ f (M) + N'` and `f (N) ⊆ N'`, then the same holds
for `M'`, `N'` and `z`. -/
lemma ColengthDvd.map (hMN : ColengthDvd M N z) (f : V →ₗ[O] U) (hM' : M' ≤ M.map f ⊔ N')
    (hN : N.map f ≤ N') : ColengthDvd M' N' z := by
  intro n Φ hΦ
  -- Write `Φ k = f (x k) + y k` with `x k ∈ M` and `y k ∈ N'`.
  have h_split (k : Fin n) : ∃ x ∈ M, ∃ y ∈ N', f x + y = Φ k := by
    simpa using mem_sup.1 (hM' (hΦ k))
  choose x hx y hy hxy using h_split
  obtain ⟨m, hm_det, hm_mem⟩ := hMN n x hx
  refine ⟨m, hm_det, fun i ↦ ?_⟩
  -- The combination of the Φ k is f (∑ k, m i k • x k) plus a combination of the y k.
  simpa [← hxy, sum_add_distrib] using
    add_mem (hN (mem_map_of_mem (hm_mem i))) (sum_smul_mem N' (m i) fun k _ ↦ hy k)

/-- Let `M`, `N` be submodules of `V` and let the endomorphism `f` keep `M`. If every finite family
in `M` is carried into `f (M) + a • M` by a square matrix whose determinant divides `z`, and into
`N + a • M` by one whose determinant divides `z'` (these are instances of `ColengthDvd`), then it is
carried into `f (N) + a • M` by one whose determinant divides `z * z'`. -/
lemma ColengthDvd.comp {f : V →ₗ[O] V} (hf_keep : M.map f ≤ M)
    (hf_onto : ColengthDvd M (M.map f ⊔ a • M) z) (hMN : ColengthDvd M (N ⊔ a • M) z') :
    ColengthDvd M (N.map f ⊔ a • M) (z * z') := by
  -- Push `hMN` forward by `f` and chain it after `hf_onto`; `f (a • M) ≤ a • M` because `f` keeps
  -- `M`.
  refine hf_onto.trans (hMN.map f (by order) ?_)
  grw [Submodule.map_sup, map_pointwise_smul, hf_keep]

/-! ### Endomorphisms that are onto up to a bounded colength -/

/-- The endomorphism `y` of `V` keeps `M` and is onto on `M` modulo `p ^ n` up to a colength
dividing `p ^ l`, for some natural number `l ≤ c`: every finite family in `M` is carried into
`y (M) + p ^ n • M` by a square matrix whose determinant divides `p ^ l` (see `ColengthDvd`). -/
def IsOntoUpToColength (p : O) (M : Submodule O V) (n : ℕ) (y : End O V) (c : ℝ) : Prop :=
  M.map y ≤ M ∧ ∃ l : ℕ, l ≤ c ∧ ColengthDvd M (M.map y ⊔ p ^ n • M) (p ^ l)

/-- The bounds on exponents add under products. Here `IsOntoUpToColength z M s y c` says that the
endomorphism `y` keeps the submodule `M` and that, for some natural number `j ≤ c`, every finite
family in `M` is carried into `y (M) + z ^ s • M` by a square matrix whose determinant divides
`z ^ j`. If each `T l`, `l` in the list `L`, satisfies this with bound `t l`, then the product of
the `T l` satisfies it with bound the sum of the `t l`. -/
lemma IsOntoUpToColength.prod {s : ℕ} {T : ι → End O V} {t : ι → ℝ} (L : List ι)
    (hT : ∀ l ∈ L, IsOntoUpToColength z M s (T l) (t l)) :
    IsOntoUpToColength z M s (L.map T).prod (L.map t).sum := by
  induction L with
  | nil => simp [IsOntoUpToColength, End.one_eq_id]
  | cons a L ih =>
    -- The product `T a ∘ ∏ L` keeps `M`, and the bounds multiply by `ColengthDvd.comp`.
    obtain ⟨ha_map, i, hi, ha⟩ := hT a List.mem_cons_self
    obtain ⟨hL_map, j, hj, hL⟩ := ih fun l hl ↦ hT l (List.mem_cons_of_mem a hl)
    rw [IsOntoUpToColength, List.map_cons, List.prod_cons, End.mul_eq_comp, map_comp]
    refine ⟨by grw [hL_map, ha_map], i + j, by simpa using add_le_add hi hj, ?_⟩
    simpa [pow_add] using ColengthDvd.comp ha_map ha hL

/-! ### The image of a square matrix over a valuation domain -/

/-- Let `O` be a valuation domain, `M` a submodule of `V`, `f` a linear form on `V` and `a : O`. The
vectors of `M` on which `f` is divisible by `a` have colength dividing `a` in `M`, in the sense of
`ColengthDvd`: every finite family in `M` is carried into them by a square matrix whose determinant
divides `a`. -/
lemma colengthDvd_inf_comap_span [IsDomain O] [ValuationRing O] (M : Submodule O V) (f : V →ₗ[O] O)
    (a : O) : ColengthDvd M (M ⊓ Submodule.comap f (Ideal.span {a})) a := by
  intro n Φ hΦ
  obtain rfl | hn := n.eq_zero_or_pos
  · exact ⟨1, by simp, finZeroElim⟩
  -- Take a member `Φ p` whose value divides the others, subtract multiples of it to clear them,
  -- and multiply it by `a`.
  classical
  obtain ⟨p, -, hp⟩ := exists_max_image univ (fun k ↦ Ideal.span {f (Φ k)}) ⟨⟨0, hn⟩, mem_univ _⟩
  replace hp (k : Fin n) : f (Φ p) ∣ f (Φ k) :=
    Ideal.span_singleton_le_span_singleton.1 (hp k (mem_univ k))
  choose c hc using hp
  let m : Matrix (Fin n) (Fin n) O := updateCol 1 p fun i ↦ if i = p then a else -c i
  have h_det : m.det = a := by simp [m, ← cramer_apply, cramer_one]
  have h_comb (i : Fin n) : ∑ k, m i k • Φ k = if i = p then a • Φ p else Φ i - c i • Φ p := by
    obtain rfl | hip := eq_or_ne i p
    · rw [Fintype.sum_eq_single i] <;> simp +contextual [m, eq_comm]
    · rw [Fintype.sum_eq_add i p hip] <;>
        simp +contextual [m, hip, Ne.symm hip, sub_eq_add_neg, eq_comm]
  refine ⟨m, h_det.dvd, fun i ↦ ⟨sum_smul_mem M _ fun k _ ↦ hΦ k, ?_⟩⟩
  rw [h_comb]
  split_ifs <;> simp [Ideal.mem_span_singleton, hc i, mul_comm]

/-- Let `O` be a valuation domain and `A` a square matrix over `O` indexed by `ι` whose determinant
divides `z`. If the submodule `L` of `ι → O` contains the image of `A`, then `L` has colength
dividing `z` in the sense of `ColengthDvd`: every finite family in `ι → O` is carried into `L` by a
square matrix, of the size of the family, whose determinant divides `z`.

A consequence of the elementary divisor theorem (Smith normal form) over a valuation domain. -/
lemma ColengthDvd.of_det_dvd [IsDomain O] [ValuationRing O] [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι O} {L : Submodule O (ι → O)} (h_dvd : A.det ∣ z)
    (h_le : LinearMap.range A.mulVecLin ≤ L) : ColengthDvd (⊤ : Submodule O (ι → O)) L z := by
  -- Write `A = g · diag(d) · g'` with `g`, `g'` invertible. Let `S s` consist of the vectors `x`
  -- such that the `j`-th coordinate of `g⁻¹ x` is divisible by `d j` for all `j ∈ s`.
  obtain ⟨g, -, g', -, d, rfl⟩ := isValuationPair_top.smith_normal_form A
  let f (j : ι) : (ι → O) →ₗ[O] O := .proj j ∘ₗ g⁻¹.val.mulVecLin
  let S (s : Finset ι) : Submodule O (ι → O) := ⨅ j ∈ s, Submodule.comap (f j) (Ideal.span {d j})
  -- Each further coordinate costs `d j`.
  have h_chain (s : Finset ι) : ColengthDvd ⊤ (S s) (∏ j ∈ s, d j) := by
    induction s using Finset.induction with
    | empty => exact .of_le (by simp [S])
    | insert j s hj ih =>
      simpa only [S, Finset.iInf_insert, inf_comm, prod_insert hj, mul_comm] using
        ih.trans (colengthDvd_inf_comap_span _ (f j) (d j))
  -- The last module lies in the image of `A`.
  have h_image : S univ ≤ LinearMap.range (g.val * diagonal d * g'.val).mulVecLin := by
    intro x hx
    simp only [S, mem_iInf, mem_univ, forall_const] at hx
    choose w hw using fun j ↦ Ideal.mem_span_singleton.1 (hx j)
    have h_diag : diagonal d *ᵥ w = g⁻¹.val *ᵥ x :=
      funext fun j ↦ by simpa [f, mulVec_diagonal] using (hw j).symm
    exact ⟨g'⁻¹.val *ᵥ w, by simp [mul_assoc, h_diag]⟩
  have h_prod : ∏ j, d j ∣ z := .trans (by simp) h_dvd
  simpa using ((h_chain univ).of_dvd h_prod).trans (of_le (z := 1) (h_image.trans h_le))

/-- Over a valuation domain `O`, the submodule `a • O ^ ι` of `O ^ ι` has colength dividing
`a ^ #ι` in the sense of `ColengthDvd`: every finite family in `O ^ ι` is carried into `a • O ^ ι`
by a square matrix whose determinant divides `a ^ #ι`. -/
lemma colengthDvd_top_smul_top [IsDomain O] [ValuationRing O] [Fintype ι] [DecidableEq ι] (a : O) :
    ColengthDvd (⊤ : Submodule O (ι → O)) (a • ⊤) (a ^ Fintype.card ι) := by
  refine .of_det_dvd (A := a • (1 : Matrix ι ι O)) (by simp) ?_
  rintro _ ⟨v, rfl⟩
  simpa [smul_mulVec] using smul_mem_pointwise_smul v a ⊤ mem_top

/-- Over a valuation domain `O`, let `N` be a submodule of `V` and `s` a finite set of vectors. The
colength of `N + z • V` in `N + span s` divides `z ^ #s`, in the sense of `ColengthDvd`: every
finite family in `N + span s` is carried into `N + z • V` by a square matrix whose determinant
divides `z ^ #s`. -/
lemma colengthDvd_sup_span [IsDomain O] [ValuationRing O] (N : Submodule O V) (s : Finset V)
    (z : O) : ColengthDvd (N ⊔ span O (s : Set V)) (N ⊔ z • ⊤) (z ^ #s) := by
  -- Push the bound for `z • O ^ s` in `O ^ s` forward along the map to linear combinations of `s`.
  classical
  let comb : (s → O) →ₗ[O] V := Fintype.linearCombination O fun v : s ↦ (v : V)
  have h_range : Submodule.map comb ⊤ = span O s := by simp [comb, Fintype.range_linearCombination]
  have h_free : ColengthDvd (⊤ : Submodule O (s → O)) (z • ⊤) (z ^ #s) := by
    simpa using colengthDvd_top_smul_top (ι := s) z
  refine h_free.map comb (by order) ?_
  grw [map_pointwise_smul, le_top (a := Submodule.map comb ⊤), ← le_sup_right]

/-! ### Comparison with lengths -/

/-- Over a discrete valuation ring `O`, `ColengthDvd` bounds a length. Let `M`, `N` be submodules of
`V` with `M` finitely generated; `N` need not lie in `M`. If every finite family in `M` is carried
into `N` by a square matrix whose determinant divides `z`, then `relLength M N`, the length of
`M / (M ∩ N)`, is at most the length of `O / z`. -/
lemma ColengthDvd.relLength_le [IsDomain O] [IsDiscreteValuationRing O]
    (hMN : ColengthDvd M N z) (hM : M.FG) :
    relLength M N ≤ length O (O ⧸ Ideal.span {z}) := by
  -- For generators `Φ` of `M` the hypothesis gives a matrix `m` with `det m ∣ z` and `m Φ` in `N`.
  -- Write `m = Q * diagonal a * P` in Smith normal form. The vectors `Ψ = P Φ` still generate `M`
  -- and `a j • Ψ j ∈ N`, so the quotient is an image of the product of the `O / a j`.
  -- `DVR O` bundles the two instances above; it is assumed by the imported lemmas on lengths.
  have : DVR O := {}
  obtain ⟨n, Φ, rfl⟩ := fg_iff_exists_fin_generating_family.1 hM
  obtain ⟨m, hm_det, hm_mem⟩ := hMN n Φ fun i ↦ subset_span ⟨i, rfl⟩
  obtain ⟨Q, -, P, -, a, rfl⟩ := isValuationPair_top.smith_normal_form m
  let Ψ : Fin n → V := P.val • Φ
  have h_comb : diagonal a • Ψ = Q⁻¹.val • (Q.val * diagonal a * P.val) • Φ := by
    simp only [Ψ, smul_smul, mul_assoc, Units.inv_mul_cancel_left]
  have h_kill (j : Fin n) : a j • N.mkQ (Ψ j) = 0 := by
    rw [← map_smul, mkQ_apply, Quotient.mk_eq_zero,
      show a j • Ψ j = (diagonal a • Ψ) j by simp [diagonal], h_comb]
    exact N.sum_mem fun i _ ↦ N.smul_mem (Q⁻¹.val j i) (hm_mem i)
  let π : (∀ j : Fin n, O ⧸ Ideal.span {a j}) →ₗ[O] V ⧸ N :=
    ∑ j, liftQSpanSingleton (a j) (.toSpanSingleton O _ (N.mkQ (Ψ j))) (h_kill j) ∘ₗ .proj j
  have h_onto : (span O (Set.range Φ)).map N.mkQ ≤ .map π ⊤ := by
    rw [map_le_iff_le_comap, span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨fun j ↦ Submodule.Quotient.mk (P⁻¹.val i j), mem_top, ?_⟩
    have h_back : P⁻¹.val • Ψ = Φ := by simp [Ψ, smul_smul]
    -- The classes stay `Submodule.Quotient.mk`, the form on which `π` evaluates.
    simp [π, ← h_back, -Ideal.Quotient.mk_eq_mk]
  have h_dvd : ∏ j, a j ∣ z := .trans (by simp) hm_det
  calc relLength (span O (Set.range Φ)) N
    _ ≤ length O (⊤ : Submodule O (∀ j : Fin n, O ⧸ Ideal.span {a j})) :=
      (relLength_eq_length_map_mkQ _ _).trans_le (length_le_of_le_map π ⊤ h_onto)
    _ = IsDiscreteValuationRing.addVal O (∏ j, a j) := by simp [addVal_prod]
    _ ≤ IsDiscreteValuationRing.addVal O z := IsDiscreteValuationRing.addVal_le_iff_dvd.2 h_dvd
    _ = length O (O ⧸ Ideal.span {z}) := length_quot_span_eq_addVal.symm

/-- Let `M` be a finitely generated submodule of `V` over a discrete valuation ring `O`, and let
`IsOntoUpToColength p M n y c` hold: the endomorphism `y` keeps `M` and, for some natural number
`l ≤ c`, every finite family in `M` is carried into `y (M) + p ^ n • M` by a square matrix whose
determinant divides `p ^ l`. Then, for some natural number `l ≤ c`, the length
`relLength M (y (M) + p ^ n • M)` of `M / (y (M) + p ^ n • M)` is at most `l` times the length of
`O / p`. -/
lemma IsOntoUpToColength.exists_relLength_le [IsDomain O] [IsDiscreteValuationRing O] {p : O}
    {n : ℕ} {y : End O V} {c : ℝ} (h_onto : IsOntoUpToColength p M n y c) (hM : M.FG) :
    ∃ l : ℕ, l ≤ c ∧ relLength M (M.map y ⊔ p ^ n • M) ≤ l * length O (O ⧸ Ideal.span {p}) := by
  have : DVR O := {}
  obtain ⟨-, l, hl, h_colength⟩ := h_onto
  exact ⟨l, hl, (h_colength.relLength_le hM).trans_eq (by simp [length_quot_span_eq_addVal])⟩

end New
