import Lib.LocalGL.Iwahori.QuadraticRelation
import Lib.Weil.Unramified.HeckeGL

/-!
# Iwahori degrees, partial Hecke sums and Satake's formula

Let `F` be the completion at `w`, with ring of integers `𝒪`, uniformiser `ϖ` and residue field of
order `q`, and let `K0 = New.proIwahori` be the pro-`p` Iwahori subgroup of `GL_N(𝒪)`. An exponent
is a linear form that is an eigenform for the torus character
`New.torusChar θ = ∏ θ_i(t_i) |t_i| ^ (N - 1 - i)`. This file computes the Hecke operator of a
dominant double coset `K0 t K0` on `K0`-fixed vectors by counting its cosets. It defines partial
Hecke operators as sums over the `g` in `New.basicDoubleCoset` (`ϖ 𝒪^N ⊆ g 𝒪^N ⊆ 𝒪^N`,
colength `j`) whose lattice contains the first `r` basis vectors. A count of hyperplanes over the
residue field relates `r` and `r + 1` and gives Satake's formula for the eigenvalue on an exponent.
It also proves a duality of lattices for these operators.

## Main definitions and results

* `New.heckeFun_iwahoriDoubleCoset_eq_iwahoriDegree_smul`: the operator of a dominant double coset
  `K t K` (`K = proIwahori`) on `K`-fixed vectors, through the number `New.iwahoriDegree t` of its
  cosets.
* `New.partialCosets`, `New.partialHecke`: the lattices that contain the first `r` basis vectors,
  and the sum over them. It is the `j`-th Hecke operator for `r = 0`, and `0` for `r = N`, `0 < j`.
* `New.echelonRows`, `New.card_echelonRows_mem_residueKer`: the rows `(0, …, 0, 1, *, …, *)` over
  the residue field, and how many of them kill a lattice.
* `New.partialHecke_hyperplane_count`: a count of hyperplanes that relates `r` and `r + 1`.
* `New.IsExponent.apply_partialHecke`: Satake's formula for the eigenvalue on an exponent, by
  descent in `r`.

Notions from other files:
* `New.dominantTorus`: The diagonal t with `v (t i) ≤ v (t j)` for i ≤ j.
* `New.blockParahoric`: For a level function b on the indices, the g in GL_N(𝒪) with g_ij in the
  maximal ideal whenever b(j) < b(i).
* `New.IsExponent`: For a character ξ of the torus, the linear form l satisfies l(ρ(t) · mean of x
  over K0) = ξ(t) l(x) for all x and all dominant t.
* `New.heckeCoset`: The Hecke operator of the double coset KgK: the sum of ρ(h) over chosen
  representatives h of the cosets hK in KgK.
* `New.compactMean`: The mean of ρ(h)x over h in a compact subgroup H, for a smooth ρ.

## Relation to the literature

Known; see `Lib.LocalGL.Iwahori.SphericalExponents` for sources.
-/

noncomputable section

section HeckeCounts

open Matrix Module WithZero Valued Finset DoubleCoset Ideal Pi Fin Quotient Nat
  Function.HasFiniteSupport

namespace New

variable {E V : Type*} [Field E] [NumberField E] {w : FinPlace E} [AddCommGroup V] [Module ℂ V]
  {N j : ℕ} {ρ : Representation ℂ (GL (Fin N) (LocField w)) V} {ϖ : (LocField w)ˣ}
  {g k : GL (Fin N) (LocField w)} {m : ℕ} {x : V} (r : Fin N)

/-! ### Double cosets of the pro-`p` Iwahori subgroup -/

attribute [-simp] WithZero.inv_exp
attribute [local simp] WithZero.exp_neg

/-- The product of `‖t j / t i‖` over the pairs `i < j`. For dominant `t` it is the number of
cosets in `K0 t K0 / K0`, the factor in `New.heckeFun_iwahoriDoubleCoset_eq_iwahoriDegree_smul`. -/
@[simp]
def iwahoriDegree (t : Fin N → (LocField w)ˣ) : ℂ :=
  ∏ p : Fin N × Fin N with p.1 < p.2, ‖(t p.2 / t p.1).1‖

/-- Multiplying on the left by an upper unitriangular `u` keeps the difference of the entries
`(i, l)` of two matrices whose columns `l` agree below row `i`. -/
lemma mul_apply_sub_mul_apply_of_unitriangular {u : GL (Fin N) (LocField w)}
    (hu : u ∈ unitriangular id (LocField w)) {A B : Matrix (Fin N) (Fin N) (LocField w)}
    {i l : Fin N} (h_below : ∀ a : Fin N, i < a → A a l = B a l) :
    (u.val * A) i l - (u.val * B) i l = A i l - B i l := by
  have h_entry (a : Fin N) (ha : a ≤ i) :
      u.val i a = (1 : Matrix (Fin N) (Fin N) (LocField w)) i a :=
    mem_agreeWithOneOn.mp hu i a ha
  rw [Matrix.mul_apply, Matrix.mul_apply, ← sum_sub_distrib, sum_eq_single i _ (by simp)]
  · simp [h_entry i le_rfl]
  · intro a _ ha
    obtain ha | ha := ha.lt_or_gt
    · simp [h_entry a ha.le, ha.ne']
    · simp [h_below a ha]

/-- Let `t` be a torus element and `x` be fixed by `K = proIwahori`. If the `r c * t`, for `c` in a
finite type `C` and `r c ∈ K`, represent each coset of `K t K / K` exactly once, then the operator
of the double coset `K t K` sends `x` to `#C` times the mean over `K` of `ρ t x`. -/
private lemma heckeFun_iwahoriDoubleCoset_eq_card_smul [IsSmoothRep ρ] {t : Fin N → (LocField w)ˣ}
    {C : Type*} [Fintype C] {r : C → GL (Fin N) (LocField w)} (hr_mem : ∀ c : C, r c ∈ proIwahori)
    (h_unique : ∀ k ∈ proIwahori, ∃! c : C, (k * diagGL t)⁻¹ * (r c * diagGL t) ∈ proIwahori)
    (hx : x ∈ levelSpace ρ proIwahori) :
    heckeFun ρ proIwahori ((iwahoriDoubleCoset t).indicator 1) x =
      (Fintype.card C : ℂ) • compactMean ρ proIwahori (ρ (diagGL t) x) := by
  set f : GL (Fin N) (LocField w) → ℂ := (iwahoriDoubleCoset t).indicator 1
  have hf : IsHeckeFunction proIwahori f := isHeckeFunction_doubleCoset isOpen_proIwahori (diagGL t)
  -- The `r c * t` represent the cosets of the double coset, each once.
  have h_distinct : Set.InjOn
      (fun c ↦ (↑(r c * diagGL t) : GL (Fin N) (LocField w) ⧸ proIwahori)) (univ : Finset C) :=
    fun c _ d _ hcd ↦
      (h_unique (r c) (hr_mem c)).unique (by simp [one_mem]) (QuotientGroup.eq.mp hcd)
  have h_cover (g : GL (Fin N) (LocField w)) (hg : f g ≠ 0) :
      ∃ c ∈ (univ : Finset C), (↑(r c * diagGL t) : GL (Fin N) (LocField w) ⧸ proIwahori) = g := by
    obtain ⟨k, hk, l, hl, rfl⟩ : ∃ k ∈ proIwahori, ∃ l ∈ proIwahori, g = k * diagGL t * l :=
      mem_doubleCoset.mp (Set.mem_of_indicator_ne_zero hg)
    obtain ⟨c, hc, -⟩ := h_unique k hk
    exact ⟨c, mem_univ c,
      (QuotientGroup.eq.mpr hc).symm.trans (QuotientGroup.mk_mul_of_mem _ hl).symm⟩
  have hf_one (c : C) : f (r c * diagGL t) = 1 :=
    Set.indicator_of_mem (mem_doubleCoset.mpr ⟨r c, hr_mem c, 1, one_mem _, (mul_one _).symm⟩) 1
  have h_sum : heckeFun ρ proIwahori f x = ∑ c : C, ρ (r c) (ρ (diagGL t) x) := by
    rw [(heckeFun_eq_sum (fun g k ↦ (hf.right g k.val k.prop).left) hx h_distinct h_cover).2]
    simp [hf_one]
  -- The left side is fixed by `K`, so it equals its mean.
  calc heckeFun ρ proIwahori f x
      = compactMean ρ proIwahori (heckeFun ρ proIwahori f x) :=
        (compactMean_eq_self _ (hf.heckeFun_mem hx)).symm
    _ = ∑ _c : C, compactMean ρ proIwahori (ρ (diagGL t) x) := by
        simp [h_sum, map_sum, compactMean_apply (hr_mem _)]
    _ = (Fintype.card C : ℂ) • compactMean ρ proIwahori (ρ (diagGL t) x) := by
        simp [Nat.cast_smul_eq_nsmul]

/-- For dominant `t` and `i ≤ j`, the quotient `t i / t j` is integral. -/
private lemma coe_div_mem_integer_of_mem_dominantTorus {t : Fin N → (LocField w)ˣ}
    (ht : t ∈ dominantTorus) {i j : Fin N} (hij : i ≤ j) : (t i / t j).val ∈ 𝒪[LocField w] := by
  simp [v.mem_integer_iff, ht hij, div_le_one_of_le₀]

/-- For dominant `t`, the families `c` of classes `c (i, j)` in `𝒪 / (t i / t j)`, over the pairs
`i < j`. -/
private abbrev UnitriangularClasses (t : Fin N → (LocField w)ˣ) (ht : t ∈ dominantTorus) : Type _ :=
  ∀ p : {p : Fin N × Fin N // p.fst < p.snd}, 𝒪[LocField w] ⧸
    span {(⟨(t p.val.fst / t p.val.snd).val,
      coe_div_mem_integer_of_mem_dominantTorus ht p.property.le⟩ : 𝒪[LocField w])}

/-- The upper unitriangular integral matrix whose entries above the diagonal are representatives of
the classes `c`. -/
private def unitriangularOfClasses {t : Fin N → (LocField w)ˣ} {ht : t ∈ dominantTorus}
    (c : UnitriangularClasses t ht) : Matrix (Fin N) (Fin N) (LocField w) :=
  of fun i j ↦ (if h : i < j then (c ⟨(i, j), h⟩).out else diagonal 1 i j : 𝒪[LocField w]).val

/-- Let `t` be dominant, and let `r c ∈ K = proIwahori` have the matrix `unitriangularOfClasses c`
for each family `c` of classes. Then for each `k ∈ K` exactly one `c` has `(k t)⁻¹ (r c t) ∈ K`: the
cosets `r c * t * K` are those of the double coset `K t K`, each once. -/
private lemma existsUnique_inv_mul_mem_proIwahori {t : Fin N → (LocField w)ˣ}
    (ht : t ∈ dominantTorus) [Finite (UnitriangularClasses t ht)]
    {r : UnitriangularClasses t ht → GL (Fin N) (LocField w)}
    (hr_mem : ∀ c : UnitriangularClasses t ht, r c ∈ proIwahori)
    (hr : ∀ c : UnitriangularClasses t ht, (r c).val = unitriangularOfClasses c)
    (hr_tri : ∀ c : UnitriangularClasses t ht, r c ∈ unitriangular id (LocField w))
    {k : GL (Fin N) (LocField w)} (hk : k ∈ proIwahori) :
    ∃! c : UnitriangularClasses t ht, (k * diagGL t)⁻¹ * (r c * diagGL t) ∈ proIwahori := by
  -- Replace `k` by an upper unitriangular `u` with `k t K = u t K`, and let `Ψ c` be the classes
  -- of the entries of `u⁻¹ * r c` above the diagonal.
  obtain ⟨u, ⟨hu_tri, hu_mem⟩, huk⟩ : ∃ u ∈ unitriangular id (LocField w) ⊓ proIwahori,
      (diagGL t)⁻¹ * (u⁻¹ * k) * diagGL t ∈ proIwahori :=
    exists_unipotent_conj_mem_proIwahori ht hk
  have h_entry_int (c : UnitriangularClasses t ht) (p : {p : Fin N × Fin N // p.fst < p.snd}) :
      (u⁻¹ * r c).val p.val.fst p.val.snd ∈ 𝒪[LocField w] :=
    (mem_proIwahori.mp (proIwahori.mul_mem (inv_mem hu_mem) (hr_mem c))).left _ _
  let Ψ (c : UnitriangularClasses t ht) : UnitriangularClasses t ht := fun p ↦
    Ideal.Quotient.mk _ ⟨(u⁻¹ * r c).val p.val.fst p.val.snd, h_entry_int c p⟩
  have h_iff (c : UnitriangularClasses t ht) :
      (k * diagGL t)⁻¹ * (r c * diagGL t) ∈ proIwahori ↔ Ψ c = 0 := by
    have h_conj_tri : (diagGL t)⁻¹ * (u⁻¹ * r c * diagGL t) ∈ unitriangular id (LocField w) := by
      rw [← mul_assoc]
      exact conj_mem_unitriangular (blockTriangular_diagonal _)
        (mul_mem (inv_mem hu_tri) (hr_tri c))
    rw [← mul_mem_cancel_left huk]
    -- Conjugation by `t` divides the entry `(i, j)` by `t i / t j`.
    simp only [mul_assoc, _root_.mul_inv_rev, mul_inv_cancel_left]
    rw [← mul_assoc u⁻¹, mem_proIwahori_iff_of_unitriangular h_conj_tri]
    simp [Ψ, UnitriangularClasses, funext_iff, Quotient.eq_zero_iff_dvd, diagGL, inv_mul_le_iff₀,
      le_div_iff₀, zero_lt_iff, (Valuation.integer.integers v).dvd_iff_le,
      Algebra.algebraMap_ofSubsemiring_apply]
  -- `Ψ` is injective: in each column compare the entries from the bottom up.
  have h_inj : Ψ.Injective := by
    refine fun c d hcd ↦ funext fun ⟨(i, j), hij⟩ ↦ ?_
    induction i using WellFoundedGT.induction with | ind i ih =>
    have h_below (a : Fin N) (ha : i < a) : (r c).val a j = (r d).val a j := by
      by_cases haj : a < j
      · simp [hr, unitriangularOfClasses, haj, ih a ha haj]
      · simp [hr, unitriangularOfClasses, haj]
    have h_sub : (r c).val i j - (r d).val i j = (u⁻¹ * r c).val i j - (u⁻¹ * r d).val i j :=
      (mul_apply_sub_mul_apply_of_unitriangular (inv_mem hu_tri) h_below).symm
    -- The representatives of `c` and `d` at `(i, j)` differ by the difference of the entries of
    -- `u⁻¹ * r c` and `u⁻¹ * r d`, which lies in the ideal as `Ψ c = Ψ d`.
    have h_out : (c ⟨(i, j), hij⟩).out - (d ⟨(i, j), hij⟩).out =
        ⟨(u⁻¹ * r c).val i j, h_entry_int c ⟨(i, j), hij⟩⟩ -
          ⟨(u⁻¹ * r d).val i j, h_entry_int d ⟨(i, j), hij⟩⟩ := by
      apply Subtype.ext
      simpa [hr, unitriangularOfClasses, show i < j from hij] using h_sub
    refine Quotient.out_equiv_out.mp ((Submodule.quotientRel_def _).mpr ?_)
    rw [h_out]
    exact Ideal.Quotient.eq.mp (congrFun hcd ⟨(i, j), hij⟩)
  exact (existsUnique_congr h_iff).mpr (h_inj.bijective_of_finite.existsUnique 0)

/-- Let `K = proIwahori` be the pro-`p` Iwahori subgroup (upper unitriangular modulo the maximal
ideal), `ρ` smooth, and `t` dominant (`v (t i) ≤ v (t j)` for `i ≤ j`). Then for `x` fixed by `K`,
the Hecke operator of the indicator of the double coset `K diag(t) K` sends `x` to `iwahoriDegree t`
times the mean over `K` of `ρ (diag t) x`. Here `iwahoriDegree t` is the product of `‖t j / t i‖`
over `i < j`, the number of cosets in `K t K / K`. -/
@[simp↓] lemma heckeFun_iwahoriDoubleCoset_eq_iwahoriDegree_smul [IsSmoothRep ρ]
    {t : Fin N → (LocField w)ˣ} (ht : t ∈ dominantTorus) (hx : x ∈ levelSpace ρ proIwahori) :
    heckeFun ρ proIwahori ((iwahoriDoubleCoset t).indicator 1) x =
      iwahoriDegree t • compactMean ρ proIwahori (ρ (diagGL t) x) := by
  -- The cosets in `K t K / K` are those of `r c * t`, where `r c` is upper unitriangular with
  -- entries `(i, j)` running over `𝒪 / (t i / t j)`. There are `iwahoriDegree t` of them, and each
  -- contributes the same vector after the mean over `K`.
  let C : Type _ := UnitriangularClasses t ht
  have h_card : iwahoriDegree t = (Nat.card C : ℝ) := by
    -- `𝒪 / (a)` has `‖a‖⁻¹` elements.
    rw [Nat.card_pi, Nat.cast_prod]
    -- `↓` makes both rewrites fire before their subterms are simplified.
    simp [↓genIndex_eq_inv_norm, ↓← genIndex_eq_card (isOpen_integer _) (isCompact_LocInt _),
      prod_subtype _ mem_filter_univ]
  have h_card_ne : Nat.card C ≠ 0 := by
    have h_degree_ne : iwahoriDegree t ≠ 0 := by simp [prod_eq_zero_iff]
    rw [h_card] at h_degree_ne
    exact_mod_cast h_degree_ne
  have : Finite C := Nat.finite_of_card_ne_zero h_card_ne
  let : Fintype C := Fintype.ofFinite C
  -- An element `r c` of `K` with the matrix `unitriangularOfClasses c`.
  have hM_tri (c : C) : (∀ i j : Fin N, j < i → v (unitriangularOfClasses c i j) < 1) ∧
      ∀ i : Fin N, v (unitriangularOfClasses c i i - 1) < 1 := by
    simp +contextual [unitriangularOfClasses, lt_asymm, ne_of_gt]
  have h_lift (c : C) : ∃ g ∈ proIwahori, g.val = unitriangularOfClasses c :=
    exists_proIwahori_coe_eq (unitriangularOfClasses c)
      (fun i j ↦ (if h : i < j then (c ⟨(i, j), h⟩).out else diagonal 1 i j : 𝒪[LocField w]).2)
      (hM_tri c)
  choose r hr_mem hr using h_lift
  have hr_tri (c : C) : r c ∈ unitriangular id (LocField w) := by
    simp +contextual [hr, unitriangularOfClasses, not_lt_of_ge, apply_ite, Matrix.one_apply]
  have h_unique (k : GL (Fin N) (LocField w)) (hk : k ∈ proIwahori) :
      ∃! c : C, (k * diagGL t)⁻¹ * (r c * diagGL t) ∈ proIwahori :=
    existsUnique_inv_mul_mem_proIwahori ht hr_mem hr hr_tri hk
  rw [heckeFun_iwahoriDoubleCoset_eq_card_smul hr_mem h_unique hx, h_card,
    Fintype.card_eq_nat_card, Complex.ofReal_natCast]

lemma coe_normAbsChar_locField (x : (LocField w)ˣ) : (normAbsChar x).val = ‖x.val‖ := by
  simp [normAbsChar, norm_locField_eq_q_zpow, ← card_ResField,
    show Nat.card 𝓀[LocField w] = Nat.card (ResField w) from rfl]

/-- For `N ≥ 1` and a uniformiser `ϖ` (`hϖ`), write `t = (ϖ, 1, …, 1)` and `K0 = proIwahori`.
Then (a) `t` is dominant; (b) on `K0`-fixed vectors the Hecke operator of `K0 t K0` is
`q ^ (N - 1)` times the mean over `K0` of `ρ t`, where `q` is the order of the residue field. -/
lemma heckeCoset_mulSingle_zero_eq (hϖ : v ϖ.val = exp (-1)) {x : V} [IsSmoothRep ρ] [NeZero N]
    (hx : x ∈ levelSpace ρ proIwahori) :
    let t : Fin N → (LocField w)ˣ := mulSingle 0 ϖ
    t ∈ dominantTorus ∧
    heckeCoset ρ proIwahori (diagGL t) x =
      (w.q : ℂ) ^ (N - 1) • compactMean ρ proIwahori (ρ (diagGL t) x) := by
  intro t
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (NeZero.ne N)
  have h_dom : t ∈ dominantTorus := by
    simp +decide [t, dominantTorus, Monotone, hϖ, Fin.forall_fin_succ]
  -- Only the pairs `(0, j)` with `0 < j` contribute to the degree, each the factor `‖ϖ⁻¹‖ = q`.
  have h_deg : iwahoriDegree t = (w.q : ℂ) ^ n := by
    simp +decide [t, hϖ, norm_locField_eq_q_zpow, prod_filter, Fintype.prod_prod_type,
      Fin.prod_univ_succ]
  refine ⟨h_dom, ?_⟩
  rw [heckeCoset, heckeFun_iwahoriDoubleCoset_eq_iwahoriDegree_smul h_dom hx, h_deg,
    Nat.add_sub_cancel]

/-! ### Lattices that contain the first basis vectors -/

/-- The `g` in `New.basicDoubleCoset` (colength `j`) whose lattice `g 𝒪^N` contains the first `r`
basis vectors, that is, the first `r` columns of `g⁻¹` are integral. -/
def partialCosets (r j : ℕ) : Set (GL (Fin N) (LocField w)) :=
  {g ∈ basicDoubleCoset (Fin N) w j | ∀ b a : Fin N, b.val < r → v (g⁻¹ a b) ≤ 1}

/-- The sum of `ρ g` over the cosets `g localIntGL` in `New.partialCosets r j`, one for each such
lattice. -/
def partialHecke (ρ : Representation ℂ (GL (Fin N) (LocField w)) V) (r j : ℕ) : End ℂ V :=
  heckeFun ρ (localIntGL (Fin N) w) ((partialCosets r j).indicator 1)

/-- `partialCosets m j` is the set of `g` in the basic double coset of colength `j` whose lattice
`g 𝒪^N` contains the first `m` standard basis vectors. This set is (a) invariant under left
multiplication by the parahoric subgroup `blockParahoric (fun i ↦ i + 1 - m)`, whose first block has
size `m` and all others size `1`, and (b) invariant under right multiplication by `GL N (𝒪)`
(`localIntGL`). -/
@[simp]
lemma mul_mem_partialCosets_iff :
    -- (a)
    (k ∈ blockParahoric (fun i : ℕ ↦ i + 1 - m) →
     (k * g ∈ partialCosets m j ↔ g ∈ partialCosets m j)) ∧
    -- (b)
    (k ∈ localIntGL (Fin N) w → (g * k ∈ partialCosets m j ↔ g ∈ partialCosets m j)) := by
  -- Prove stability; for `k` and for `k⁻¹` it gives both directions of each equivalence.
  have h_mul_mul_mem (g k l : GL (Fin N) (LocField w)) (hl : l ∈ localIntGL (Fin N) w)
      (hk : k ∈ blockParahoric fun i ↦ i + 1 - m) (hg : g ∈ partialCosets m j) :
      k * g * l ∈ partialCosets m j := by
    obtain ⟨hg_basic, hg_cols⟩ := hg
    obtain ⟨hk_int, -⟩ := mem_blockParahoric.mp hk
    refine ⟨mul_mul_mem_basicDoubleCoset hg_basic hk_int hl, fun b a hb ↦ ?_⟩
    -- Every term of the entry `(i, b)` of `g⁻¹ * k⁻¹` is integral, for a column `b < m`.
    have h_term (i c : Fin N) : v (g⁻¹ i c) * v (k⁻¹ c b) ≤ 1 := by
      by_cases hc : c.val < m
      · exact mul_le_one' (hg_cols c i hc) (hk_int.isIntMatrix_inv c b)
      · -- Here `v (g⁻¹ i c) ≤ exp 1` only, but `k⁻¹ c b` lies in the maximal ideal as `b < m ≤ c`.
        have h_small : v (k⁻¹ c b) < 1 := (mem_blockParahoric.mp (inv_mem hk)).2 c b (by lia)
        obtain ⟨-, hg_inv_le, -⟩ := hg_basic
        grw [hg_inv_le]
        simpa [← lt_mul_exp_iff_le] using h_small
    -- `(k * g * l)⁻¹ = l⁻¹ * (g⁻¹ * k⁻¹)` and `l⁻¹` is integral.
    exact 𝒪[LocField w].sum_mem fun i _ ↦ mul_mem (hl.isIntMatrix_inv a i)
      (v.map_sum_le fun c _ ↦ (map_mul v _ _).trans_le (h_term i c))
  refine ⟨fun hk ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩, fun hk ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩⟩
  · simpa using h_mul_mul_mem (k * g) k⁻¹ 1 (one_mem _) (inv_mem hk) h
  · simpa using h_mul_mul_mem g k 1 (one_mem _) hk h
  · simpa using h_mul_mul_mem (g * k) 1 k⁻¹ (inv_mem hk) (one_mem _) h
  · simpa using h_mul_mul_mem g 1 k hk (one_mem _) h

lemma hasFiniteCosets_partialCosets :
    HasFiniteCosets (A := ℂ) (localIntGL (Fin N) w) ((partialCosets m j).indicator 1) := by
  have h_sub : partialCosets m j ⊆ basicDoubleCoset (Fin N) w j := Set.sep_subset _ _
  refine (isHeckeFunction_basicDoubleCoset (A := ℂ) j).left.subset ?_
  -- The indicator of the smaller set vanishes wherever that of the larger one does.
  simpa using fun g hg ↦ h_sub hg

/-- For `r = 0` the condition on basis vectors is empty, and `New.partialHecke ρ 0 j` is the `j`-th
Hecke operator `New.heckeGL ρ j`. -/
lemma partialHecke_zero_eq_heckeGL : partialHecke ρ 0 j = heckeGL ρ j := by
  simp [partialHecke, partialCosets, heckeGL]

/-- No lattice of positive colength contains all `N` basis vectors, so
`New.partialHecke ρ N (j + 1)` is `0`. -/
@[simp]
lemma partialHecke_top_eq_zero : partialHecke ρ N (j + 1) = 0 := by
  -- `partialCosets N (j + 1)` is empty: `g` and `g⁻¹` integral force `v (det g) = 1`.
  have h_empty (g : GL (Fin N) (LocField w)) : g ∉ partialCosets N (j + 1) := by
    rintro ⟨⟨h_int, -, h_det⟩, h_inv⟩
    have hg : g ∈ localIntGL (Fin N) w := mem_intGL.mpr ⟨h_int, fun a b ↦ h_inv b a b.isLt⟩
    have h_exp_ne : (exp (-↑(j + 1)) : ℤᵐ⁰) ≠ 1 := fun h_eq ↦ nomatch h_eq
    exact h_exp_ne (h_det.symm.trans (mem_intGL_iff_det.mp hg).2)
  simp [partialHecke, heckeFun, h_empty]

/-- Dividing row `r` by the uniformiser `ϖ` (`hϖ`): the product lies in `partialCosets (r + 1) j`
iff `g` lies in `partialCosets r (j + 1)` and row `r` of `g` vanishes modulo `ϖ`. -/
lemma inv_mul_mem_partialCosets_iff (hϖ : v ϖ.val = exp (-1)) (r : Fin N)
    (g : GL (Fin N) (LocField w)) :
    (diagGL (mulSingle r ϖ))⁻¹ * g ∈ partialCosets (r + 1) j ↔
      g ∈ partialCosets r (j + 1) ∧ g.val.map residueOrZero r = 0 := by
  simp [partialCosets, basicDoubleCoset, diagGL, apply_ite, funext_iff, hϖ, field,
    ← @lt_mul_exp_iff_le (exp 1 * _), mulSingle_apply, ite_apply, -coe_units_inv]
  -- Row `r` of the product is row `r` of `g` divided by `ϖ`: it is integral iff row `r` of `g` lies
  -- in the maximal ideal. Column `r` of the inverse gains the factor `ϖ`, the determinant `ϖ⁻¹`.
  have h_exp : (exp 1 : ℤᵐ⁰) ≤ exp 2 := exp_le_exp.mpr (by norm_num)
  grind

/-- Let `g` lie in `basicDoubleCoset (Fin N) w j`. The lattice of `g` contains the first `m` basis
vectors iff the rows that kill `g` modulo the maximal ideal vanish at the indices below `m`. -/
lemma mem_partialCosets_iff_residueKer (hg : g ∈ basicDoubleCoset (Fin N) w j) :
    g ∈ partialCosets m j ↔
      ∀ u ∈ residueKer (transposeGL g).val, ∀ i : Fin N, i.val < m → u i = 0 := by
  -- For integral `z`, `z * (gᵀ)⁻¹` is integral iff the kernel of `gᵀ` modulo the maximal ideal lies
  -- in that of `z`; take for `z` the projection to the first `m` coordinates.
  let z : Matrix (Fin N) (Fin N) (LocField w) := diagonal fun i ↦ if i.val < m then 1 else 0
  have h_integral_iff : (∀ a b : Fin N, v ((z * (transposeGL g)⁻¹.val) a b) ≤ 1) ↔
      (∀ a b : Fin N, v (z a b) ≤ 1) ∧ residueKer (transposeGL g).val ≤ residueKer z :=
    v_mul_inv_le_one_iff (transposeGL_mem_basicDoubleCoset.mpr hg)
  simpa [z, partialCosets, hg, IsConcreteLE.le_iff, funext_iff, mulVec_diagonal, apply_ite,
    diagonal_apply, ite_apply, ← transpose_nonsing_inv] using h_integral_iff

/-- The rows `(0, …, 0, 1, *, …, *)` over the residue field, with the entry `1` at the index `r`. -/
def echelonRows : Finset (Fin N → ResField w) :=
  Fintype.piFinset fun i ↦
    if r < i then @univ (ResField w) (.ofFinite (ResField w)) else {if r = i then 1 else 0}

/-- The rows of `echelonRows r` are those with entry `1` at `r` and `0` before it. -/
lemma mem_echelonRows {u : Fin N → ResField w} :
    u ∈ echelonRows r ↔ u r = 1 ∧ ∀ i < r, u i = 0 := by
  simp only [echelonRows, Fintype.mem_piFinset]
  refine ⟨fun hu ↦ ⟨?_, fun i hi ↦ ?_⟩, fun ⟨h_one, h_zero⟩ i ↦ ?_⟩
  · simpa using hu r
  · simpa [hi.asymm, hi.ne'] using hu i
  · obtain hi | rfl | hi := lt_trichotomy i r
    · simp [hi.asymm, hi.ne', h_zero i hi]
    · simp [h_one]
    · simp [hi]

/-- There are `q ^ (N - 1 - r)` rows `(0, …, 0, 1, *, …, *)` with the entry `1` at `r`, where `q` is
the order of the residue field. -/
lemma card_echelonRows : #(echelonRows (w := w) r) = w.q ^ r.rev.val := by
  simp [echelonRows, apply_ite card, prod_ite, card_ResField, filter_lt_eq_Ioi,
    tsub_add_eq_tsub_tsub_swap, Fintype.card_eq_nat_card]

open scoped Classical in
/-- Let `g` lie in `partialCosets r (j + 1)`: it is in the basic double coset of colength `j + 1`
and its lattice `g 𝒪^N` contains the first `r` standard basis vectors. Consider the rows `u` in
`echelonRows r` over the residue field, which are `(0, …, 0, 1, *, …, *)` with the `1` at index `r`.
The number of such `u` in the kernel of the transpose of `g` reduced modulo the maximal ideal is `0`
if `g` also lies in `partialCosets (r + 1) (j + 1)`, and `q ^ j` otherwise, where `q` is the order
of the residue field. -/
lemma card_echelonRows_mem_residueKer (hg : g ∈ partialCosets r (j + 1)) :
    #{u ∈ echelonRows r | u ∈ residueKer (transposeGL g).val} =
      if g ∈ partialCosets (r + 1) (j + 1) then 0 else w.q ^ j := by
  have hg_basic : g ∈ basicDoubleCoset (Fin N) w (j + 1) := hg.left
  have h_low : ∀ u ∈ residueKer (transposeGL g).val, ∀ i : Fin N, i.val < r → u i = 0 :=
    (mem_partialCosets_iff_residueKer hg_basic).mp hg
  rw [mem_partialCosets_iff_residueKer hg_basic]
  set L : Submodule (ResField w) (Fin N → ResField w) := residueKer (transposeGL g).val
  split_ifs with hL
  · rw [Finset.card_eq_zero, filter_eq_empty_iff]
    intro u hu huL
    simpa [hL u huL r (Nat.lt_succ_self r)] using ((mem_echelonRows r).mp hu).left
  -- The coordinate `r` is a nonzero linear form on `L`, which has dimension `j + 1`.
  let p : Dual (ResField w) L := L.dualRestrict (.proj r)
  have hp_ne : p ≠ 0 := by
    refine fun hp ↦ hL fun u hu i hi ↦ ?_
    obtain hi | hi := Nat.lt_succ_iff_lt_or_eq.mp hi
    · exact h_low u hu i hi
    · rw [Fin.ext hi]
      exact LinearMap.congr_fun hp ⟨u, hu⟩
  have h_dim_L : finrank (ResField w) L = j + 1 :=
    finrank_residueKer (transposeGL_mem_basicDoubleCoset.mpr hg_basic)
  have h_dim : finrank (ResField w) p.ker = j :=
    Nat.succ_injective ((p.finrank_ker_add_one_of_ne_zero hp_ne).trans h_dim_L)
  -- The vectors counted form the fibre of `p` over `1`, a translate of the kernel.
  have h_mem (u : L) : u.val ∈ echelonRows r ↔ u.val r = 1 :=
    (mem_echelonRows r).trans (and_iff_left (h_low u u.prop))
  have h_fibre : Nat.card (p.toAddMonoidHom ⁻¹' {1}) = w.q ^ j := by
    rw [Nat.card_congr (p.toAddMonoidHom.fiberEquivKerOfSurjective (p.surjective hp_ne) 1)]
    exact (natCard_eq_pow_finrank (K := ResField w) (V := p.ker)).trans
      (by rw [card_ResField, h_dim])
  -- `erw`: the count of the filter is that of the fibre of `p` over `1` only up to unfolding
  -- `p` and the coercions of `L`.
  erw [← card_subtype, ← Nat.subtype_card _ (p := fun u ↦ u.val r = 1) (by simpa using h_mem),
    h_fibre]

/-- If `x` is fixed by `GL_N(𝒪)` (`hx`), then `partialHecke ρ m j x` is fixed by the parahoric
subgroup whose blocks are given by the level function `i ↦ i + 1 - m` (truncated subtraction). -/
lemma partialHecke_mem_levelSpace {x : V} (hx : x ∈ levelSpace ρ (localIntGL (Fin N) w)) :
    partialHecke ρ m j x ∈ levelSpace ρ (blockParahoric fun i : ℕ ↦ i + 1 - m) := by
  classical
  simp_all [partialHecke, heckeFun_mem_levelSpace hasFiniteCosets_partialCosets, Set.indicator]

/-- Every lattice of colength `0` is `𝒪^N` and contains all basis vectors, so
`partialHecke ρ m 0` fixes a vector `x` fixed by `GL_N(𝒪)`. -/
lemma partialHecke_zero_right {x : V} (hx : x ∈ levelSpace ρ (localIntGL (Fin N) w)) :
    partialHecke ρ m 0 x = x := by
  -- Every `g ∈ basicDoubleCoset (Fin N) w 0` is integral with unit determinant, so `g⁻¹` is
  -- integral too.
  have h_cosets : partialCosets m 0 = basicDoubleCoset (Fin N) w 0 :=
    Set.sep_eq_self_iff_mem_true.mpr fun g ⟨hg_int, _, hg_det⟩ b a _ ↦
      (mem_intGL_iff_det.mpr ⟨hg_int, hg_det⟩).isIntMatrix_inv a b
  rw [partialHecke, h_cosets]
  exact heckeGL_zero hx

/-- Let `b` be diagonal with `ϖ` at `r` and `1` elsewhere, and for each row
`u = (0, …, 0, 1, *, …, *)` let `n u ∈ proIwahori` have row `r` equal to `u` modulo the maximal
ideal. Then the sum over these `u` of the indicator of `partialCosets (r + 1) j` at
`((n u)⁻¹ * b)⁻¹ * g` is `q ^ j` times the indicator of `partialCosets r (j + 1)` minus that of
`partialCosets (r + 1) (j + 1)`, at `g`. -/
private lemma sum_echelonRows_indicator_partialCosets_eq (hϖ : v ϖ.val = exp (-1)) (r : Fin N)
    {n : (Fin N → ResField w) → GL (Fin N) (LocField w)}
    (hn_mem : ∀ u : Fin N → ResField w, n u ∈ proIwahori)
    (hn_row : ∀ u ∈ echelonRows r, (n u).val.map residueOrZero r = u)
    (g : GL (Fin N) (LocField w)) :
    ∑ u ∈ echelonRows r,
        (partialCosets (r + 1) j).indicator 1 (((n u)⁻¹ * diagGL (mulSingle r ϖ))⁻¹ * g) =
      (w.q ^ j : ℂ) * ((partialCosets r (j + 1)).indicator 1 g -
        (partialCosets (r + 1) (j + 1)).indicator 1 g) := by
  classical
  set b : GL (Fin N) (LocField w) := diagGL (mulSingle r ϖ)
  have h_shift (g' : GL (Fin N) (LocField w)) : b⁻¹ * g' ∈ partialCosets (r + 1) j ↔
      g' ∈ partialCosets r (j + 1) ∧ g'.val.map residueOrZero r = 0 :=
    inv_mul_mem_partialCosets_iff hϖ r g'
  have hn_fix (u : Fin N → ResField w) :
      n u * g ∈ partialCosets r (j + 1) ↔ g ∈ partialCosets r (j + 1) :=
    mul_mem_partialCosets_iff.left (proIwahori_le_blockParahoric (by lia) (hn_mem u))
  by_cases hg : g ∈ partialCosets r (j + 1)
  · -- `g` is integral, as a member of `basicDoubleCoset`.
    obtain ⟨hg_int, -, -⟩ : g ∈ basicDoubleCoset (Fin N) w (j + 1) := Set.sep_subset _ _ hg
    have h_kills (u : Fin N → ResField w) (hu : u ∈ echelonRows r) :
        (n u * g).val.map residueOrZero r = 0 ↔ u ∈ residueKer (transposeGL g).val := by
      simp [map_residueOrZero_mul (hn_mem u).1.isIntMatrix hg_int, mul_apply_eq_vecMul,
        transpose_map, hn_row u hu]
    simp only [_root_.mul_inv_rev, inv_inv, mul_assoc, Set.indicator, h_shift, hn_fix, hg,
      true_and, Pi.one_apply, sum_boole, filter_congr h_kills,
      card_echelonRows_mem_residueKer r hg]
    split_ifs <;> simp
  · have hg_succ : g ∉ partialCosets (r + 1) (j + 1) := fun ⟨h_basic, h_cols⟩ ↦
      hg ⟨h_basic, fun c a hc ↦ h_cols c a (hc.trans (Nat.lt_succ_self r))⟩
    simp [mul_assoc, h_shift, hn_fix, hg, hg_succ]

/-- The count of hyperplanes. Let `ϖ` be a uniformiser (`v ϖ = exp (-1)`), `q = w.q`, `x` a vector
fixed by `GL_N(𝒪_w)` (`localIntGL`), and `T r j = partialHecke ρ r j`, the sum of `ρ g` over the
cosets in `partialCosets r j`. Let `b` be diagonal with `ϖ` at the index `r` (counted from `0`) and
`1` elsewhere, and let the linear map `ψ` be invariant under `ρ k` for every `k` in the pro-`p`
Iwahori subgroup `proIwahori` whose off-diagonal entries vanish outside row `r`. Then
`q ^ (N - 1 - r) ψ (ρ b (T (r + 1) j x)) = ψ (q ^ j (T r (j + 1) x - T (r + 1) (j + 1) x))`. -/
lemma partialHecke_hyperplane_count_of_invariant (hϖ : v ϖ.val = exp (-1)) {x : V}
    (hx : x ∈ levelSpace ρ (localIntGL (Fin N) w)) (r : Fin N) {W : Type*} [AddCommGroup W]
    [Module ℂ W] {ψ : V →ₗ[ℂ] W}
    (hψ : ∀ k ∈ proIwahori, (∀ i ≠ r, ∀ l ≠ i, k.val i l = 0) → ∀ z : V, ψ (ρ k z) = ψ z) (j : ℕ) :
    (w.q ^ r.rev.val : ℂ) • ψ (ρ (diagGL (mulSingle r ϖ)) (partialHecke ρ (r + 1) j x)) =
      ψ ((w.q : ℂ) ^ j • (partialHecke ρ r (j + 1) x - partialHecke ρ (r + 1) (j + 1) x)) := by
  classical
  -- Write `q ^ (N - 1 - r) • ψ ∘ ρ b` as `ψ ∘ ∑ u, ρ ((n u)⁻¹ * b)`, where `n u ∈ proIwahori` has
  -- row `r` congruent to `u = (0, …, 0, 1, *, …, *)` and the other rows of `1`. In this sum a
  -- lattice of `partialCosets r (j + 1)` occurs once for each `u` that kills it modulo `ϖ`: never
  -- if it contains the basis vector `r`, and `q ^ j` times otherwise.
  set b : GL (Fin N) (LocField w) := diagGL (mulSingle r ϖ)
  -- `M u` is the identity matrix with row `r` replaced by representatives of `u` right of `r`.
  let M (u : Fin N → ResField w) : Matrix (Fin N) (Fin N) (LocField w) :=
    of fun i k ↦ (if k ≤ i ∨ i ≠ r then diagonal 1 i k else (u k).out : LocInt w).val
  have hM_tri (u : Fin N → ResField w) :
      (∀ i k : Fin N, k < i → v (M u i k) < 1) ∧ ∀ i : Fin N, v (M u i i - 1) < 1 := by
    simp_all [M, le_of_lt, ne_of_gt]
  have h_lift (u : Fin N → ResField w) : ∃ g ∈ proIwahori, g.val = M u :=
    exists_proIwahori_coe_eq (M u)
      (fun i k ↦ (if k ≤ i ∨ i ≠ r then diagonal 1 i k else (u k).out : LocInt w).2) (hM_tri u)
  choose n hn_mem hn_val using h_lift
  have hn_row (u : Fin N → ResField w) (hu : u ∈ echelonRows r) :
      (n u).val.map residueOrZero r = u := by
    obtain ⟨h_one, h_zero⟩ := (mem_echelonRows r).mp hu
    ext i
    simp only [hn_val, M, Matrix.map_apply, of_apply, residueOrZero_coe]
    split
    · have hi : u i = if r = i then 1 else 0 := by grind
      simp [hi, apply_ite (IsLocalRing.residue _), diagonal_apply]
    · exact (u i).out_eq
  have hψ_inv (u : Fin N → ResField w) (z : V) : ψ (ρ (n u)⁻¹ z) = ψ z := by
    have h_diag : ∀ i ≠ r, ∀ l ≠ i, (n u).val i l = 0 := by
      simp +contextual [hn_val, M, eq_comm]
    simpa using (hψ (n u) (hn_mem u) h_diag (ρ (n u)⁻¹ z)).symm
  -- The coefficient of the coset of `g` on the two sides.
  have h_coeff (g : GL (Fin N) (LocField w)) :
      ∑ u ∈ echelonRows r, (partialCosets (r + 1) j).indicator 1 (((n u)⁻¹ * b)⁻¹ * g) =
        (w.q ^ j : ℂ) * ((partialCosets r (j + 1)).indicator 1 g -
          (partialCosets (r + 1) (j + 1)).indicator 1 g) :=
    sum_echelonRows_indicator_partialCosets_eq hϖ r hn_mem hn_row g
  -- `ρ y` turns the operator of a function `f` into that of `g ↦ f (y⁻¹ * g)`.
  have h_translate (y : GL (Fin N) (LocField w)) :
      heckeFun ρ (localIntGL (Fin N) w) (fun g ↦ (partialCosets (r + 1) j).indicator 1 (y⁻¹ * g)) x
        =
        ρ y (heckeFun ρ (localIntGL (Fin N) w) ((partialCosets (r + 1) j).indicator 1) x) :=
    heckeFun_comp_inv_mul hasFiniteCosets_partialCosets (by simp [Set.indicator]) hx y
  have h_finite (y : GL (Fin N) (LocField w)) : HasFiniteCosets (localIntGL (Fin N) w)
      (fun g ↦ (partialCosets (r + 1) j).indicator (1 : GL (Fin N) (LocField w) → ℂ) (y⁻¹ * g)) :=
    hasFiniteCosets_partialCosets.comp_inv_mul (by simp [Set.indicator]) y
  have h_sum : ∑ u ∈ echelonRows r, ρ ((n u)⁻¹ * b) (partialHecke ρ (r + 1) j x) =
      (w.q : ℂ) ^ j • (partialHecke ρ r (j + 1) x - partialHecke ρ (r + 1) (j + 1) x) := by
    -- Write both sides as sums over cosets and compare coefficients.
    unfold partialHecke
    -- Each `ρ ((n u)⁻¹ * b)` moves into the operator, as a left translate of the function.
    simp only [← h_translate]
    -- Both sides become one sum over cosets, each term a coefficient times `ρ g`.
    simp only [heckeFun, ← LinearMap.sum_apply, ← LinearMap.sub_apply,
      ← LinearMap.smul_apply, ← finsum_sum_comm, smul_finsum, ← finsum_sub_distrib,
      fun_smul_left hasFiniteCosets_partialCosets, fun_smul_left (h_finite _), implies_true,
      ← sum_smul]
    congr with g
    rw [h_coeff, mul_smul, sub_smul]
  -- `ψ` does not see `(n u)⁻¹`, and there are `q ^ (N - 1 - r)` rows `u`.
  rw [← h_sum]
  simp [hψ_inv, card_echelonRows, ← Nat.cast_smul_eq_nsmul ℂ]

/-! ### The hyperplane count, Satake's formula and the duality of lattices -/

/-- The count of hyperplanes of `partialHecke_hyperplane_count_of_invariant`, for `ψ` invariant
under `ρ k⁻¹` whenever `k⁻¹ ∈ proIwahori` and `k` has no off-diagonal entry outside row `r`. Write
`T r j` for `partialHecke ρ r j` and `b` for the diagonal matrix with `ϖ` at `r` and `1` elsewhere:
`q ^ (N - 1 - r) ψ (ρ b (T (r + 1) j x)) = ψ (q ^ j (T r (j + 1) x - T (r + 1) (j + 1) x))`. -/
lemma partialHecke_hyperplane_count (hϖ : v ϖ.val = exp (-1)) {x : V}
    (hx : x ∈ levelSpace ρ (localIntGL (Fin N) w)) (r : Fin N) {W : Type*} [AddCommGroup W]
    [Module ℂ W] {ψ : V →ₗ[ℂ] W}
    (hψ : ∀ k : GL (Fin N) (LocField w), (∀ i ≠ r, ∀ l ≠ i, k.val i l = 0) →
      k⁻¹ ∈ proIwahori → ∀ z : V, ψ (ρ k⁻¹ z) = ψ z)
    (j : ℕ) :
    (w.q ^ r.rev.val : ℂ) • ψ (ρ (diagGL (mulSingle r ϖ)) (partialHecke ρ (r + 1) j x)) =
      ψ ((w.q : ℂ) ^ j • (partialHecke ρ r (j + 1) x - partialHecke ρ (r + 1) (j + 1) x)) := by
  refine partialHecke_hyperplane_count_of_invariant hϖ hx r (fun k hk h_diag z ↦ ?_) j
  -- apply the invariance to `k⁻¹ ∈ proIwahori` and the vector `ρ k z`
  simpa using (hψ k h_diag (inv_mem hk) (ρ k z)).symm

open Multiset in
/-- Satake's formula, in stages. Let `ρ` be a smooth representation of `GL_N` over the completion at
`w`, `ϖ` a uniformiser (`v ϖ = exp (-1)`), `q = w.q`, `x` fixed by `GL_N(𝒪_w)` (`localIntGL`),
`r ≤ N`, and `l` an exponent (`New.IsExponent`) for the torus character `New.torusChar θ`; put
`y i = θ i ϖ`. Then `l (partialHecke ρ r j x)` (the sum of `ρ g` over the cosets in
`partialCosets r j`) is `e_j (y r, …, y (N - 1)) / q ^ (j (j - 1) / 2)` times `l x`, with `e_j` the
elementary symmetric function. The case `r = 0` is Satake's formula for the `j`-th Hecke operator of
`GL_N`. -/
lemma IsExponent.apply_partialHecke (hϖ : v ϖ.val = exp (-1)) {x : V}
    (hx : x ∈ levelSpace ρ (localIntGL (Fin N) w)) [IsSmoothRep ρ] {θ : Fin N → (LocField w)ˣ →* ℂˣ}
    {l : Rep.of ρ →ₗ[ℂ] ℂ} (hl : IsExponent (Rep.of ρ) (torusChar θ) l) {r : ℕ} (hr_le : r ≤ N) :
    ∀ j : ℕ, l (partialHecke ρ r j x) =
      esymm ((List.ofFn fun i : Fin N ↦ (θ i ϖ).val).drop r) j / w.q ^ j.choose 2 * l x := by
  -- Descend in `r` from `r = N`. The count of hyperplanes for `ψ = l` becomes the
  -- recursion `e_{j+1}(y_r, …) = e_{j+1}(y_{r+1}, …) + y_r e_j(y_{r+1}, …)`.
  intro j
  induction hr_le using Nat.decreasingInduction generalizing j with
  | self => cases j <;> simp [partialHecke_zero_right hx, esymm]
  | of_succ r hr ih =>
    obtain _ | j := j
    · simp [partialHecke_zero_right hx, esymm]
    have hq : (w.q : ℂ) ≠ 0 := by grind [Nat.cast_ne_zero, w.q_bounds]
    set t : Fin N → (LocField w)ˣ := mulSingle ⟨r, hr⟩ ϖ
    -- the valuations of the entries of `t`, against the levels `i + 1 - (r + 1)` of the
    -- parahoric subgroup that fixes `partialHecke ρ (r + 1) j x`
    have h_levels : ∀ a b : Fin N, b < a → v (t b).val ≤ v (t a).val ∨
        a.val + 1 - (r + 1) ≤ b.val + 1 - (r + 1) ∧ v (t b).val ≤ v (t a).val * exp 1 := by
      simp_all +decide [t, apply_ite, mulSingle_apply, ite_apply]
      lia
    -- the eigenvalue of the diagonal matrix with `ϖ` at `r`, on a vector fixed by the parahoric
    have h_eigen : l (ρ (diagGL t) (partialHecke ρ (r + 1) j x)) =
        θ ⟨r, hr⟩ ϖ / w.q ^ (N - (r + 1)) * l (partialHecke ρ (r + 1) j x) := by
      simpa [t, coe_normAbsChar_locField, norm_locField_eq_q_zpow, hϖ, div_eq_mul_inv] using
        hl.apply_monomial_translate hϖ (partialHecke_mem_levelSpace hx (m := r + 1) (j := j))
          And.left 1 h_levels
    -- divide the count of hyperplanes by `q ^ j`; the factors `q ^ (N - (r + 1))` cancel
    have h_rec : l (partialHecke ρ r (j + 1) x) = l (partialHecke ρ (r + 1) (j + 1) x) +
        θ ⟨r, hr⟩ ϖ / w.q ^ j * l (partialHecke ρ (r + 1) j x) := by
      have h_count : (w.q ^ (N - (r + 1)) : ℂ) • l (ρ (diagGL t) (partialHecke ρ (r + 1) j x)) =
          l ((w.q : ℂ) ^ j • (partialHecke ρ r (j + 1) x - partialHecke ρ (r + 1) (j + 1) x)) :=
        partialHecke_hyperplane_count_of_invariant hϖ hx ⟨r, hr⟩
          (fun k hk _ ↦ hl.apply_proIwahori k hk) j
      grind [pow_ne_zero, smul_eq_mul, map_smul]
    rw [h_rec, ih, ih, List.drop_eq_getElem_cons (i := r) (by simpa using hr)]
    -- `e_{j+1}(y_r ::ₘ s) = e_{j+1}(s) + y_r e_j(s)` and `(j + 1).choose 2 = j.choose 2 + j`
    simp [esymm, sum_map_mul_left, Nat.choose, ← cons_coe, pow_add, field]

/-- Duality of lattices. Let `ϖ` be a uniformiser, `x` a vector fixed by `GL N (𝒪)`, and
`m + i + j = N`. The operator `partialHecke _ m j` of the representation `g ↦ ρ (gᵀ)⁻¹` sends `x`
to `partialHecke ρ m i x` followed by the diagonal matrix with `m` entries `1` and then `ϖ⁻¹`. -/
lemma partialHecke_dual (hϖ : v ϖ.val = exp (-1)) {m : ℕ} {x : V}
    (hx : x ∈ levelSpace ρ (localIntGL (Fin N) w)) (i : ℕ) (h_sum : m + (i + j) = N) :
    partialHecke (ρ.comp invTransposeGL.toMonoidHom) m j x =
      ρ (diagGL fun a : Fin N ↦ if a.val < m then 1 else ϖ⁻¹) (partialHecke ρ m i x) := by
  classical
  set c := diagGL fun a : Fin N ↦ if a.val < m then 1 else ϖ⁻¹
  -- `g ↦ c⁻¹ * invTransposeGL g` matches the cosets of `partialCosets m j` with those of
  -- `partialCosets m i`: both conditions unfold to the same bounds on the entries of `g`, `g⁻¹` and
  -- the same valuation of `det g`.
  have dual (g : GL (Fin N) (LocField w)) :
      g ∈ partialCosets m j ↔ c⁻¹ * invTransposeGL g ∈ partialCosets m i := by
    subst h_sum
    have h_det : v g.val.det ≠ 0 := by simp [g.det_ne_zero]
    simp [c, invTransposeGL, partialCosets, basicDoubleCoset, diagGL, apply_ite, hϖ,
      Fin.prod_univ_add, field, ← g⁻¹.val_det_apply, transposeGL, ite_apply, -coe_units_inv]
    grind [le_of_lt, lt_mul_exp_iff_le one_ne_zero]
  -- The two side conditions of `heckeFun_comp` are the right invariance of the translated
  -- indicator and `dual` read on indicators.
  calc
    _ = heckeFun ρ (localIntGL (Fin N) w) (fun g ↦ (partialCosets m i).indicator 1 (c⁻¹ * g)) x :=
      heckeFun_comp _ (by simp [← mul_assoc, Set.indicator]) hx hasFiniteCosets_partialCosets
        invTransposeGL.surjective invTransposeGL_mem_intGL (fun _ ↦ rfl)
        (by simp [dual, Set.indicator_apply])
    _ = _ := heckeFun_comp_inv_mul hasFiniteCosets_partialCosets (by simp [Set.indicator]) hx c

end New

end HeckeCounts

end
