import New.Spanning.Frames.Lengths

/-!
# Comparing the lengths at two points; minors and heads

Each isometry g of the form `T.splitGram` gives a gauge, the size of g⁻¹ y, on vectors y. The
gauges at two points differ little on Y^(l-1) if they differ little on Y^(l), the frame vector
e_(l-1) has short lifts at both points, and it has a short dual that looks nearly the same from both
points. Over a head, such duals come from determinants of blocks of the isometries (Cramer's rule).

Notions from other files:
* `S.ofSize i`, `S.vecsOfSize i`, `S.HasMatrixSize i`: the numbers x of size i (|x| ≤ L^i at a real
  place, L^i x integral at the finite places, for a fixed scale L), and the vectors and matrices all
  of whose entries have size i.
* Y^(l): the vectors orthogonal to e_0, …, e_(l-1) (`IsOrthogonalBelow l`) modulo the span of these
  (`CongrBelow l`). The basis vectors e_a and e*_a have the indices `inl a` and `eStar a`.
* `S.GaugesDifferLe r g g' l t`: for each ω orthogonal to e_0, …, e_(l-1) with g⁻¹ ω of size i, the
  class of ω in Y^(l) has a lift ω' such that (g⁻¹ ω - g'⁻¹ ω') / r has size i + t.
* R^(l) = `partialUnitriangularGroup l`: the isometries that change each frame vector of index below
  l by a combination of the earlier ones. U_(<l) = `unipotentBelow l`: the isometries that are
  unitriangular when all basis vectors other than e_a, e*_a (a < l) are put on one middle level.
* `S.IsHead j p`: the inverses of the products p₀ ⋯ p_(l-1), l ≤ j, have size 1. The Weyl element
  w_p = `weylElem j p` sends e_a to p_a e*_a for a < j.

## Main definitions and results

* `New.Floors.Size.GaugesDifferLe.of_succ`,
  `New.Floors.Size.GaugesDifferLe.on_whole_space_of_hasShortDual`: the recursion down the quotients.
* `New.Floors.Size.GaugesDifferLe.hasMatrixSize_sub_one`: a bound on the whole space bounds the
  matrix `(x - 1) / r`.
* `New.Floors.Size.leadingMinor_mem_ofSize`, `New.Floors.Size.head_products_mem_ofSize`: the leading
  minors have bounded size.
* `New.Floors.Size.dual_mem_vecsOfSize`, `New.Floors.Size.hasMatrixSize_of_isHead`: short duals over
  a head, and bounds for the sizes of g and w_p⁻¹ g.

## Relation to the literature

See `New.Spanning.MainTerm.EnergyEstimate` for related work.
-/

noncomputable section

namespace New.Floors

section Size

open Matrix BesselIndex Sum Fintype FloorGroups Finset Fin

variable {A : Type} [CommRing A] [StarRing A] {𝔰 : Shape} {T : 𝔰.Form A}

variable {c i j : ℕ} [IsHermitianUnit T.splitGram] {s g x : T.G} {a : Fin 𝔰.ϱ} {p : ℕ → Aˣ}
  {r : Aˣ} {S : Size T}

namespace Size

/-- Let the isometries `ξ` and `ξ'` change each frame vector of index below `l` by a combination of
the earlier ones (`partialUnitriangularGroup l`). If all entries of `ξ g` and `ξ' γ⁻¹ g` have size 1
(size i: in `S.ofSize i`), then the leading minors of order `j ≤ l` of `T.frameGram γ`, the matrix
of the products ⟨f_a, γ f_b⟩ of the `𝔰.n = ϱ + 1` frame vectors f_a, have size `9 * 𝔰.n`. -/
theorem leadingMinor_mem_ofSize {l : ℕ} {γ g ξ ξ' : T.G} (hξ : ξ ∈ partialUnitriangularGroup l)
    (hξ' : ξ' ∈ partialUnitriangularGroup l)
    (hg : S.HasMatrixSize 1 (↑(ξ * g) : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A))
    (hγg : S.HasMatrixSize 1 (↑(ξ' * (γ⁻¹ * g)) : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A))
    {j : Fin (𝔰.n + 1)} (hj : j.val ≤ l) :
    leadingMinor (T.frameGram γ) j ∈ S.ofSize (9 * 𝔰.n) := by
  -- The element `x = (ξ g) (ξ' γ⁻¹ g)⁻¹ = ξ γ ξ'⁻¹` has size 7, and `T.frameGram x` has the same
  -- leading minors of order at most `l` as `T.frameGram γ`.
  let x : T.G := ξ * g * (ξ' * (γ⁻¹ * g))⁻¹
  let X : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A := x
  have h_size : S.HasMatrixSize 7 X := hg.mul hγg.inv
  have h_minor : leadingMinor (T.frameGram γ) j = leadingMinor (T.frameGram X) j := by
    have hx : ξ⁻¹ * x * ξ' = γ := by simp [x, mul_assoc]
    rw [← leadingMinor_frameGram_partialUnitriangularGroup_mul hξ hξ' x hj, hx]
  -- In `J x`, with `J = T.splitGram`, the row of `e_a` is the row of `e*_a` in `x`.
  have h_row (i k : 𝔰.BesselIndex) (hi : floorOf i < 𝔰.ϱ) :
      (T.splitGram * X) i k = X (oppositeIndex i) k :=
    splitGram_mulVec_apply (e := fun m ↦ X m k) i hi
  have h_all : S.HasMatrixSize 9 (T.splitGram * X) := hasMatrixSize_splitGram.mul h_size
  rw [h_minor, leadingMinor]
  obtain ⟨_ | j, hj_lt⟩ := j
  · rw [det_isEmpty]
    exact (S.zero_one_mem_ofSize _).right
  -- All rows of the minor but the last belong to vectors `e_a`, `a < ϱ`.
  have hj_le : j ≤ 𝔰.ϱ := by lia
  refine mem_ofSize_mono (i := 9 * (j + 1)) ?_ (by lia)
  refine det_mem_ofSize_of_last_row _ hj_le (fun a b ↦ ?_) fun b ↦ h_all _ _
  rw [submatrix_apply, submatrix_apply, frameGram, submatrix_apply,
    h_row _ _ (floorOf_besselFrame.trans_lt (a.is_lt.trans_le hj_le))]
  exact h_size _ _

omit [IsHermitianUnit T.splitGram] in
/-- Let g, g' be isometries and r a self-adjoint unit of size 1. Write Y^(l) for the vectors
orthogonal to e_0, …, e_(l-1) modulo the span of these. Assume that the class of
e_a = `Pi.single (inl a) 1` in Y^(a) has lifts f, f' with g⁻¹ f and g'⁻¹ f' of size c. Assume also
that e_a has a short dual ζ in Y^(a): ⟨e_a, ζ⟩ = 1, and g⁻¹ ζ and (g⁻¹ ζ - g'⁻¹ ζ') / r have size c
for some lift ζ' of ζ. Suppose the lengths at g and g' differ by at most L^t modulo r on Y^(a+1):
each class [ω] with g⁻¹ ω of size i has a lift ω' with (g⁻¹ ω - g'⁻¹ ω') / r of size i + t. Then
they differ by at most L^(t + 4 c + 12) modulo r on Y^(a). -/
lemma GaugesDifferLe.of_succ {g' : T.G} {t : ℕ} (hr_star : star r.val = r)
    (hr_size : ↑r ∈ S.ofSize 1) (hg : S.InducedLengthLe g a c (Pi.single (inl a) 1))
    (hg' : S.InducedLengthLe g' a c (Pi.single (inl a) 1)) (h_dual : S.HasShortDual r g g' a c)
    (h : S.GaugesDifferLe r g g' (a + 1) t) : S.GaugesDifferLe r g g' a (t + (4 * c + 12)) := by
  -- Write ω = α ζ + ω₀ with α = ⟨e_a, ω⟩, so that ω₀ is orthogonal to e_a. The class of ω₀ in
  -- Y^(a+1) has a lift ω₀' with g'⁻¹ ω₀' close to g⁻¹ ω₀ modulo r. Pairing with the dual ζ bounds
  -- μ / r, where μ is the coefficient of e_a in ω₀' - ω₀, and α ζ' + ω₀' - μ f' is the lift of ω,
  -- where f' is the short lift of e_a at g'.
  intro i ω hω hω_len
  obtain ⟨f, hf, hf_len⟩ : ∃ f, CongrBelow a (Pi.single (inl a) 1) f ∧ S.LengthLeAt g c f := hg
  obtain ⟨f', hf', hf'_len⟩ :
      ∃ f', CongrBelow a (Pi.single (inl a) 1) f' ∧ S.LengthLeAt g' c f' := hg'
  obtain ⟨ζ, hζ, hζ_one, hζ_len, ζ', hζ', hζ_agree⟩ : ∃ ζ, IsOrthogonalBelow a ζ ∧ ζ (eStar a) = 1 ∧
      S.LengthLeAt g c ζ ∧ S.AgreesModulo r g g' a c ζ := h_dual
  set α : A := ω (eStar a) with hα
  have hα_size : α ∈ S.ofSize (c + i + 3) := by
    have h_form : star (g⁻¹.val.val *ᵥ f) ⬝ᵥ T.splitGram *ᵥ g⁻¹.val.val *ᵥ ω = α := by
      rw [U.form_mulVec_mulVec, hf.form_eq_left hω a.is_lt.le]
      simp [hα]
    rw [← h_form]
    exact form_mem_ofSize hf_len hω_len
  set ω₀ : 𝔰.BesselIndex → A := ω - α • ζ with hω₀
  have hω₀_orth : IsOrthogonalBelow (a + 1) ω₀ := fun b hb ↦ by
    obtain hb | hb := Nat.lt_succ_iff_lt_or_eq.1 hb
    · simp [hω₀, hω b hb, hζ b hb]
    · simp [hω₀, hα, Fin.ext hb, hζ_one]
  have hω₀_len : S.LengthLeAt g (c + i + 3 + c + 1) ω₀ := by
    simpa only [LengthLeAt, hω₀, mulVec_sub, mulVec_smul] using
      sub_mem_vecsOfSize (mem_vecsOfSize_mono hω_len) (smul_mem_vecsOfSize hα_size hζ_len)
  obtain ⟨ω₀', hω₀', hω₀_agree⟩ : S.AgreesModulo r g g' (a + 1) (c + i + 3 + c + 1 + t) ω₀ :=
    h _ ω₀ hω₀_orth hω₀_len
  set μ : A := ω₀' (inl a) - ω₀ (inl a) with hμ
  have hμ_size : r⁻¹.val * μ ∈ S.ofSize (c + (c + i + 3 + c + 1 + t) + 6) := by
    rw [hμ, ← hω₀'.form_sub_form (T := T) hω₀_orth hζ hζ_one hζ', ← U.form_mulVec_mulVec g'⁻¹,
      ← U.form_mulVec_mulVec g⁻¹ ζ]
    exact form_sub_form_mem_ofSize hr_star hr_size hζ_len hζ_agree (mem_vecsOfSize_mono hω₀_len)
      hω₀_agree
  refine ⟨α • ζ' + (ω₀' - μ • f'), fun k hk ↦ ?_, ?_⟩
  · rw [Pi.add_apply, hω₀'.sub_smul hf' k hk]
    simp [hω₀, hζ' k hk]
  · set M : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A := g⁻¹.val.val
    set M' : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A := g'⁻¹.val.val
    have h_terms : r⁻¹.val • (M *ᵥ ω - M' *ᵥ (α • ζ' + (ω₀' - μ • f'))) =
        r⁻¹.val • (M *ᵥ ω₀ - M' *ᵥ ω₀') -
          (-α • r⁻¹.val • (M *ᵥ ζ - M' *ᵥ ζ') - (r⁻¹.val * μ) • M' *ᵥ f') := by
      simp only [hω₀, mulVec_add, mulVec_sub, mulVec_smul]
      module
    have h_dual_term : -α • r⁻¹.val • (M *ᵥ ζ - M' *ᵥ ζ') ∈ S.vecsOfSize (c + i + 3 + c) :=
      smul_mem_vecsOfSize (neg_mem_ofSize hα_size) hζ_agree
    have h_frame_term :
        (r⁻¹.val * μ) • M' *ᵥ f' ∈ S.vecsOfSize (c + (c + i + 3 + c + 1 + t) + 6 + c) :=
      smul_mem_vecsOfSize hμ_size hf'_len
    rw [h_terms]
    exact mem_vecsOfSize_mono (sub_mem_vecsOfSize (mem_vecsOfSize_mono hω₀_agree)
      (sub_mem_vecsOfSize (mem_vecsOfSize_mono h_dual_term) h_frame_term))

omit [IsHermitianUnit T.splitGram] in
/-- Let g, g' be isometries, r a self-adjoint unit of size 1 and j ≤ ϱ. For each a < j, let the
class of e_a = `Pi.single (inl a) 1` in Y^(a) have lifts f, f' with g⁻¹ f and g'⁻¹ f' of size c. Let
e_a also have a short dual ζ in Y^(a): ⟨e_a, ζ⟩ = 1, and g⁻¹ ζ and (g⁻¹ ζ - g'⁻¹ ζ') / r have size c
for some lift ζ' of ζ. Suppose the lengths at g and g' differ by at most L^t modulo r on Y^(j): each
class [ω] with g⁻¹ ω of size i has a lift ω' with (g⁻¹ ω - g'⁻¹ ω') / r of size i + t. Then they
differ by at most L^(t + (4 c + 12) j) modulo r on Y^(0), the whole space. -/
lemma GaugesDifferLe.on_whole_space_of_hasShortDual {g' : T.G} {t : ℕ} (hr_star : star r.val = r)
    (hr_size : ↑r ∈ S.ofSize 1) (hj : j ≤ 𝔰.ϱ)
    (hg : ∀ a : Fin 𝔰.ϱ, a.val < j → S.InducedLengthLe g a c (Pi.single (inl a) 1))
    (hg' : ∀ a : Fin 𝔰.ϱ, a.val < j → S.InducedLengthLe g' a c (Pi.single (inl a) 1))
    (h_dual : ∀ a : Fin 𝔰.ϱ, a.val < j → S.HasShortDual r g g' a c)
    (h : S.GaugesDifferLe r g g' j t) : S.GaugesDifferLe r g g' 0 (t + (4 * c + 12) * j) := by
  induction j generalizing t with
  | zero => simpa using h
  | succ j ih =>
    lift j to Fin 𝔰.ϱ using hj
    have hj_lt : j.val < j.val + 1 := j.val.lt_succ_self
    have h_step : S.GaugesDifferLe r g g' j (t + (4 * c + 12)) :=
      h.of_succ hr_star hr_size (hg j hj_lt) (hg' j hj_lt) (h_dual j hj_lt)
    rw [show t + (4 * c + 12) * (j.val + 1) = t + (4 * c + 12) + (4 * c + 12) * j.val by ring]
    exact ih j.is_lt.le (fun a ha ↦ hg a (ha.trans hj_lt)) (fun a ha ↦ hg' a (ha.trans hj_lt))
      (fun a ha ↦ h_dual a (ha.trans hj_lt)) h_step

/-- Let g, x be isometries and r a unit with star r = r. Suppose `S.GaugesDifferLe r g (g * x) 0 i`:
the lengths at g and g x differ by at most L^i modulo r on the whole space. Then r⁻¹ • (x - 1) has
size i + 4. Size i means entries in `S.ofSize i`, for the scale L of `S`. -/
lemma GaugesDifferLe.hasMatrixSize_sub_one (hr_star : star r.val = r)
    (h : S.GaugesDifferLe r g (g * x) 0 i) :
    S.HasMatrixSize (i + 4) (r⁻¹.val • ((x : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A) - 1)) := by
  -- On the whole space a class has one lift, so the columns of g give those of (1 - x⁻¹) / r. The
  -- matrix (x - 1) / r is the adjoint, for the form, of N = (x⁻¹ - 1) / r.
  set N : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A := r⁻¹.val • (x⁻¹.val.val - 1) with hN
  have h_col (k n : 𝔰.BesselIndex) : N n k ∈ S.ofSize i := by
    set ω : 𝔰.BesselIndex → A := g.val.val *ᵥ Pi.single k 1 with hω
    have hω_len : S.LengthLeAt g 0 ω := lengthLeAt_mulVec_iff.mpr (single_mem_vecsOfSize k)
    obtain ⟨ω', h_congr, h_agree⟩ : S.AgreesModulo r g (g * x) 0 (0 + i) ω :=
      h 0 ω (fun b hb ↦ absurd hb b.val.not_lt_zero) hω_len
    obtain rfl : ω = ω' := funext fun m ↦ (h_congr m (Nat.zero_le _)).symm
    have h_entry : N n k = -(r⁻¹.val • (g⁻¹.val.val *ᵥ ω - (g * x)⁻¹.val.val *ᵥ ω)) n := by
      simp only [hN, hω, mulVec_mulVec]
      simp [mul_sub, Matrix.mul_assoc]
    rw [h_entry, ← zero_add i]
    exact neg_mem_ofSize (h_agree n)
  have h_adj : T.splitGram * (r⁻¹.val • (x.val.val - 1)) = Nᴴ * T.splitGram := by
    have h_inv : T.splitGram * x.val.val = x⁻¹.val.valᴴ * T.splitGram := by
      simpa only [inv_inv] using U.form_mul_inv_eq x⁻¹
    simp [hN, hr_star, ← inverse_star_unit, h_inv, mul_sub, Matrix.sub_mul]
  exact fun a b ↦ adjoint_apply_mem_ofSize h_adj a b fun n _ k ↦ h_col k n

/-- A bound by Cramer's rule. Let K be a set of isometries of the form (elements of `T.G`) whose
entries all have size 1, and let a < j ≤ ϱ, where ϱ is the number of hyperbolic pairs e_b, e*_b. Let
s ∈ R^(j) with s g ∈ K, and let η w_p⁻¹ g ∈ K for some η ∈ R^(j). Then p₀ ⋯ p_a times the i-th entry
of the column s e*_a has size 8 ϱ. -/
lemma head_prod_mul_dual_mem_ofSize {S : Size T} {K : Set T.G} {j : ℕ} {p : ℕ → Aˣ} {s g : T.G}
    {a : Fin 𝔰.ϱ}
    (hK : ∀ ⦃x : T.G⦄, x ∈ K → S.HasMatrixSize 1 (x : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A))
    (hj : j ≤ 𝔰.ϱ)
    (h_near : ∃ η : T.G, η ∈ partialUnitriangularGroup j ∧ η * ((weylElem j p)⁻¹ * g) ∈ K)
    (hs : s ∈ partialUnitriangularGroup j) (hsK : s * g ∈ K) (ha : a.val < j) (i : 𝔰.BesselIndex) :
    (∏ b ∈ Finset.range (a + 1), p b).val *
      (s : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A) i (eStar a) ∈ S.ofSize (8 * 𝔰.ϱ) := by
  -- Take the rows e*_b (b < a) and i, and the columns e_d (d ≤ a), of s w_p η⁻¹. This block has
  -- size 7, being part of (s g) (η w_p⁻¹ g)⁻¹, and its determinant is the given product.
  obtain ⟨η, hη, hηK⟩ := h_near
  let c : Fin (a + 1) → Fin 𝔰.ϱ := Fin.castLE a.is_lt
  let R (b : Fin (a + 1)) : 𝔰.BesselIndex := if b = .last a then i else eStar (c b)
  let Z : Matrix (Fin (a + 1)) (Fin (a + 1)) A :=
    (s * weylElem j p * η⁻¹).val.val.submatrix R fun d ↦ inl (c d)
  have Z_size : S.HasMatrixSize 7 Z := fun b d ↦ by
    simpa [Z, Matrix.mul_assoc] using (hK hsK).mul (hK hηK).inv (R b) (inl (c d))
  -- Z = L C, where L is the same block of s w_p (w_p sends e_d to p d e*_d) and C is the block of
  -- η⁻¹ on e_0, …, e_a. L is lower triangular, C is unitriangular since η⁻¹ ∈ R^(j).
  let L : Matrix (Fin (a + 1)) (Fin (a + 1)) A := of fun b d ↦ s.val.val (R b) (eStar (c d)) * p d
  let C : Matrix (Fin (a + 1)) (Fin (a + 1)) A :=
    η⁻¹.val.val.submatrix (fun b ↦ inl (c b)) fun d ↦ inl (c d)
  have column (m : 𝔰.BesselIndex) (d : Fin (a + 1)) (hm : d ≤ level m) :
      η⁻¹.val.val m (inl (c d)) = (1 : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A) m (inl (c d)) :=
    mem_partialUnitriangularGroup.mp (inv_mem hη) m _ hm (by simp [c, ha, level, val_lt_of_le])
  have det_C : C.det = 1 := det_eq_one_of_unitriangular (lev := id) fun b d hbd ↦
    (column (inl (c b)) d hbd).trans (by simp [c, Matrix.one_apply])
  have Z_eq : Z = L * C := by
    ext b d
    -- Rows other than e_0, …, e_a have level at least d, so the column e_d of η⁻¹ vanishes there.
    have h_zero (m : 𝔰.BesselIndex) (hm : m ∉ Set.range fun e ↦ inl (c e)) :
        η⁻¹.val.val m (inl (c d)) = 0 := by
      have h_level : ↑d ≤ level m := by
        obtain e | (e | e) := m
        · exact le_of_not_gt fun he ↦ hm ⟨⟨e, Nat.lt_trans he d.is_lt⟩, rfl⟩
        · exact (c d).is_lt.le
        · exact (c d).is_lt.le.trans (le_level_eStar e)
      rw [column m d h_level, one_apply_ne fun h_eq ↦ hm ⟨d, h_eq.symm⟩]
    have h_weyl (e : Fin (a + 1)) : (s * weylElem j p).val.val (R b) (inl (c e)) = L b e := by
      have he_lt : e.val < j ∧ e.val < 𝔰.ϱ := by lia
      simp [L, mul_apply, c, he_lt, weylElem, weylOn, level]
    calc Z b d = ∑ m, (s * weylElem j p).val.val (R b) m * η⁻¹.val.val m (inl (c d)) := by
          simp only [Z, submatrix_apply, Subgroup.coe_mul, Units.val_mul, mul_apply]
      _ = ∑ e, (s * weylElem j p).val.val (R b) (inl (c e)) * C e d :=
          (sum_of_injective _ (inl_injective.comp (Fin.castLE_injective _)) _ _
            (fun m hm ↦ by rw [h_zero m hm, mul_zero]) fun _ ↦ rfl).symm
      _ = (L * C) b d := by simp only [h_weyl, mul_apply]
  -- The row of s at e*_b agrees with that of 1 outside the columns e*_d, d < b; so L is lower
  -- triangular, with p b on the diagonal for b < a.
  have s_row (b d : Fin (a + 1)) (hbd : b ≤ d) :
      s.val.val (eStar (c b)) (eStar (c d)) = if b = d then 1 else 0 := by
    have hb : (c b).val < j := (Nat.le_of_lt_succ b.is_lt).trans_lt ha
    have h_ne (e : Fin 𝔰.ϱ) (he : e < c b) : (eStar (c d) : 𝔰.BesselIndex) ≠ eStar e := by
      simpa using (he.trans_le (show c b ≤ c d from hbd)).ne'
    rw [partialUnitriangularGroup_apply_eStar hs hb _ h_ne]
    simp [c, Matrix.one_apply]
  have L_lower : L.BlockTriangular OrderDual.toDual := fun b d (hbd : b < d) ↦ by
    simp [L, R, Fin.ne_last_of_lt hbd, s_row b d hbd.le, hbd.ne]
  have L_diag (b : Fin a) : L b.castSucc b.castSucc = p b := by simp [L, R, s_row]
  have L_last : L (.last a) (.last a) = s.val.val i (eStar a) * p a := by simp [L, R, c, castLE]
  have det_Z : Z.det = (∏ b ∈ Finset.range (a + 1), p b).val * s.val.val i (eStar a) := by
    rw [det_eq_of_eq_mul_det_one C det_C Z_eq, det_of_isLowerTriangular _ L_lower,
      prod_univ_castSucc, L_last, prod_range_succ, prod_range]
    simp only [L_diag, Units.val_mul, Units.coe_prod]
    ring
  rw [← det_Z]
  exact mem_ofSize_mono (det_mem_ofSize Z a.is_lt Z_size)

/-- The leading minors at a Weyl element have bounded size. Let `K` be a set of isometries whose
matrices have size 1, and let j ≤ ϱ. Let η w_p⁻¹ g ∈ K for some η ∈ R^(j), and let s ∈ R^(j) with s
g ∈ K. Then the products p₀ ⋯ p_(l-1), l ≤ j, which are the leading minors of `T.frameGram w_p`,
have size 9 n, where n = `𝔰.n` = ϱ + 1. -/
lemma head_products_mem_ofSize {K : Set T.G}
    (hK : ∀ ⦃x : T.G⦄, x ∈ K → S.HasMatrixSize 1 (x : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A))
    (hj : j ≤ 𝔰.ϱ)
    (h_near : ∃ η : T.G, η ∈ partialUnitriangularGroup j ∧ η * ((weylElem j p)⁻¹ * g) ∈ K)
    (hs_near : s ∈ partialUnitriangularGroup j ∧ s * g ∈ K) :
    ∀ l : ℕ, l ≤ j → (↑(∏ a ∈ Finset.range l, p a) : A) ∈ S.ofSize (9 * 𝔰.n) := by
  intro l hl
  obtain ⟨η, hη, hηK⟩ := h_near
  obtain ⟨hs, hsK⟩ := hs_near
  rw [← leadingMinor_frameGram_weylElem (T := T) hj p (j := ⟨l, by lia⟩) hl]
  exact leadingMinor_mem_ofSize hs hη (hK hsK) (hK hηK) hl

/-- A bound for s e*_a, by Cramer's rule. Let `K` be a set of isometries whose matrices have size 1,
and let a < j ≤ ϱ. Let η w_p⁻¹ g ∈ K for some η ∈ R^(j), and let s ∈ R^(j) with s g ∈ K. Let `p` be
a head: the inverses of the products p₀ ⋯ p_(l-1), l ≤ j, have size 1. Then all entries of the
vector s e*_a have size 8 ϱ + 1. -/
lemma dual_mem_vecsOfSize {K : Set T.G}
    (hK : ∀ ⦃x : T.G⦄, x ∈ K → S.HasMatrixSize 1 (x : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A))
    (hj : j ≤ 𝔰.ϱ)
    (h_near : ∃ η : T.G, η ∈ partialUnitriangularGroup j ∧ η * ((weylElem j p)⁻¹ * g) ∈ K)
    (hs_near : s ∈ partialUnitriangularGroup j ∧ s * g ∈ K) (hp : S.IsHead j p) (ha : a < j) :
    (s : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A) *ᵥ Pi.single (eStar a) 1 ∈
      S.vecsOfSize (8 * 𝔰.ϱ + 1) := by
  intro i
  obtain ⟨hs, hsK⟩ := hs_near
  set M : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A := ↑s
  set P : Aˣ := ∏ b ∈ Finset.range (a + 1), p b
  have hP_inv : P⁻¹.val ∈ S.ofSize 1 := hp (a + 1) ha
  have h_cramer : P.val * M i (eStar a) ∈ S.ofSize (8 * 𝔰.ϱ) :=
    head_prod_mul_dual_mem_ofSize hK hj h_near hs hsK ha i
  have h_entry : (M *ᵥ Pi.single (eStar a) 1) i = P⁻¹.val * (P.val * M i (eStar a)) := by simp
  rw [h_entry, add_comm (8 * 𝔰.ϱ)]
  exact S.mul_mem_ofSize hP_inv h_cramer

/-- The entries of a head and of the dual vectors have bounded size. Let `K` be a set of isometries
whose matrices have size 1, and let a < j ≤ ϱ. With R^(j) = `partialUnitriangularGroup j` and the
Weyl element w_p = `weylElem j p`, let η w_p⁻¹ g ∈ K for some η ∈ R^(j), and let s ∈ R^(j) with s g
∈ K. Let `p` be a head: the inverses of the products p₀ ⋯ p_(l-1), l ≤ j, have size 1. Then p_a, its
inverse and the entries of the column s e*_a have size 10 n, where n = `𝔰.n` = ϱ + 1. -/
lemma head_entries_mem_ofSize {K : Set T.G}
    (hK : ∀ ⦃x : T.G⦄, x ∈ K → S.HasMatrixSize 1 (x : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A))
    (hj : j ≤ 𝔰.ϱ)
    (h_near : ∃ η : T.G, η ∈ partialUnitriangularGroup j ∧ η * ((weylElem j p)⁻¹ * g) ∈ K)
    (hs_near : s ∈ partialUnitriangularGroup j ∧ s * g ∈ K) (hp : S.IsHead j p) (ha : a < j) :
    (p a : A) ∈ S.ofSize (10 * 𝔰.n) ∧
    (((p a)⁻¹ : Aˣ) : A) ∈ S.ofSize (10 * 𝔰.n) ∧
    ∀ i : 𝔰.BesselIndex,
      (s : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A) i (eStar a) ∈ S.ofSize (10 * 𝔰.n) := by
  -- Both p a and its inverse are quotients of two consecutive products p₀ ⋯ p_(l-1).
  let P (l : ℕ) : Aˣ := ∏ b ∈ Finset.range l, p b
  have h_quot {l m : ℕ} (hl : l ≤ j) (hm : m ≤ j) : ((P l)⁻¹ * P m).val ∈ S.ofSize (10 * 𝔰.n) :=
    mem_ofSize_mono (S.mul_mem_ofSize (hp l hl)
      (head_products_mem_ofSize hK hj h_near hs_near m hm))
  have h_succ : P (a + 1) = P a * p a := prod_range_succ p a
  refine ⟨?_, ?_, fun i ↦ ?_⟩
  · simpa only [h_succ, inv_mul_cancel_left] using h_quot ha.le ha
  · simpa only [h_succ, _root_.mul_inv_rev, inv_mul_cancel_right] using h_quot ha ha.le
  · simpa using mem_ofSize_mono (j := 10 * 𝔰.n) (dual_mem_vecsOfSize hK hj h_near hs_near hp ha i)

omit [IsHermitianUnit T.splitGram] in
/-- If p_a and its inverse have size i for all a < j with a < ϱ, then the inverse of the Weyl
element w_p = `weylElem j p` has size i: its entries are 0, 1, star p_a and p_a⁻¹. -/
lemma hasMatrixSize_weylElem_inv (hp : ∀ a : Fin 𝔰.ϱ, a < j → (p a : A) ∈ S.ofSize i)
    (hp_inv : ∀ a : Fin 𝔰.ϱ, a < j → (((p a)⁻¹ : Aˣ) : A) ∈ S.ofSize i) :
    S.HasMatrixSize i (((weylElem j p)⁻¹ : T.G) : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A) := by
  intro k m
  obtain ⟨h_zero, h_one⟩ := S.zero_one_mem_ofSize i
  by_cases hm : floorOf m < j ∧ floorOf m < 𝔰.ϱ
  · obtain ⟨hmj, hmϱ⟩ := hm
    have h_entry : (weylElem j p : T.G)⁻¹.val.val k m =
        if k = oppositeIndex m then
          if level m < 𝔰.ϱ then star (p (floorOf m)).val else (p (floorOf m))⁻¹.val
        else 0 := by
      simp [weylElem, weylOn, hmj, hmϱ]
    rw [h_entry]
    split_ifs
    exacts [star_mem_ofSize (hp ⟨_, hmϱ⟩ hmj), hp_inv ⟨_, hmϱ⟩ hmj, h_zero]
  · rw [show (weylElem j p : T.G)⁻¹.val.val k m = if k = m then 1 else 0 by
      simp [weylElem, weylOn, hm]]
    split_ifs
    exacts [h_one, h_zero]

/-- Let j ≤ ϱ and let the isometry s lie in R^(j) = `partialUnitriangularGroup j` and in
`unipotentBelow j`. If the columns s e*_a, a < j, have size d, then s⁻¹ has size (4 (d + 1) + 12)
j + 5. -/
lemma hasMatrixSize_inv_of_mem_unipotentBelow {d : ℕ} (hj : j ≤ 𝔰.ϱ)
    (hs : s ∈ partialUnitriangularGroup j) (hs_unip : s ∈ unipotentBelow j)
    (h_col : ∀ a : Fin 𝔰.ϱ, a < j → ∀ i : 𝔰.BesselIndex,
      (s : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A) i (eStar a) ∈ S.ofSize d) :
    S.HasMatrixSize ((4 * (d + 1) + 12) * j + 5)
      ((s⁻¹ : T.G) : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A) := by
  -- Compare the gauges at 1 and at 1 * s⁻¹. They agree on Y^(j), where s acts as 1, and the e*_a
  -- are short duals as the columns s e*_a have size d. This bounds s⁻¹ - 1.
  set c : ℕ := d + 1
  have h_top : S.GaugesDifferLe 1 (1 : T.G) (1 * s⁻¹) j 0 := by
    intro i ω hω _
    refine ⟨s⁻¹.val.val *ᵥ ω, hω.congrBelow_mulVec (inv_mem hs_unip), ?_⟩
    simp [vecsOfSize, zero_one_mem_ofSize]
  have h_lift (a : Fin 𝔰.ϱ) (ha : a.val < j) :
      S.InducedLengthLe (1 * s⁻¹) a c (Pi.single (inl a) 1) := by
    refine ⟨(1 * s⁻¹).val.val *ᵥ Pi.single (inl a) 1, fun k hk ↦ ?_,
      lengthLeAt_mulVec_iff.2 (single_mem_vecsOfSize (inl a))⟩
    simpa [Matrix.one_apply, Pi.single_apply] using
      mem_partialUnitriangularGroup.1 (inv_mem hs) k (inl a) hk (.inl ⟨ha, ha⟩)
  have h_dual (a : Fin 𝔰.ϱ) (ha : a.val < j) : S.HasShortDual 1 (1 : T.G) (1 * s⁻¹) a c := by
    have h_diff : (1 : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A) *ᵥ Pi.single (eStar a) 1 -
        s.val.val *ᵥ Pi.single (eStar a) 1 ∈ S.vecsOfSize c := by
      rw [one_mulVec, mulVec_single_one]
      exact sub_mem_vecsOfSize (single_mem_vecsOfSize (eStar a)) (h_col a ha)
    exact ⟨Pi.single (eStar a) 1, fun b hb ↦ Pi.single_eq_of_ne (by grind) 1, by simp,
      lengthLeAt_one_iff.2 (single_mem_vecsOfSize (eStar a)), Pi.single (eStar a) 1, .refl _ _,
      by simpa using h_diff⟩
  have h_differ : S.GaugesDifferLe 1 (1 : T.G) (1 * s⁻¹) 0 (0 + (4 * c + 12) * j) :=
    h_top.on_whole_space_of_hasShortDual (by simp) (S.zero_one_mem_ofSize 1).right hj
      (fun a _ ↦ ⟨_, .refl _ _, lengthLeAt_one_iff.2 (single_mem_vecsOfSize (inl a))⟩) h_lift h_dual
  have h_one_sub : S.HasMatrixSize ((4 * c + 12) * j + 4) (1 - s⁻¹.val.val) := fun a b ↦ by
    simpa using neg_mem_ofSize (h_differ.hasMatrixSize_sub_one (by simp) a b)
  simpa only [sub_sub_cancel] using HasMatrixSize.one.sub h_one_sub

/-- Let `K` be a set of isometries whose matrices have size 1, and let j ≤ ϱ. Let η w_p⁻¹ g ∈ K for
some η ∈ R^(j), and let s ∈ R^(j) with s g ∈ K. Let `p` be a head: the inverses of the products p₀ ⋯
p_(l-1), l ≤ j, have size 1. If s also lies in `unipotentBelow j`, then g has size 60 n² and w_p⁻¹ g
has size 99 n², with n = `𝔰.n` = ϱ + 1. -/
lemma hasMatrixSize_of_isHead {K : Set T.G}
    (hK : ∀ ⦃x : T.G⦄, x ∈ K → S.HasMatrixSize 1 (x : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A))
    (hj : j ≤ 𝔰.ϱ)
    (h_near : ∃ η : T.G, η ∈ partialUnitriangularGroup j ∧ η * ((weylElem j p)⁻¹ * g) ∈ K)
    (hs_near : s ∈ partialUnitriangularGroup j ∧ s * g ∈ K) (hp : S.IsHead j p)
    (hs_unip : s ∈ unipotentBelow j) :
    S.HasMatrixSize (60 * 𝔰.n ^ 2) (g : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A) ∧
    S.HasMatrixSize (99 * 𝔰.n ^ 2)
      (((weylElem j p)⁻¹ * g : T.G) : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A) := by
  -- Write g = s⁻¹ (s g). The columns s e*_a bound s⁻¹, and the entries of p bound w_p⁻¹.
  have h_entries (a : Fin 𝔰.ϱ) (ha : a < j) :
      (p a : A) ∈ S.ofSize (10 * 𝔰.n) ∧ (((p a)⁻¹ : Aˣ) : A) ∈ S.ofSize (10 * 𝔰.n) ∧
        ∀ i, (s : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A) i (eStar a) ∈ S.ofSize (10 * 𝔰.n) :=
    head_entries_mem_ofSize hK hj h_near hs_near hp ha
  choose h_p h_p_inv h_col using h_entries
  obtain ⟨hs, hsK⟩ := hs_near
  have h_g : S.HasMatrixSize (60 * 𝔰.n ^ 2) (g : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A) := by
    have h_prod : S.HasMatrixSize ((4 * (10 * 𝔰.n + 1) + 12) * j + 5 + 1 + 1)
        ((s⁻¹ * (s * g) : T.G) : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A) :=
      (hasMatrixSize_inv_of_mem_unipotentBelow hj hs hs_unip h_col).mul (hK hsK)
    rw [inv_mul_cancel_left] at h_prod
    -- The size is rounded up using j ≤ ϱ.
    exact h_prod.mono (by nlinarith)
  exact ⟨h_g, ((hasMatrixSize_weylElem_inv h_p h_p_inv).mul h_g).mono (by nlinarith)⟩

end Size

end Size

end New.Floors

end
