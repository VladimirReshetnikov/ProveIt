import Lib.Adelic.TraceFormula.LineCount
import Lib.Adelic.TraceFormula.TestFunction
import Lib.Shimura.HeckeTower.HeckeData

/-!
# The stabiliser of a line at a finite place

Let `w` be a finite place of the number field `E`, with local field `LocField w` (the `E_w` of
`GL_n(E_w)`), valuation `v`, ring of integers `𝒪`, uniformiser `ϖ` and residue field of `q`
elements. In the formulas, `n` also stands for the cardinality of the index type `n`, and the
exponent `n - 2` is an integer. Let `J_line ⊂ GL_n(𝒪)` be the stabiliser of the line of a basis
vector `e_i` modulo `w`. We write `diag (ϖ, 1, …, 1)` for the diagonal matrix with `ϖ` at the index
`i` and `1` elsewhere. Let `T⁺`, `T⁻` be the operators of the double cosets of this matrix and of
its inverse, and let `e_sph` be the mean over chosen lifts to `GL_n(𝒪)` of the elements of `GL_n` of
the residue field, which on vectors fixed by the kernel of the reduction modulo `w` is the mean over
`GL_n(𝒪)`. On the vectors fixed by `J_line`, `T⁻` is the adjoint of `T⁺` in a unitary representation
(`inner_lineRaise`), and `T⁺ T⁻ = q ^ (n - 2) (1 + (q ^ n - 1) e_sph)` (`lineRaise_lineLower`). The
positive powers of `lineHecke`, the element of the group algebra that acts as `T⁺`, are supported on
integral matrices whose characteristic polynomial has the simple root `0` modulo `w`
(`lineHecke_pow_mem_spanOn`).

Notions from other files:
* `localIntGL n w` is `GL_n(𝒪)`, and `reduceGL` is its reduction to `GL_n` of the residue field
  `ResField w`.
* `parabolic lev` is the subgroup of invertible matrices that are block upper triangular for the
  level function `lev`.
* `levelSpace ρ J` is the space of vectors fixed by `J` in the representation `ρ`.
* `heckeCoset ρ J t` is the sum of `ρ g` over chosen representatives `g` of the cosets in
  `J t J / J`.

## Relation to the literature

A relation in the Hecke algebra of a parahoric subgroup of `GL_n`, proved by a direct count of
cosets.
-/

noncomputable section

namespace New

open NumberField Matrix Finset Valued MonoidAlgebra Variety InnerProductSpace DoubleCoset

/-! ### Double cosets -/

section DoubleCoset

variable {G W ι : Type} [Group G] {J : Subgroup G} {t : G}

/-- The sum in the group algebra of the chosen representatives of the cosets in `J t J / J`. It is
zero if there are infinitely many of them. -/
def doubleCosetSum (J : Subgroup G) (t : G) : ℂ[G] :=
  ∑ᶠ q : G ⧸ J, .single q.out ((doubleCoset t J J).indicator 1 q.out)

/-- If finitely many cosets of `J` meet `J t J`, the sum of their representatives is a finite
sum. -/
lemma doubleCosetSum_eq_sum
    (h_fin : HasFiniteCosets J ((doubleCoset t J J).indicator (1 : G → ℂ))) :
    doubleCosetSum J t =
      ∑ q ∈ h_fin.toFinset, .single q.out ((doubleCoset t J J).indicator 1 q.out) := by
  refine finsum_eq_sum_of_support_subset _ fun q hq ↦ h_fin.mem_toFinset.2 fun h_zero ↦ hq ?_
  simp only [h_zero, MonoidAlgebra.single_zero]

/-- If finitely many cosets of `J` meet `J t J`, the sum of their representatives in the group
algebra is supported on `J t J`. -/
lemma doubleCosetSum_mem_spanOn
    (h_fin : HasFiniteCosets J ((doubleCoset t J J).indicator (1 : G → ℂ))) :
    doubleCosetSum J t ∈ spanOn ℂ (doubleCoset t J J) := by
  rw [doubleCosetSum_eq_sum h_fin]
  refine sum_mem fun q hq ↦ ?_
  have h_mem : q.out ∈ doubleCoset t J J := Set.mem_of_indicator_ne_zero (h_fin.mem_toFinset.1 hq)
  rw [Set.indicator_of_mem h_mem]
  exact Submodule.subset_span ⟨q.out, h_mem, rfl⟩

section Module

variable [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ G W} {y : W}

/-- If finitely many cosets of `J` meet `J t J`, the sum of their representatives acts in a
representation `ρ` as the operator `heckeCoset ρ J t` of the double coset. -/
lemma asAlgebraHom_doubleCosetSum
    (h_fin : HasFiniteCosets J ((doubleCoset t J J).indicator (1 : G → ℂ))) :
    ρ.asAlgebraHom (doubleCosetSum J t) = heckeCoset ρ J t := by
  ext y
  simp [doubleCosetSum_eq_sum h_fin, heckeCoset, heckeFun_eq_sum_toFinset h_fin]

lemma apply_of_mem_levelSpace (hy : y ∈ levelSpace ρ J) {g : G} (hg : g ∈ J) : ρ g y = y := by
  simpa using mem_levelSpace.1 hy ⟨g, hg⟩

/-- The translate `ρ g y` of a vector fixed by `J` depends only on the coset `g J`. -/
lemma apply_eq_of_inv_mul_mem (hy : y ∈ levelSpace ρ J) {g h : G} (h_mem : g⁻¹ * h ∈ J) :
    ρ h y = ρ g y := by
  rw [← mul_inv_cancel_left g h, map_mul, Module.End.mul_apply, apply_of_mem_levelSpace hy h_mem]

/-- Membership in `J t J` is unchanged by right multiplication with an element of `J`. -/
lemma mul_mem_doubleCoset_iff_of_mem {g k : G} (hk : k ∈ J) :
    g * k ∈ doubleCoset t J J ↔ g ∈ doubleCoset t J J := by
  simp only [mem_doubleCoset]
  constructor
  · rintro ⟨j, hj, l, hl, h_eq⟩
    exact ⟨j, hj, l * k⁻¹, mul_mem hl (inv_mem hk), by simp [← mul_assoc, ← h_eq]⟩
  · rintro ⟨j, hj, l, hl, rfl⟩
    exact ⟨j, hj, l * k, mul_mem hl hk, mul_assoc (j * t) l k⟩

/-- On a vector fixed by `J`, the operator of `J t J` is the sum over any family `r` in `J t J` that
meets each coset `j t J` exactly once. -/
lemma heckeCoset_eq_sum (hy : y ∈ levelSpace ρ J) {s : Finset ι} {r : ι → G}
    (h_mem : ∀ a ∈ s, r a ∈ doubleCoset t J J)
    (h_inj : ∀ a ∈ s, ∀ b ∈ s, (r a)⁻¹ * r b ∈ J → a = b)
    (h_cover : ∀ j ∈ J, ∃ a ∈ s, (r a)⁻¹ * (j * t) ∈ J) :
    heckeCoset ρ J t y = ∑ a ∈ s, ρ (r a) y := by
  -- The indicator of `J t J` is right `J`-invariant, and the cosets `r a J` cover its support.
  have h_right (g : G) (k : J) : (doubleCoset t J J).indicator (1 : G → ℂ) (g * k) =
      (doubleCoset t J J).indicator 1 g := by
    classical simp [Set.indicator_apply, mul_mem_doubleCoset_iff_of_mem k.2]
  have h_all (g : G) (hg : (doubleCoset t J J).indicator (1 : G → ℂ) g ≠ 0) :
      ∃ a ∈ s, (r a : G ⧸ J) = g := by
    obtain ⟨j, hj, l, hl, rfl⟩ := mem_doubleCoset.1 (Set.mem_of_indicator_ne_zero hg)
    obtain ⟨a, ha, h_coset⟩ := h_cover j hj
    exact ⟨a, ha, QuotientGroup.eq.2 (by simpa only [mul_assoc] using mul_mem h_coset hl)⟩
  rw [heckeCoset, (heckeFun_eq_sum h_right hy
    (fun a ha b hb h_eq ↦ h_inj a ha b hb (QuotientGroup.eq.1 h_eq)) h_all).2]
  exact sum_congr rfl fun a ha ↦ by simp [Set.indicator_of_mem (h_mem a ha)]

end Module

/-- In a unitary representation `ρ` of a group `G`, let `x` and `y` be fixed by the subgroup `J` and
let the `r a` lie in `J t J`. Then each `⟪ρ (r a) x, y⟫` equals `⟪ρ t x, y⟫`, so the sum over
`a ∈ s` is this times `#s`. -/
lemma inner_sum_of_mem_doubleCoset [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    {ρ : Representation ℂ G W} (hρ : ∀ (g : G) (x y : W), ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ) {x y : W}
    (hx : x ∈ levelSpace ρ J) (hy : y ∈ levelSpace ρ J) {s : Finset ι} {r : ι → G}
    (h_mem : ∀ a ∈ s, r a ∈ doubleCoset t J J) :
    ⟪∑ a ∈ s, ρ (r a) x, y⟫_ℂ = #s • ⟪ρ t x, y⟫_ℂ := by
  rw [sum_inner, ← sum_const]
  refine sum_congr rfl fun a ha ↦ ?_
  obtain ⟨j, hj, l, hl, h_eq⟩ := mem_doubleCoset.1 (h_mem a ha)
  calc ⟪ρ (r a) x, y⟫_ℂ
    _ = ⟪ρ j (ρ t (ρ l x)), ρ j y⟫_ℂ := by simp [h_eq, apply_of_mem_levelSpace hy hj]
    _ = ⟪ρ t x, y⟫_ℂ := by rw [hρ, apply_of_mem_levelSpace hx hl]

end DoubleCoset

section LineStabilizer

variable {E n : Type} [Field E] [NumberField E] [Fintype n] [DecidableEq n] (w : FinPlace E) (i : n)

attribute [local instance] Prop.linearOrder

/-- The stabiliser `J_line` in `GL_n(𝒪)` of the line of the basis vector `e_i` modulo `w`. -/
def lineStabilizer : Subgroup (GL n (LocField w)) :=
  ((parabolic (· ≠ i)).comap reduceGL).map (localIntGL n w).subtype

/-- The stabiliser in `GL_n(𝒪)` of the hyperplane spanned by the `e_j`, `j ≠ i`, modulo `w`. -/
def hyperplaneStabilizer : Subgroup (GL n (LocField w)) :=
  ((parabolic (· = i)).comap reduceGL).map (localIntGL n w).subtype

/-- The matrix `diag (ϖ, 1, …, 1)`, with the uniformiser `ϖ` of `w` at the index `i` and `1`
elsewhere. -/
def lineElement : GL n (LocField w) := diagGL fun j : n ↦ if j = i then uniformizer w else 1

lemma lineStabilizer_le_localIntGL : lineStabilizer w i ≤ localIntGL n w :=
  Subgroup.map_subtype_le _

/-- The stabiliser of a line modulo `w` is open, as it contains the kernel of the reduction. -/
lemma isOpen_lineStabilizer : (lineStabilizer w i).IsOpen := by
  refine Subgroup.isOpen_mono (fun g hg ↦ ?_) (isOpen_localCongruence (m := 0))
  obtain ⟨h_int, h_one⟩ := mem_localCongruence_zero.1 hg
  have h_mem : reduceGL ⟨g, h_int⟩ ∈ parabolic (· ≠ i) := by simp only [h_one, one_mem]
  exact ⟨⟨g, h_int⟩, Subgroup.mem_comap.2 h_mem, rfl⟩

instance : CompactSpace (lineStabilizer w i) :=
  isCompact_iff_compactSpace.1 <| (isCompact_localIntGL w).of_isClosed_subset
    ((lineStabilizer w i).isClosed_of_isOpen (isOpen_lineStabilizer w i))
      (lineStabilizer_le_localIntGL w i)

/-- For every `t`, the indicator function of `J t J`, where `J` is the stabiliser of a line modulo
`w`, is invariant under `J` on both sides and lives on finitely many cosets of `J`. -/
lemma isHeckeFunction_indicator_doubleCoset (t : GL n (LocField w)) :
    IsHeckeFunction (lineStabilizer w i) ((doubleCoset t (lineStabilizer w i)
      (lineStabilizer w i)).indicator (1 : GL n (LocField w) → ℂ)) :=
  isHeckeFunction_doubleCoset (isOpen_lineStabilizer w i) t

lemma coe_lineElement :
    (lineElement w i).val = diagonal fun j : n ↦ if j = i then (uniformizer w).val else 1 := by
  simp [lineElement, apply_ite Units.val]

lemma coe_lineElement_inv :
    (lineElement w i)⁻¹.val = diagonal fun j : n ↦ if j = i then (uniformizer w).val⁻¹ else 1 := by
  simp [lineElement, ← map_inv, apply_ite Units.val, apply_ite Inv.inv]

variable {w : FinPlace E} {i : n} {g h : GL n (LocField w)} {k l : localIntGL n w}

lemma v_le_one_of_mem_localIntGL (hg : g ∈ localIntGL n w) (a b : n) : v (g a b) ≤ 1 :=
  (mem_intGL.1 hg).1 a b

lemma reduceGL_mul (k l : localIntGL n w) :
    reduceGL (k * l : localIntGL n w) = reduceGL k * reduceGL l := reduceGL.map_mul k l

lemma reduceGL_inv (k : localIntGL n w) : reduceGL (k⁻¹ : localIntGL n w) = (reduceGL k)⁻¹ :=
  reduceGL.map_inv k

/-- For `k` in `GL_n(𝒪)`, the entries of `reduceGL k` are the residues of those of `k`, computed by
`residueOrZero`, which reduces integral elements and is `0` elsewhere. -/
lemma coe_reduceGL (k : localIntGL n w) :
    (reduceGL k).1 = (k : GL n (LocField w)).1.map residueOrZero := by
  ext a b
  -- The entries of `reduceGL k` are by definition the residues of the integral entries of `k`.
  exact (residueOrZero_coe ⟨k.1 a b, v_le_one_of_mem_localIntGL k.2 a b⟩).symm

/-- An entry of the reduction of `k ∈ GL_n(𝒪)` vanishes exactly when that of `k` has valuation
less than `1`. -/
lemma reduceGL_apply_eq_zero_iff {a b : n} : (reduceGL k).1 a b = 0 ↔ v (k.1 a b) < 1 := by
  rw [coe_reduceGL, Matrix.map_apply, residueOrZero_eq_zero,
    (v_le_one_of_mem_localIntGL k.2 a b).lt_iff_ne]

/-- An element of `GL_n(𝒪)` stabilises the line of `e_i` modulo `w` exactly when its reduction is
block upper triangular for `(· ≠ i)`. -/
lemma coe_mem_lineStabilizer : k.1 ∈ lineStabilizer w i ↔ reduceGL k ∈ parabolic (· ≠ i) :=
  Subgroup.mem_map_iff_mem (localIntGL n w).subtype_injective

/-- An element of `GL_n(𝒪)` stabilises the hyperplane of the `e_j`, `j ≠ i`, modulo `w` exactly
when its reduction is block upper triangular for `(· = i)`. -/
lemma coe_mem_hyperplaneStabilizer :
    k.1 ∈ hyperplaneStabilizer w i ↔ reduceGL k ∈ parabolic (· = i) :=
  Subgroup.mem_map_iff_mem (localIntGL n w).subtype_injective

/-- The stabiliser of the line of `e_i` modulo `w` consists of the elements of
`localIntGL n w = GL_n(𝒪)` whose column `i` has valuation `v` less than `1` off the diagonal. -/
lemma mem_lineStabilizer :
    g ∈ lineStabilizer w i ↔ g ∈ localIntGL n w ∧ ∀ j ≠ i, v (g j i) < 1 := by
  have h_iff (hg : g ∈ localIntGL n w) : g ∈ lineStabilizer w i ↔ ∀ j ≠ i, v (g j i) < 1 := by
    simp [coe_mem_lineStabilizer (k := ⟨g, hg⟩), mem_parabolic_ne, reduceGL_apply_eq_zero_iff]
  have h_le : lineStabilizer w i ≤ localIntGL n w := lineStabilizer_le_localIntGL w i
  exact ⟨fun hg ↦ ⟨h_le hg, (h_iff (h_le hg)).1 hg⟩, fun ⟨hg, h_lt⟩ ↦ (h_iff hg).2 h_lt⟩

/-- The stabiliser of the hyperplane of the `e_j`, `j ≠ i`, modulo `w` consists of the elements of
`localIntGL n w = GL_n(𝒪)` whose row `i` has valuation `v` less than `1` off the diagonal. -/
lemma mem_hyperplaneStabilizer :
    g ∈ hyperplaneStabilizer w i ↔ g ∈ localIntGL n w ∧ ∀ j ≠ i, v (g i j) < 1 := by
  have h_iff (hg : g ∈ localIntGL n w) : g ∈ hyperplaneStabilizer w i ↔ ∀ j ≠ i, v (g i j) < 1 := by
    simp [coe_mem_hyperplaneStabilizer (k := ⟨g, hg⟩), mem_parabolic_eq, reduceGL_apply_eq_zero_iff]
  have h_le : hyperplaneStabilizer w i ≤ localIntGL n w := Subgroup.map_subtype_le _
  exact ⟨fun hg ↦ ⟨h_le hg, (h_iff (h_le hg)).1 hg⟩, fun ⟨hg, h_lt⟩ ↦ (h_iff hg).2 h_lt⟩

/-- The cosets `k J_line` and `l J_line` agree exactly when `l e_i` lies on the line of `k e_i`
modulo `w`. -/
lemma inv_mul_mem_lineStabilizer : k.1⁻¹ * l.1 ∈ lineStabilizer w i ↔
    ∃ c : ResField w, (reduceGL l).1.col i = c • (reduceGL k).1.col i := by
  rw [← Subgroup.coe_inv, ← Subgroup.coe_mul, coe_mem_lineStabilizer, reduceGL_mul, reduceGL_inv,
    inv_mul_mem_parabolic_ne]

/-- The cosets `J k` and `J l` of the stabiliser `J` of the hyperplane agree exactly when the
`i`-th row of `l` is a multiple of that of `k` modulo `w`. -/
lemma mul_inv_mem_hyperplaneStabilizer : l.1 * k.1⁻¹ ∈ hyperplaneStabilizer w i ↔
    ∃ c : ResField w, (reduceGL l).1.row i = c • (reduceGL k).1.row i := by
  rw [← Subgroup.coe_inv, ← Subgroup.coe_mul, coe_mem_hyperplaneStabilizer, reduceGL_mul,
    reduceGL_inv, mul_inv_mem_parabolic_eq]

/-- A product `x ϖ` with the uniformiser lies in the maximal ideal exactly when `x` is integral. -/
lemma v_mul_uniformizer_lt_one_iff {x : LocField w} : v (x * (uniformizer w).1) < 1 ↔ v x ≤ 1 := by
  rw [← v_uniformizer_inv_mul_le_one_iff, mul_comm x, inv_mul_cancel_left₀ (uniformizer w).ne_zero]

lemma v_uniformizer_lt_one : v (uniformizer w).1 < 1 := by
  rw [← one_mul (uniformizer w).1, v_mul_uniformizer_lt_one_iff, map_one]

omit [Fintype n] in
/-- A property `p` of index pairs holds everywhere if it holds at `(i, i)`, on the rest of row `i`
and of column `i`, and off both. -/
lemma forall_entries (i : n) {p : n → n → Prop} (h_diag : p i i) (h_row : ∀ j ≠ i, p i j)
    (h_col : ∀ j ≠ i, p j i) (h_rest : ∀ a ≠ i, ∀ b ≠ i, p a b) (a b : n) : p a b := by
  by_cases ha : a = i <;> by_cases hb : b = i <;> simp_all

/-- Conjugation `g ↦ t⁻¹ g t` by `t = diag (ϖ, 1, …, 1)`, where the uniformiser `ϖ` is at the index
`i`, takes the stabiliser in `GL_n(𝒪)` of the hyperplane spanned by the `e_j`, `j ≠ i`, modulo `w`
onto the stabiliser of the line of `e_i`. -/
lemma conj_lineElement_mem_lineStabilizer_iff :
    (lineElement w i)⁻¹ * g * lineElement w i ∈ lineStabilizer w i ↔
      g ∈ hyperplaneStabilizer w i := by
  -- Conjugation divides the `i`-th row by `ϖ`, multiplies the `i`-th column by `ϖ`, and keeps the
  -- determinant.
  set g' : GL n (LocField w) := (lineElement w i)⁻¹ * g * lineElement w i with hg'
  have h_entry (a b : n) : g' a b = (if a = i then (uniformizer w).1⁻¹ else 1) * g a b *
      if b = i then (uniformizer w).1 else 1 := by
    simp only [hg', Units.val_mul, coe_lineElement_inv, coe_lineElement, mul_diagonal, diagonal_mul]
  have h_diag : v (g' i i) ≤ 1 ↔ v (g i i) ≤ 1 := by simp [h_entry, mul_right_comm _ (g i i)]
  have h_row (j : n) (hj : j ≠ i) : v (g' i j) ≤ 1 ↔ v (g i j) < 1 := by
    rw [h_entry, ite_eq_left rfl, ite_eq_right hj, mul_one, v_uniformizer_inv_mul_le_one_iff]
  have h_col (j : n) (hj : j ≠ i) : v (g' j i) < 1 ↔ v (g j i) ≤ 1 := by
    rw [h_entry, ite_eq_left rfl, ite_eq_right hj, one_mul, v_mul_uniformizer_lt_one_iff]
  have h_rest (a b : n) (ha : a ≠ i) (hb : b ≠ i) : v (g' a b) ≤ 1 ↔ v (g a b) ≤ 1 := by
    simp [h_entry, ha, hb]
  have h_det : g'.1.det = g.1.det := by rw [hg', Units.val_mul, Units.val_mul, det_units_conj']
  have h_Kw (x : GL n (LocField w)) :
      x ∈ localIntGL n w ↔ (∀ a b : n, v (x a b) ≤ 1) ∧ v x.1.det = 1 := mem_intGL_iff_det
  rw [mem_lineStabilizer, mem_hyperplaneStabilizer, h_Kw, h_Kw, h_det]
  constructor
  · rintro ⟨⟨h_int, h_unit⟩, h_small⟩
    have h_small' (j : n) (hj : j ≠ i) : v (g i j) < 1 := (h_row j hj).1 (h_int i j)
    exact ⟨⟨forall_entries i (h_diag.1 (h_int i i)) (fun j hj ↦ (h_small' j hj).le)
      (fun j hj ↦ (h_col j hj).1 (h_small j hj))
      fun a ha b hb ↦ (h_rest a b ha hb).1 (h_int a b), h_unit⟩, h_small'⟩
  · rintro ⟨⟨h_int, h_unit⟩, h_small⟩
    have h_small' (j : n) (hj : j ≠ i) : v (g' j i) < 1 := (h_col j hj).2 (h_int j i)
    exact ⟨⟨forall_entries i (h_diag.2 (h_int i i)) (fun j hj ↦ (h_row j hj).2 (h_small j hj))
      (fun j hj ↦ (h_small' j hj).le)
      fun a ha b hb ↦ (h_rest a b ha hb).2 (h_int a b), h_unit⟩, h_small'⟩

/-- A chosen element of `GL_n(𝒪)` with reduction `M`, for an invertible matrix `M` over the residue
field. -/
def liftMatrix (M : Matrix n n (ResField w)) : localIntGL n w :=
  Function.invFun (fun k : localIntGL n w ↦ (reduceGL k).1) M

/-- For an invertible matrix `M` over the residue field, the chosen lift `liftMatrix M` reduces to
`M`. -/
lemma reduceGL_liftMatrix {M : Matrix n n (ResField w)} (hM_det : M.det ≠ 0) :
    (reduceGL (liftMatrix M)).1 = M := by
  obtain ⟨k, hk⟩ := reduceGL_surjective (GeneralLinearGroup.mkOfDetNeZero M hM_det)
  exact Function.invFun_eq (f := fun k : localIntGL n w ↦ (reduceGL k).1) ⟨k, congrArg Units.val hk⟩

lemma reduceGL_liftMatrix_val (g : GL n (ResField w)) : reduceGL (liftMatrix g.1) = g :=
  Units.ext (reduceGL_liftMatrix g.det_ne_zero)

/-- The representative of the coset in `J_line diag (ϖ, 1, …, 1) J_line / J_line` that corresponds
to the hyperplane on which the linear form `ξ` with `ξ e_i = 1` vanishes. -/
def raiseCosetRep (i : n) (ξ : n → ResField w) : GL n (LocField w) :=
  (liftMatrix (updateRow 1 i ξ)).1⁻¹ * lineElement w i

/-- The representative of the coset in `J_line diag (ϖ, 1, …, 1)⁻¹ J_line / J_line` that corresponds
to the line of a vector `z` with `z i = 1`. -/
def lowerCosetRep (i : n) (z : n → ResField w) : GL n (LocField w) :=
  (lineElement w i)⁻¹ * (liftMatrix (updateCol 1 i z)).1

variable {ξ z : n → ResField w}

/-- For `ξ i = 1`, the chosen lift of the identity with row `i` replaced by `ξ` has this matrix as
its reduction. -/
lemma reduceGL_liftMatrix_updateRow (hξ : ξ i = 1) :
    (reduceGL (liftMatrix (updateRow 1 i ξ))).1 = updateRow 1 i ξ :=
  reduceGL_liftMatrix (by simp [det_updateRow_one, hξ])

/-- For `z i = 1`, the chosen lift of the identity with column `i` replaced by `z` has this matrix
as its reduction. -/
lemma reduceGL_liftMatrix_updateCol (hz : z i = 1) :
    (reduceGL (liftMatrix (updateCol 1 i z))).1 = updateCol 1 i z :=
  reduceGL_liftMatrix (by simp [det_updateCol_one, hz])

lemma col_reduceGL_liftMatrix_updateCol (hz : z i = 1) :
    (reduceGL (liftMatrix (updateCol 1 i z))).1.col i = z :=
  funext fun _ ↦ by simp [reduceGL_liftMatrix_updateCol hz]

/-- For `ξ i = 1`, `raiseCosetRep i ξ` lies in the double coset of `diag (ϖ, 1, …, 1)` for the
stabiliser of the line of `e_i` modulo `w`. -/
lemma raiseCosetRep_mem_doubleCoset (hξ : ξ i = 1) :
    raiseCosetRep i ξ ∈
      doubleCoset (lineElement w i) (lineStabilizer w i) (lineStabilizer w i) := by
  have h_mem : (liftMatrix (updateRow 1 i ξ)).1 ∈ lineStabilizer w i :=
    coe_mem_lineStabilizer.2 <| mem_parabolic_ne.2 fun j hj ↦ by
      simp [reduceGL_liftMatrix_updateRow hξ, hj]
  exact mem_doubleCoset.2 ⟨_, inv_mem h_mem, 1, one_mem _, by rw [mul_one, raiseCosetRep]⟩

/-- For `z i = 1`, `lowerCosetRep i z` lies in the double coset of `diag (ϖ, 1, …, 1)⁻¹` for the
stabiliser of the line of `e_i` modulo `w`. -/
lemma lowerCosetRep_mem_doubleCoset (hz : z i = 1) :
    lowerCosetRep i z ∈
      doubleCoset (lineElement w i)⁻¹ (lineStabilizer w i) (lineStabilizer w i) := by
  have h_mem : (liftMatrix (updateCol 1 i z)).1 ∈ hyperplaneStabilizer w i :=
    coe_mem_hyperplaneStabilizer.2 <| mem_parabolic_eq.2 fun j hj ↦ by
      simp [reduceGL_liftMatrix_updateCol hz, hj, hj.symm]
  -- Conjugation by `diag (ϖ, 1, …, 1)` takes the lift into the stabiliser of the line.
  exact mem_doubleCoset.2
    ⟨_, conj_lineElement_mem_lineStabilizer_iff.2 h_mem, 1, one_mem _, by simp [lowerCosetRep]⟩

omit [Fintype n] [DecidableEq n] in
/-- If two vectors with `i`-th coordinate `1` are proportional, they are equal. -/
lemma eq_of_eq_smul_of_apply_eq_one {z z' : n → ResField w} {c : ResField w} (hz : z i = 1)
    (hz' : z' i = 1) (h_eq : z' = c • z) : z = z' := by
  subst h_eq
  simp_all [show c = 1 by simpa [hz] using hz']

/-- For `ξ i = 1` and `k` in `GL_n(𝒪)`, the coset `k⁻¹ diag (ϖ, 1, …, 1) J_line` is that of the
representative `raiseCosetRep i ξ` exactly when `ξ` is a multiple of the `i`-th row of `k` modulo
`w`. Here `J_line` is the stabiliser of the line of `e_i` modulo `w`. -/
lemma raiseCosetRep_inv_mul_mem_lineStabilizer_iff (hξ : ξ i = 1) :
    (raiseCosetRep i ξ)⁻¹ * (k.1⁻¹ * lineElement w i) ∈ lineStabilizer w i ↔
      ∃ c : ResField w, ξ = c • (reduceGL k).1.row i := by
  have h_conj : (raiseCosetRep i ξ)⁻¹ * (k.1⁻¹ * lineElement w i) = (lineElement w i)⁻¹ *
      ((liftMatrix (updateRow 1 i ξ)).1 * k.1⁻¹) * lineElement w i := by
    simp [raiseCosetRep, mul_assoc]
  rw [h_conj, conj_lineElement_mem_lineStabilizer_iff, mul_inv_mem_hyperplaneStabilizer,
    reduceGL_liftMatrix_updateRow hξ, show (updateRow 1 i ξ).row i = ξ from updateRow_self]

/-- For `z i = 1` and `k` in `GL_n(𝒪)`, the coset `diag (ϖ, 1, …, 1)⁻¹ k J_line` is that of the
representative `lowerCosetRep i z` exactly when the `i`-th column of `k` modulo `w` is a multiple of
`z`. Here `J_line` is the stabiliser of the line of `e_i` modulo `w`. -/
lemma lowerCosetRep_inv_mul_mem_lineStabilizer_iff (hz : z i = 1) :
    (lowerCosetRep i z)⁻¹ * ((lineElement w i)⁻¹ * k.1) ∈ lineStabilizer w i ↔
      ∃ c : ResField w, (reduceGL k).1.col i = c • z := by
  have h_cancel : (lowerCosetRep i z)⁻¹ * ((lineElement w i)⁻¹ * k.1) =
      (liftMatrix (updateCol 1 i z)).1⁻¹ * k.1 := by simp [lowerCosetRep, mul_assoc]
  rw [h_cancel, inv_mul_mem_lineStabilizer, col_reduceGL_liftMatrix_updateCol hz]

end LineStabilizer

/-! ### The operators -/

section Operators

variable {E n : Type} [Field E] [NumberField E] [Fintype n] [DecidableEq n] (w : FinPlace E) (i : n)

/-- The sum in the group algebra of chosen representatives of the cosets in
`J_line diag (ϖ, 1, …, 1) J_line / J_line`. -/
def lineHecke : ℂ[GL n (LocField w)] := doubleCosetSum (lineStabilizer w i) (lineElement w i)

/-- The sum in the group algebra of chosen representatives of the cosets in
`J_line diag (ϖ, 1, …, 1)⁻¹ J_line / J_line`. It acts as `T⁻`. -/
def lineHeckeLower : ℂ[GL n (LocField w)] := doubleCosetSum (lineStabilizer w i) (lineElement w i)⁻¹

variable (n) in
/-- The mean in the group algebra of chosen lifts to `GL_n(𝒪)` of all elements of `GL_n` of the
residue field. -/
def sphericalMeanElement : ℂ[GL n (LocField w)] :=
  (Nat.card (GL n (ResField w)) : ℂ)⁻¹ • ∑ᶠ g : GL n (ResField w), .single (liftMatrix g.1).1 1

variable {w} {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GL n (LocField w)) W)

/-- The operator `T⁺`, the sum over the cosets in `J_line diag (ϖ, 1, …, 1) J_line / J_line`. -/
def lineRaise : Module.End ℂ W := heckeCoset ρ (lineStabilizer w i) (lineElement w i)

/-- The operator `T⁻`, the sum over the cosets in `J_line diag (ϖ, 1, …, 1)⁻¹ J_line / J_line`. -/
def lineLower : Module.End ℂ W := heckeCoset ρ (lineStabilizer w i) (lineElement w i)⁻¹

/-- The operator `e_sph`, the action of the mean of chosen lifts to `GL_n(𝒪)` of the elements of
`GL_n` of the residue field. -/
def sphericalMean : Module.End ℂ W := ρ.asAlgebraHom (sphericalMeanElement n w)

/-- The translate `y[z]` of `y` by a chosen element of `GL_n(𝒪)` that takes `e_i` to `z` modulo
`w`. It is used for `z ≠ 0` and `y` fixed by `J_line`; then it depends only on the line of `z`
(`lineTranslate_eq_apply_of_col_eq_smul`). -/
def lineTranslate (y : W) (z : n → ResField w) : W :=
  ρ (Function.invFun (fun k : localIntGL n w ↦ (reduceGL k).1.col i) z).1 y

lemma asAlgebraHom_lineHecke : ρ.asAlgebraHom (lineHecke w i) = lineRaise i ρ :=
  asAlgebraHom_doubleCosetSum (isHeckeFunction_indicator_doubleCoset w i (lineElement w i)).1

lemma asAlgebraHom_lineHeckeLower : ρ.asAlgebraHom (lineHeckeLower w i) = lineLower i ρ :=
  asAlgebraHom_doubleCosetSum (isHeckeFunction_indicator_doubleCoset w i (lineElement w i)⁻¹).1

lemma asAlgebraHom_sphericalMeanElement :
  ρ.asAlgebraHom (sphericalMeanElement n w) = sphericalMean ρ := rfl

end Operators

section FixedVectors

variable {E n : Type} [Field E] [NumberField E] [Fintype n] [DecidableEq n] {w : FinPlace E} {i : n}
  {k : localIntGL n w} {z ξ : n → ResField w}

variable {W : Type} [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ (GL n (LocField w)) W}
  {y : W}

lemma lineRaise_mem (hy : y ∈ levelSpace ρ (lineStabilizer w i)) :
    lineRaise i ρ y ∈ levelSpace ρ (lineStabilizer w i) :=
  (isHeckeFunction_indicator_doubleCoset w i (lineElement w i)).heckeFun_mem hy

lemma lineLower_mem (hy : y ∈ levelSpace ρ (lineStabilizer w i)) :
    lineLower i ρ y ∈ levelSpace ρ (lineStabilizer w i) :=
  (isHeckeFunction_indicator_doubleCoset w i (lineElement w i)⁻¹).heckeFun_mem hy

/-- For a vector `y` fixed by the stabiliser `J_line` of the line of `e_i` modulo `w` and `z ≠ 0`,
the vector `y[z] = lineTranslate i ρ y z` is the translate of `y` by any `k` in `GL_n(𝒪)` whose
reduction modulo `w` takes `e_i` to a multiple of `z`. -/
lemma lineTranslate_eq_apply_of_col_eq_smul (hy : y ∈ levelSpace ρ (lineStabilizer w i))
    (hz : z ≠ 0) {c : ResField w} (hk : (reduceGL k).1.col i = c • z) :
    lineTranslate i ρ y z = ρ k.1 y := by
  obtain ⟨g, hg⟩ := exists_col_eq i hz
  obtain ⟨l, rfl⟩ : ∃ l : localIntGL n w, reduceGL l = g := reduceGL_surjective g
  set k₀ : localIntGL n w := Function.invFun (fun k : localIntGL n w ↦ (reduceGL k).1.col i) z with
    hk₀
  have h_col : (reduceGL k₀).1.col i = z :=
    Function.invFun_eq (f := fun k : localIntGL n w ↦ (reduceGL k).1.col i) ⟨l, hg⟩
  have h_mem : k₀.1⁻¹ * k.1 ∈ lineStabilizer w i :=
    inv_mul_mem_lineStabilizer.2 ⟨c, by rw [hk, h_col]⟩
  rw [lineTranslate, ← hk₀, apply_eq_of_inv_mul_mem hy h_mem]

/-- For a vector `y` fixed by `J_line` and `z ≠ 0` on the line of `e_i`, the translate
`y[z] = lineTranslate i ρ y z` is `y` itself. -/
lemma lineTranslate_eq_self (hy : y ∈ levelSpace ρ (lineStabilizer w i)) (hz : z ≠ 0)
    (h_line : ∀ j ≠ i, z j = 0) : lineTranslate i ρ y z = y := by
  obtain ⟨c, rfl⟩ := exists_eq_smul_single_iff.2 h_line
  have h_col : (reduceGL (1 : localIntGL n w)).1.col i = c⁻¹ • c • Pi.single i 1 := by
    rw [inv_smul_smul₀ (left_ne_zero_of_smul hz), ← mulVec_single_one,
      show reduceGL (1 : localIntGL n w) = 1 from reduceGL.map_one, Units.val_one, one_mulVec]
  rw [lineTranslate_eq_apply_of_col_eq_smul hy hz h_col, Subgroup.coe_one, map_one,
    Module.End.one_apply]

/-- For a vector `y` fixed by the stabiliser `J_line` of the line of `e_i` modulo `w`, a vector
`z ≠ 0` and `k` in `GL_n(𝒪) = localIntGL n w`, the translate of `y[z] = lineTranslate i ρ y z` by
`k` is `y[k z]`, where `k z` is taken modulo `w` by the reduction `reduceGL`. -/
lemma apply_lineTranslate (hy : y ∈ levelSpace ρ (lineStabilizer w i)) (hz : z ≠ 0)
    (k : localIntGL n w) :
    ρ k.1 (lineTranslate i ρ y z) = lineTranslate i ρ y ((reduceGL k).1 *ᵥ z) := by
  obtain ⟨g, rfl⟩ := exists_col_eq i hz
  obtain ⟨l, rfl⟩ : ∃ l : localIntGL n w, reduceGL l = g := reduceGL_surjective g
  have h_ne : (reduceGL k).1 *ᵥ (reduceGL l).1.col i ≠ 0 := by
    simpa only [mulVec_zero] using (mulVec_injective_iff_isUnit.2 (reduceGL k).isUnit).ne hz
  have h_col : (reduceGL (k * l)).1.col i =
      (1 : ResField w) • (reduceGL k).1 *ᵥ (reduceGL l).1.col i := by
    rw [one_smul, reduceGL_mul, Units.val_mul, ← mulVec_single_one, ← mulVec_single_one,
      mulVec_mulVec]
  rw [lineTranslate_eq_apply_of_col_eq_smul hy hz (one_smul _ _).symm,
    lineTranslate_eq_apply_of_col_eq_smul hy h_ne h_col, Subgroup.coe_mul,
    map_mul, Module.End.mul_apply]

/-- Let `y` be fixed by `J_line`, let `k` be in `GL_n(𝒪)` and let `S`, `S'` be sets of vectors with
`0 ∉ S` such that `z ∈ S` exactly when `k z ∈ S'` modulo `w`. Then `k` takes the sum of the
translates `y[z] = lineTranslate i ρ y z` over `S` to the sum over `S'`. -/
lemma apply_sum_lineTranslate (hy : y ∈ levelSpace ρ (lineStabilizer w i)) (k : localIntGL n w)
    {S S' : Finset (n → ResField w)} (hS : 0 ∉ S)
    (h_iff : ∀ z : n → ResField w, z ∈ S ↔ (reduceGL k).1 *ᵥ z ∈ S') :
    ρ k.1 (∑ z ∈ S, lineTranslate i ρ y z) = ∑ z ∈ S', lineTranslate i ρ y z := by
  rw [map_sum]
  exact sum_bijective _ (mulVec_injective_iff_isUnit.2 (reduceGL k).isUnit).bijective_of_finite
    h_iff fun z hz ↦ apply_lineTranslate hy (ne_of_mem_of_not_mem hz hS) k

/-- On a vector fixed by `J_line`, the chosen lift of `g` to `GL_n(𝒪)` acts as any other lift
`k`. -/
lemma apply_liftMatrix_eq (hy : y ∈ levelSpace ρ (lineStabilizer w i)) {g : GL n (ResField w)}
    (hk : reduceGL k = g) : ρ (liftMatrix g.1).1 y = ρ k.1 y :=
  apply_eq_of_inv_mul_mem hy <|
    inv_mul_mem_lineStabilizer.2 ⟨1, by rw [reduceGL_liftMatrix_val, hk, one_smul]⟩

/-- The operator `e_sph = sphericalMean ρ` is the mean of the actions of the chosen lifts to
`GL_n(𝒪)` of the elements of `GL_n` of the residue field. -/
lemma sphericalMean_apply [Fintype (GL n (ResField w))] (x : W) : sphericalMean ρ x =
    (Fintype.card (GL n (ResField w)) : ℂ)⁻¹ • ∑ g : GL n (ResField w), ρ (liftMatrix g.1).1 x := by
  simp [sphericalMean, sphericalMeanElement, finsum_eq_sum_of_fintype]

lemma sphericalMean_eq_self (hy_Kw : y ∈ levelSpace ρ (localIntGL n w)) :
    sphericalMean ρ y = y := by
  have : Fintype (GL n (ResField w)) := Fintype.ofFinite _
  simp [sphericalMean_apply, apply_of_mem_levelSpace hy_Kw, ← Nat.cast_smul_eq_nsmul ℂ]

/-- The operator `e_sph = sphericalMean ρ` takes a vector fixed by `J_line` to one fixed by
`GL_n(𝒪) = localIntGL n w`. -/
lemma sphericalMean_mem (hy : y ∈ levelSpace ρ (lineStabilizer w i)) :
    sphericalMean ρ y ∈ levelSpace ρ (localIntGL n w) := by
  have : Fintype (GL n (ResField w)) := Fintype.ofFinite _
  refine mem_levelSpace.2 fun k ↦ ?_
  have h_term (g : GL n (ResField w)) :
      ρ k.1 (ρ (liftMatrix g.1).1 y) = ρ (liftMatrix (reduceGL k * g).1).1 y := by
    have h_reduce : reduceGL (k * liftMatrix g.1) = reduceGL k * g := by
      rw [reduceGL_mul, reduceGL_liftMatrix_val]
    rw [apply_liftMatrix_eq hy h_reduce, Subgroup.coe_mul, map_mul, Module.End.mul_apply]
  -- Left multiplication by the reduction of `k` permutes the terms of the mean.
  rw [sphericalMean_apply, map_smul, map_sum, MonoidHom.one_apply, one_smul,
    Fintype.sum_equiv (Equiv.mulLeft (reduceGL k)) _
      (fun g ↦ ρ (liftMatrix g.1).1 y) h_term]

/-- A vector fixed by `J_line` and its translates by `GL_n(𝒪)` have the same image under
`e_sph = sphericalMean ρ`. -/
lemma sphericalMean_apply_translate (hy : y ∈ levelSpace ρ (lineStabilizer w i))
    (k : localIntGL n w) : sphericalMean ρ (ρ k.1 y) = sphericalMean ρ y := by
  have : Fintype (GL n (ResField w)) := Fintype.ofFinite _
  have h_term (g : GL n (ResField w)) :
      ρ (liftMatrix g.1).1 (ρ k.1 y) = ρ (liftMatrix (g * reduceGL k).1).1 y := by
    have h_reduce : reduceGL (liftMatrix g.1 * k) = g * reduceGL k := by
      rw [reduceGL_mul, reduceGL_liftMatrix_val]
    rw [apply_liftMatrix_eq hy h_reduce, Subgroup.coe_mul, map_mul, Module.End.mul_apply]
  -- Right multiplication by the reduction of `k` permutes the terms of the mean.
  rw [sphericalMean_apply, sphericalMean_apply,
    Fintype.sum_equiv (Equiv.mulRight (reduceGL k)) _
      (fun g ↦ ρ (liftMatrix g.1).1 y) h_term]

/-- Let `y` be fixed by the stabiliser `J_line` of the line of `e_i` modulo `w`. Then
`T⁺ y = lineRaise i ρ y` is the sum of its translates by the coset representatives
`raiseCosetRep i ξ` of `J_line diag (ϖ, 1, …, 1) J_line`, over the forms `ξ` with `ξ e_i = 1`, that
is, over the hyperplanes modulo `w` that do not contain `e_i`. -/
lemma lineRaise_eq_sum [Fintype (ResField w)] [DecidableEq (ResField w)]
    (hy : y ∈ levelSpace ρ (lineStabilizer w i)) :
    lineRaise i ρ y = ∑ ξ : n → ResField w with ξ i = 1, ρ (raiseCosetRep i ξ) y := by
  -- The representatives give distinct cosets, and these cover the double coset.
  have h_inj (ξ η : n → ResField w) (hξ : ξ i = 1) (hη : η i = 1)
      (h_mem : (raiseCosetRep i ξ)⁻¹ * raiseCosetRep i η ∈ lineStabilizer w i) : ξ = η := by
    obtain ⟨c, hc⟩ := (raiseCosetRep_inv_mul_mem_lineStabilizer_iff
      (k := liftMatrix (updateRow 1 i η)) hξ).1 h_mem
    have h_row : (updateRow 1 i η).row i = η := updateRow_self
    rw [reduceGL_liftMatrix_updateRow hη, h_row] at hc
    exact (eq_of_eq_smul_of_apply_eq_one hη hξ hc).symm
  have h_cover (j : GL n (LocField w)) (hj : j ∈ lineStabilizer w i) : ∃ ξ : n → ResField w,
      ξ i = 1 ∧ (raiseCosetRep i ξ)⁻¹ * (j * lineElement w i) ∈ lineStabilizer w i := by
    obtain ⟨k, hk, rfl⟩ : ∃ k : localIntGL n w, k.1 ∈ lineStabilizer w i ∧ j = k.1⁻¹ :=
      ⟨⟨j⁻¹, lineStabilizer_le_localIntGL w i (inv_mem hj)⟩, inv_mem hj, (inv_inv j).symm⟩
    have h_corner : (reduceGL k).1 i i ≠ 0 :=
      diag_ne_zero_of_col (mem_parabolic_ne.1 (coe_mem_lineStabilizer.1 hk))
    -- The hyperplane is given by the `i`-th row of `k`, scaled to take the value `1` at `e_i`.
    let ξ : n → ResField w := ((reduceGL k).1 i i)⁻¹ • (reduceGL k).1.row i
    have hξ : ξ i = 1 := by simp [ξ, h_corner]
    exact ⟨ξ, hξ, (raiseCosetRep_inv_mul_mem_lineStabilizer_iff hξ).2 ⟨_, rfl⟩⟩
  exact heckeCoset_eq_sum hy (fun ξ hξ ↦ raiseCosetRep_mem_doubleCoset (mem_filter.1 hξ).2)
    (by simpa using fun ξ hξ η ↦ h_inj ξ η hξ) (by simpa using h_cover)

/-- Let `y` be fixed by the stabiliser `J_line` of the line of `e_i` modulo `w`. Then
`T⁻ y = lineLower i ρ y` is the sum of its translates by the coset representatives
`lowerCosetRep i z` of `J_line diag (ϖ, 1, …, 1)⁻¹ J_line`, over the vectors `z` with `z i = 1`,
that is, over the lines modulo `w` outside the hyperplane `z i = 0`. -/
lemma lineLower_eq_sum [Fintype (ResField w)] [DecidableEq (ResField w)]
    (hy : y ∈ levelSpace ρ (lineStabilizer w i)) :
    lineLower i ρ y = ∑ z : n → ResField w with z i = 1, ρ (lowerCosetRep i z) y := by
  -- The representatives give distinct cosets, and these cover the double coset.
  have h_inj (z z' : n → ResField w) (hz : z i = 1) (hz' : z' i = 1)
      (h_mem : (lowerCosetRep i z)⁻¹ * lowerCosetRep i z' ∈ lineStabilizer w i) : z = z' := by
    obtain ⟨c, hc⟩ := (lowerCosetRep_inv_mul_mem_lineStabilizer_iff
      (k := liftMatrix (updateCol 1 i z')) hz).1 h_mem
    rw [col_reduceGL_liftMatrix_updateCol hz'] at hc
    exact eq_of_eq_smul_of_apply_eq_one hz hz' hc
  have h_cover (j : GL n (LocField w)) (hj : j ∈ lineStabilizer w i) : ∃ z : n → ResField w,
      z i = 1 ∧ (lowerCosetRep i z)⁻¹ * (j * (lineElement w i)⁻¹) ∈ lineStabilizer w i := by
    have h_conj : lineElement w i * j * (lineElement w i)⁻¹ ∈ hyperplaneStabilizer w i := by
      simpa [← conj_lineElement_mem_lineStabilizer_iff, mul_assoc] using hj
    obtain ⟨k, hk, h_eq⟩ : ∃ k : localIntGL n w, k.1 ∈ hyperplaneStabilizer w i ∧
        j * (lineElement w i)⁻¹ = (lineElement w i)⁻¹ * k.1 :=
      ⟨⟨_, (mem_hyperplaneStabilizer.1 h_conj).1⟩, h_conj, by simp [mul_assoc]⟩
    have h_corner : (reduceGL k).1 i i ≠ 0 :=
      diag_ne_zero_of_row (mem_parabolic_eq.1 (coe_mem_hyperplaneStabilizer.1 hk))
    -- The line is spanned by the `i`-th column of `k`, scaled to have the entry `1` at `i`.
    let z : n → ResField w := ((reduceGL k).1 i i)⁻¹ • (reduceGL k).1.col i
    have hz : z i = 1 := by simp [z, h_corner]
    rw [h_eq]
    exact ⟨z, hz, (lowerCosetRep_inv_mul_mem_lineStabilizer_iff hz).2
      ⟨(reduceGL k).1 i i, (smul_inv_smul₀ h_corner _).symm⟩⟩
  exact heckeCoset_eq_sum hy (fun z hz ↦ lowerCosetRep_mem_doubleCoset (mem_filter.1 hz).2)
    (by simpa using fun z hz z' ↦ h_inj z z' hz) (by simpa using h_cover)

/-- For `y` fixed by `J_line` and a form `ξ` with `ξ e_i = 1`, the representative
`raiseCosetRep i ξ` of the coset of `T⁺` that corresponds to the hyperplane `ξ = 0` takes
`T⁻ y = lineLower i ρ y` to the sum of the translates `y[z] = lineTranslate i ρ y z` over the
vectors `z` with `ξ z = 1`, that is, over the lines outside the hyperplane `ξ = 0`. -/
lemma raiseCosetRep_apply_lineLower [Fintype (ResField w)] [DecidableEq (ResField w)]
    (hy : y ∈ levelSpace ρ (lineStabilizer w i)) (hξ : ξ i = 1) :
    ρ (raiseCosetRep i ξ) (lineLower i ρ y) =
      ∑ z : n → ResField w with ξ ⬝ᵥ z = 1, lineTranslate i ρ y z := by
  set b : localIntGL n w := liftMatrix (updateRow 1 i ξ) with hb
  have h_lower : ρ (lineElement w i) (lineLower i ρ y) =
      ∑ z : n → ResField w with z i = 1, lineTranslate i ρ y z := by
    rw [lineLower_eq_sum hy, map_sum]
    refine sum_congr rfl fun z hz ↦ ?_
    have hz_one : z i = 1 := (mem_filter.1 hz).2
    have h_col : (reduceGL (liftMatrix (updateCol 1 i z))).1.col i = (1 : ResField w) • z := by
      rw [col_reduceGL_liftMatrix_updateCol hz_one, one_smul]
    have hz_ne : z ≠ 0 := Function.ne_iff.2 ⟨i, hz_one.trans_ne one_ne_zero⟩
    rw [lineTranslate_eq_apply_of_col_eq_smul hy hz_ne h_col, lowerCosetRep, ← Module.End.mul_apply,
      ← map_mul,
      mul_inv_cancel_left]
  have h_move : ρ b.1 (∑ z : n → ResField w with ξ ⬝ᵥ z = 1, lineTranslate i ρ y z) =
      ∑ z : n → ResField w with z i = 1, lineTranslate i ρ y z := by
    refine apply_sum_lineTranslate hy b (by simp) fun z ↦ ?_
    rw [mem_filter_univ, mem_filter_univ, hb, reduceGL_liftMatrix_updateRow hξ, updateRow_mulVec,
      Function.update_self]
  calc ρ (raiseCosetRep i ξ) (lineLower i ρ y)
    _ = ρ b.1⁻¹ (ρ (lineElement w i) (lineLower i ρ y)) := by
      rw [raiseCosetRep, ← hb, map_mul, Module.End.mul_apply]
    _ = ρ b.1⁻¹ (ρ b.1 (∑ z : n → ResField w with ξ ⬝ᵥ z = 1, lineTranslate i ρ y z)) := by
      rw [h_lower, h_move]
    _ = ∑ z : n → ResField w with ξ ⬝ᵥ z = 1, lineTranslate i ρ y z := ρ.inv_self_apply b.1 _

/-- For `y` fixed by `J_line`, the sum of the translates `y[z] = lineTranslate i ρ y z` over all
`z ≠ 0`, in which each line occurs `q - 1` times, is `(q ^ n - 1) e_sph y`. Here `q` is the order
of the residue field, the exponent `n` stands for the number of indices and `e_sph` is
`sphericalMean ρ`. -/
lemma sum_lineTranslate [Fintype (ResField w)] [DecidableEq (ResField w)]
    (hy : y ∈ levelSpace ρ (lineStabilizer w i)) :
    ∑ z : n → ResField w with z ≠ 0, lineTranslate i ρ y z =
      ((w.q : ℂ) ^ Fintype.card n - 1) • sphericalMean ρ y := by
  -- The sum is fixed by `GL_n(𝒪)`, so it equals its mean, and each term has the mean of `y`.
  have h_fixed :
      ∑ z : n → ResField w with z ≠ 0, lineTranslate i ρ y z ∈ levelSpace ρ (localIntGL n w) := by
    refine mem_levelSpace.2 fun k ↦ ?_
    rw [MonoidHom.one_apply, one_smul]
    refine apply_sum_lineTranslate hy k (by simp) fun z ↦ ?_
    have h_inj : Function.Injective (reduceGL k).1.mulVec :=
      mulVec_injective_iff_isUnit.2 (reduceGL k).isUnit
    simpa only [mem_filter_univ, mulVec_zero] using (h_inj.ne_iff (x := z) (y := 0)).symm
  have h_term (z : n → ResField w) :
      sphericalMean ρ (lineTranslate i ρ y z) = sphericalMean ρ y :=
    sphericalMean_apply_translate hy _
  have h_card : (#{z : n → ResField w | z ≠ 0} : ℂ) = (w.q : ℂ) ^ Fintype.card n - 1 := by
    rw [filter_ne', card_erase_of_mem (mem_univ _), card_univ, Nat.cast_pred Fintype.card_pos,
      Fintype.card_fun, ← Nat.card_eq_fintype_card, card_ResField, Nat.cast_pow]
  calc ∑ z : n → ResField w with z ≠ 0, lineTranslate i ρ y z
    _ = sphericalMean ρ (∑ z : n → ResField w with z ≠ 0, lineTranslate i ρ y z) :=
      (sphericalMean_eq_self h_fixed).symm
    _ = _ := by simp only [map_sum, h_term, sum_const, ← Nat.cast_smul_eq_nsmul ℂ, h_card]
/-- Let `ρ` be a complex representation of `GL_n(E_w)` at a finite place `w` of the number field
`E`, and let `y` be a vector fixed by the stabiliser `J_line` in `GL_n(𝒪_w)` of the line of `e_i`
modulo `w`. Then `T⁺ T⁻ y = q ^ (n - 2) (y + (q ^ n - 1) e_sph y)`. Here `T⁺ = lineRaise i ρ` and
`T⁻ = lineLower i ρ` are the sums over the cosets in `J_line diag (ϖ, 1, …, 1) J_line / J_line` and
in `J_line diag (ϖ, 1, …, 1)⁻¹ J_line / J_line`, `e_sph = sphericalMean ρ` is the action of the mean
of chosen lifts to `GL_n(𝒪_w)` of all elements of `GL_n` of the residue field, `q` is the order of
the residue field, and the exponent `n` stands for the number of indices. -/
theorem lineRaise_lineLower (hy : y ∈ levelSpace ρ (lineStabilizer w i)) :
    lineRaise i ρ (lineLower i ρ y) = (w.q : ℂ) ^ (Fintype.card n - 2 : ℤ) •
      (y + ((w.q : ℂ) ^ Fintype.card n - 1) • sphericalMean ρ y) := by
  classical
  -- The line of `z` is reached once for each hyperplane that contains neither `e_i` nor `z`.
  have : Fintype (ResField w) := Fintype.ofFinite _
  calc lineRaise i ρ (lineLower i ρ y)
    _ = ∑ ξ : n → ResField w with ξ i = 1, ∑ z : n → ResField w with ξ ⬝ᵥ z = 1,
        lineTranslate i ρ y z := by
      rw [lineRaise_eq_sum (lineLower_mem hy)]
      exact sum_congr rfl fun ξ hξ ↦ raiseCosetRep_apply_lineLower hy (mem_filter.1 hξ).2
    _ = (w.q : ℂ) ^ (Fintype.card n - 2 : ℤ) •
        (y + ∑ z : n → ResField w with z ≠ 0, lineTranslate i ρ y z) := by
      rw [sum_sum_dotProduct_eq_one_eq_smul fun _ ↦ lineTranslate_eq_self hy,
        ← Nat.card_eq_fintype_card, card_ResField]
    _ = _ := by rw [sum_lineTranslate hy]

end FixedVectors

section LineOperators

variable {E n : Type} [Field E] [NumberField E] [Fintype n] [DecidableEq n] {w : FinPlace E} {i : n}

/-- Let `W` carry a unitary representation of `GL_n` of the local field at `w`. On the vectors fixed
by the stabiliser `J_line` of the line of `e_i` modulo `w`, the operator `T⁻ = lineLower i ρ` of the
double coset of `diag (ϖ, 1, …, 1)⁻¹` is the adjoint of the operator `T⁺ = lineRaise i ρ` of the
double coset of `diag (ϖ, 1, …, 1)`. -/
theorem inner_lineRaise {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    {ρ : Representation ℂ (GL n (LocField w)) W}
    (hρ : ∀ (g : GL n (LocField w)) (x y : W), ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ) {x y : W}
    (hx : x ∈ levelSpace ρ (lineStabilizer w i)) (hy : y ∈ levelSpace ρ (lineStabilizer w i)) :
    ⟪lineRaise i ρ x, y⟫_ℂ = ⟪x, lineLower i ρ y⟫_ℂ := by
  classical
  -- The two double cosets are mutually inverse and have the same number of cosets.
  have : Fintype (ResField w) := Fintype.ofFinite _
  have h_inv : ⟪ρ (lineElement w i) x, y⟫_ℂ = ⟪x, ρ (lineElement w i)⁻¹ y⟫_ℂ := by
    rw [← hρ (lineElement w i) x, ρ.self_inv_apply]
  have h_raise : ⟪lineRaise i ρ x, y⟫_ℂ =
      #{ξ : n → ResField w | ξ i = 1} • ⟪ρ (lineElement w i) x, y⟫_ℂ := by
    rw [lineRaise_eq_sum hx, inner_sum_of_mem_doubleCoset hρ hx hy
      fun ξ hξ ↦ raiseCosetRep_mem_doubleCoset (mem_filter.1 hξ).2]
  have h_lower : ⟪lineLower i ρ y, x⟫_ℂ =
      #{z : n → ResField w | z i = 1} • ⟪ρ (lineElement w i)⁻¹ y, x⟫_ℂ := by
    rw [lineLower_eq_sum hy, inner_sum_of_mem_doubleCoset hρ hy hx
      fun z hz ↦ lowerCosetRep_mem_doubleCoset (mem_filter.1 hz).2]
  rw [h_raise, h_inv, ← inner_conj_symm x (lineLower i ρ y), h_lower, map_nsmul, inner_conj_symm]

/-! ### The support of the powers of `lineHecke` -/

variable {g h : GL n (LocField w)}

/-- The matrix `g` is integral and keeps the line of `e_i` modulo `w`, with an invertible action on
the quotient by that line. -/
structure KeepsLineMod (i : n) (g : GL n (LocField w)) : Prop where
  /-- The entries are integral. -/
  v_le_one : ∀ a b : n, v (g a b) ≤ 1
  /-- The reduction has the block shape `(∗ ∗; 0 g')` with `g'` invertible. -/
  keepsLine : KeepsLine i (g.1.map residueOrZero)

lemma KeepsLineMod.mul (hg : KeepsLineMod i g) (hh : KeepsLineMod i h) :
    KeepsLineMod i (g * h) where
  v_le_one a b := (v_matrix_mul_le hg.v_le_one hh.v_le_one a b).trans_eq (one_mul 1)
  keepsLine := by
    rw [Units.val_mul, map_residueOrZero_mul hg.v_le_one hh.v_le_one]
    exact hg.keepsLine.mul hh.keepsLine

/-- If two matrices are integral and keep the line of `e_i` modulo `w`, with invertible actions on
the quotient, then the `(i, i)` entry of their product reduces to the product of the reduced
`(i, i)` entries. -/
lemma KeepsLineMod.residue_mul_apply_self (hg : KeepsLineMod i g) (hh : KeepsLineMod i h) :
    residueOrZero ((g * h) i i) = residueOrZero (g i i) * residueOrZero (h i i) :=
  calc residueOrZero ((g * h) i i)
    _ = (g.1.map residueOrZero * h.1.map residueOrZero) i i :=
      congrFun₂ (map_residueOrZero_mul hg.v_le_one hh.v_le_one) i i
    _ = residueOrZero (g i i) * residueOrZero (h i i) := hh.keepsLine.mul_apply_self

/-- An element of the stabiliser of the line of `e_i` modulo `w` is integral and keeps this line,
with an invertible action on the quotient. -/
lemma keepsLineMod_of_mem (hg : g ∈ lineStabilizer w i) : KeepsLineMod i g where
  v_le_one := v_le_one_of_mem_localIntGL (lineStabilizer_le_localIntGL w i hg)
  keepsLine := by
    rw [← coe_reduceGL ⟨g, lineStabilizer_le_localIntGL w i hg⟩]
    exact keepsLine_of_mem_parabolic (coe_mem_lineStabilizer.1 hg)

/-- The matrix `diag (ϖ, 1, …, 1)`, with the uniformiser at the index `i`, is integral and keeps the
line of `e_i` modulo `w`, with an invertible action on the quotient. -/
lemma keepsLineMod_lineElement : KeepsLineMod i (lineElement w i) where
  v_le_one a b := by
    rw [coe_lineElement, diagonal_apply]
    split_ifs
    · exact v_uniformizer_lt_one.le
    all_goals simp
  keepsLine := by
    have h_zero : residueOrZero (0 : LocField w) = 0 := (residueOrZero_coe 0).trans (map_zero _)
    have h_one : residueOrZero (1 : LocField w) = 1 := (residueOrZero_coe 1).trans (map_one _)
    rw [coe_lineElement, diagonal_map h_zero]
    refine ⟨fun j hj ↦ diagonal_apply_ne _ hj, ?_⟩
    have h_block : (diagonal fun j : n ↦ residueOrZero (if j = i then (uniformizer w).1 else 1)
        ).toSquareBlockProp (· ≠ i) = 1 := by
      ext ⟨a, ha⟩ ⟨b, hb⟩
      simp [toSquareBlockProp_def, diagonal_apply, one_apply, ha, h_one]
    simp [h_block]

/-- An element `g` of the double coset of `diag (ϖ, 1, …, 1)` by the stabiliser of the line of
`e_i` is integral, and modulo `w` it has the shape `(0 ∗; 0 g')` with `g'` invertible. -/
lemma keepsLineMod_of_mem_doubleCoset
    (hg : g ∈ doubleCoset (lineElement w i) (lineStabilizer w i) (lineStabilizer w i)) :
    KeepsLineMod i g ∧ residueOrZero (g i i) = 0 := by
  obtain ⟨j, hj, j', hj', rfl⟩ := mem_doubleCoset.1 hg
  have h_left : KeepsLineMod i (j * lineElement w i) :=
    (keepsLineMod_of_mem hj).mul keepsLineMod_lineElement
  have h_corner : residueOrZero (lineElement w i i i) = 0 := by
    simp [coe_lineElement, residueOrZero_eq_zero]
  refine ⟨h_left.mul (keepsLineMod_of_mem hj'), ?_⟩
  rw [h_left.residue_mul_apply_self (keepsLineMod_of_mem hj'),
    (keepsLineMod_of_mem hj).residue_mul_apply_self keepsLineMod_lineElement, h_corner, mul_zero,
    zero_mul]

lemma spanOn_mono {G : Type} [Group G] {D D' : Set G} (h_sub : D ⊆ D') :
    spanOn ℂ D ≤ spanOn ℂ D' :=
  Submodule.span_mono (Set.image_mono h_sub)

variable (w i) in
/-- For `m > 0`, the `m`-th power of the element `lineHecke w i` of the group algebra, which acts as
`T⁺`, is supported on the matrices `g` such that every element of `g J_line` is integral, with `0` a
simple root of its characteristic polynomial modulo `w`. Here `J_line` is the stabiliser of the line
of `e_i` modulo `w`. -/
theorem lineHecke_pow_mem_spanOn {m : ℕ} (hm : 0 < m) : lineHecke w i ^ m ∈
    spanOn ℂ {g : GL n (LocField w) | ∀ k ∈ lineStabilizer w i, HasSimpleZero (g * k)} := by
  -- The shape `(0 ∗; 0 g')` modulo `w` is kept by products and by right translation by `J_line`.
  let D : Set (GL n (LocField w)) := {g | KeepsLineMod i g ∧ residueOrZero (g i i) = 0}
  have h_mem : lineHecke w i ∈ spanOn ℂ D :=
    spanOn_mono (fun _ ↦ keepsLineMod_of_mem_doubleCoset)
      (doubleCosetSum_mem_spanOn (isHeckeFunction_indicator_doubleCoset w i _).1)
  have h_mul : ∀ g ∈ D, ∀ h : GL n (LocField w), KeepsLineMod i h → g * h ∈ D :=
    fun g ⟨hg, hg_zero⟩ h hh ↦
      ⟨hg.mul hh, by rw [hg.residue_mul_apply_self hh, hg_zero, zero_mul]⟩
  have h_pow : lineHecke w i ^ m ∈ spanOn ℂ D := by
    induction hm with
    | refl => rwa [pow_one]
    | step _ ih =>
      rw [pow_succ]
      exact spanOn.mul ih h_mem fun g hg h ⟨hh_keeps, _⟩ ↦ h_mul g hg h hh_keeps
  refine spanOn_mono ?_ h_pow
  intro g hg k hk
  obtain ⟨h_keeps, h_zero⟩ : g * k ∈ D := h_mul g hg k (keepsLineMod_of_mem hk)
  exact ⟨h_keeps.v_le_one, h_keeps.keepsLine.rootMultiplicity_charpoly h_zero⟩

end LineOperators
end New

end
