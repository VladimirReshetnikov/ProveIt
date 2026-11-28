import Lib.GLn.SchurModule.Basic

/-!
# A basis of minor products for Borel semi-invariants over any ring, by induction on rows

Polynomials are in variables `X (a, i)`, where `a` is a row with colour `c a` and `i : ℕ` is a
column (`New.MatrixPoly`). For finitely many rows and `l = New.GL.columnWeight τ h`, the module
`New.nabla R c l` of Borel semi-invariants has a basis of products of minors that does not depend on
the ring `R`. The proof takes leading terms in one row: bordering lifts a family of minor products,
and a leading-term analysis describes the leading term of a semi-invariant.

## Main definitions and results

* `New.GL.HasLeadingTerm F γ G`: `F` is `G` times the monomial of exponent `γ` plus smaller terms;
  `New.GL.rowExpansion x` expands in row `x`.
* `New.GL.columnWeight`, `New.GL.ColouredTableau`, `New.GL.minorProduct`: the weight of a family of
  coloured columns, its fillings by rows, and the product of the minors of a filling.
* `New.GL.interlacing l`: the exponents `γ` with `γ i ≤ l i - l (i + 1)` (truncated subtraction).
  For antitone `l`, these are the `γ ≤ l` such that `l - γ` interlaces `l`.
* `New.GL.exists_bordering`: a filling that avoids `x` is lifted to one whose product of minors has,
  in the variables of row `x`, leading term `X ^ γ` times the old product.
* `New.GL.degree_rowExpansion_mem_interlacing`: the leading exponent of a Borel semi-invariant in
  the variables of one row `x` lies in `New.GL.interlacing` of its weight at the colour of `x`.
* `New.GL.HasLeadingTerm.leadingCoeff_mem_nabla`: the leading coefficient of a semi-invariant in row
  `x` is a semi-invariant in the other rows, of the weight lowered by that exponent.
* `New.GL.exists_isStdMinorFamily`: some finite family of fillings has products of minors that are
  linearly independent and span the semi-invariants of its weight over every ring, recorded as
  `New.GL.IsStdMinorFamily`.

Notions from other files:
* `New.nabla`: For a row colouring c and weight l, the module of Borel semi-invariants: polynomials
  f with f(yβ) = ∏β_{τ,ii}^{l(τ,i)} f(y) for generic upper triangular matrices β_τ, one per colour.
* `New.minor`: For an h-tuple I of rows, the polynomial determinant of the h×h matrix of variables
  in rows I and the first h columns.
* `New.GL.alternant`: For x in ℂ^N and l : ℕ → ℕ, the alternant det(x_i^{l(N−1−j)+j}), 0 ≤ i, j < N,
  if l(N) = 0, and zero otherwise.

## Relation to the literature

Known result: The standard basis theorem for Schur (dual Weyl) modules over any ring, with their
character. Here the module is the space of polynomials on matrices that are semi-invariant under a
triangular group, for several row colours at once. It lies in the span of a set of products of
minors built one row at a time rather than the semistandard tableaux, and this set is linearly
independent over every ring. For a single colour its character is given by Weyl's quotient of
alternants. Source: De Concini, Eisenbud, Procesi, Young diagrams and determinantal varieties,
Invent. Math. 56 (1980); Akin, Buchsbaum, Weyman, Schur functors and Schur complexes, Adv. Math. 44
(1982), II.2.16, II.4.11.

See also `Lib.DiscreteSeries.Character.WeylCharacterFormula`.
-/

noncomputable section

/-! ## Leading terms of products of minors and bordering -/

section Bordering

open MvPolynomial Finset MonomialOrder Finsupp Matrix Fin

namespace New.GL

variable {Φ J m R ι : Type} [DecidableEq m] [CommRing R]
  {F : ι → MvPolynomial ℕ R} {δ : ι → ℕ →₀ ℕ} {G : ι → R} {t : Finset ι} {γ : ℕ →₀ ℕ} {a : R}

/-! ### Leading terms -/

/-- The lexicographic monomial order on variables indexed by ℕ that compares exponents at the
highest index first, so that x₀ ≺ x₁ ≺ …. -/
def columnOrder : MonomialOrder ℕ := lex (σ := ℕᵒᵈ)

/-- If the exponents `γ` and `δ` agree in the columns beyond `i` and `γ i < δ i`, then `γ` is
below `δ` in `New.GL.columnOrder`. -/
lemma columnOrder_lt_of_eq_above {γ : ℕ →₀ ℕ} (i : ℕ) (δ : ℕ →₀ ℕ) (h_eq : ∀ j > i, γ j = δ j)
    (h_lt : γ i < δ i) : γ ≺[columnOrder] δ :=
  ⟨OrderDual.toDual i, h_eq, h_lt⟩

/-- No monomial of F exceeds x^γ in the order `New.GL.columnOrder`, and the coefficient of x^γ in F
is G (G = 0 is allowed). -/
abbrev HasLeadingTerm (F : MvPolynomial ℕ R) (γ : ℕ →₀ ℕ) (G : R) : Prop :=
  columnOrder.degree F ≼[columnOrder] γ ∧ F.coeff γ = G

/-- If `F` has leading term `a * x ^ γ`, then no monomial of `F` exceeds `x ^ γ`. -/
lemma HasLeadingTerm.degree_le {F : MvPolynomial ℕ R} (hF : HasLeadingTerm F γ a) :
    columnOrder.degree F ≼[columnOrder] γ :=
  hF.1

lemma HasLeadingTerm.coeff_eq {F : MvPolynomial ℕ R} (hF : HasLeadingTerm F γ a) :
    F.coeff γ = a :=
  hF.2

/-- Leading terms multiply: if `F` has leading term `a * x ^ γ` and `F'` has leading term
`a' * x ^ γ'`, then `F * F'` has leading term `(a * a') * x ^ (γ + γ')`. -/
lemma HasLeadingTerm.mul {F F' : MvPolynomial ℕ R} {γ' : ℕ →₀ ℕ} {a' : R}
    (hF : HasLeadingTerm F γ a) (hF' : HasLeadingTerm F' γ' a') :
    HasLeadingTerm (F * F') (γ + γ') (a * a') := by
  constructor
  · grw [degree_mul_le, map_add, map_add, hF.degree_le, hF'.degree_le]
  · rw [coeff_mul_of_add_of_degree_le hF.degree_le hF'.degree_le, hF.coeff_eq, hF'.coeff_eq]

lemma HasLeadingTerm.of_monomial : HasLeadingTerm (monomial γ a) γ a :=
  ⟨degree_monomial_le a, by simp⟩

/-- Leading terms of finite products: if each `F i` has leading term `G i * x ^ δ i`, then the
product of the `F i` over `t` has leading term `(∏ G i) * x ^ (∑ δ i)`. -/
lemma HasLeadingTerm.prod (h_lead : ∀ i : ι, HasLeadingTerm (F i) (δ i) (G i)) :
    HasLeadingTerm (∏ i ∈ t, F i) (∑ i ∈ t, δ i) (∏ i ∈ t, G i) := by
  induction t using Finset.cons_induction with
  | empty => simpa using of_monomial (γ := 0) (a := (1 : R))
  | cons i t hi ih => simpa only [Finset.prod_cons, Finset.sum_cons] using (h_lead i).mul ih

/-- Let each `F i` have leading term `G i * x ^ δ i`. If `δ j` exceeds every other exponent `δ i`
with `i ∈ t`, then the sum of the `F i` over `t` has leading term `G j * x ^ δ j`. The index `j`
may lie outside `t` when `G j = 0`. -/
lemma HasLeadingTerm.sum (h_lead : ∀ i : ι, HasLeadingTerm (F i) (δ i) (G i)) (j : ι)
    (h_lt : ∀ i ∈ t, i ≠ j → δ i ≺[columnOrder] δ j) (h_notMem : j ∉ t → G j = 0) :
    HasLeadingTerm (∑ i ∈ t, F i) (δ j) (G j) := by
  -- Every summand has degree at most `δ j`; all but the `j`-th have degree below `δ j`.
  have h_below (i : ι) (hi : i ∈ t) (hij : i ≠ j) :
      columnOrder.degree (F i) ≺[columnOrder] δ j :=
    (h_lead i).degree_le.trans_lt (h_lt i hi hij)
  have h_le (i : ι) (hi : i ∈ t) : columnOrder.degree (F i) ≼[columnOrder] δ j := by
    rcases eq_or_ne i j with rfl | hij
    · exact (h_lead i).degree_le
    · exact (h_below i hi hij).le
  have h_coeff : (F j).coeff (δ j) = G j := (h_lead j).coeff_eq
  have h_single : ∑ i ∈ t, (F i).coeff (δ j) = (F j).coeff (δ j) :=
    Finset.sum_eq_single j (fun i hi hij ↦ coeff_eq_zero_of_lt (h_below i hi hij))
      fun hj ↦ h_coeff.trans (h_notMem hj)
  refine ⟨degree_sum_le.trans (Finset.sup_le h_le), ?_⟩
  rw [coeff_sum, h_single, h_coeff]

/-- If each `u j` has leading term `b j` times the variable `x j` (exponent `single j 1`),
then the product of the powers `u j ^ n j` has leading term `∏ b j ^ n j` times the monomial of
exponent `n`. -/
lemma HasLeadingTerm.finsuppProd_pow {u : ℕ → MvPolynomial ℕ R} {b : ℕ → R}
    (hu_lead : ∀ j : ℕ, HasLeadingTerm (u j) (Finsupp.single j 1) (b j)) (n : ℕ →₀ ℕ) :
    HasLeadingTerm (n.prod fun j e : ℕ ↦ u j ^ e) n (n.prod fun j e : ℕ ↦ b j ^ e) := by
  have h_pow (j : ℕ) : HasLeadingTerm (u j ^ n j) (Finsupp.single j (n j)) (b j ^ n j) := by
    simpa using HasLeadingTerm.prod (t := range (n j)) fun _ ↦ hu_lead j
  have h_sum_single : ∑ j ∈ n.support, Finsupp.single j (n j) = n := n.sum_single
  simpa only [Finsupp.prod, h_sum_single] using HasLeadingTerm.prod (t := n.support) h_pow

variable [Fintype J] {c : m → Φ} {τ : J → Φ} {h : J → ℕ} {x : m} (l : ℕ →₀ ℕ)

/-! ### Columns, fillings and products of minors -/

/-- For a row x, the R-algebra isomorphism writing a polynomial in the y_{a,i} as a polynomial
in the y_{x,i}, i ∈ ℕ, over the polynomials in the other rows. -/
def rowExpansion (x : m) : MatrixPoly m R ≃ₐ[R] MvPolynomial ℕ (MatrixPoly {a // a ≠ x} R) :=
  -- split the variables into those of row `x` and the others
  (renameEquiv R (((Equiv.optionSubtypeNe x).symm.prodCongr 1).trans optionProdEquiv)).trans
    (sumAlgEquiv R ℕ ({a // a ≠ x} × ℕ))

/-- The finite set of the `γ` with `γ i ≤ l i - l (i + 1)` (truncated subtraction) for all `i`. For
antitone `l` these are the `γ ≤ l` such that `μ = l - γ` interlaces `l`: `l (i + 1) ≤ μ i ≤ l i`. -/
def interlacing : Finset (ℕ →₀ ℕ) := Icc 0 (l - l.comapDomain Nat.succ (by simp))

lemma mem_interlacing_iff {γ : ℕ →₀ ℕ} : γ ∈ interlacing l ↔ ∀ i : ℕ, γ i ≤ l i - l (i + 1) := by
  simp [interlacing, Finsupp.le_def]

/-- For finitely many columns j with colour τ_j and height h_j, the weight whose value at (τ,i)
counts the columns of colour τ with height exceeding i. -/
def columnWeight (τ : J → Φ) (h : J → ℕ) : Φ × ℕ →₀ ℕ :=
  ∑ j : J, ∑ i ∈ range (h j), Finsupp.single ((τ j : Φ), i) 1

/-- The type of assignments giving each column j an h_j-tuple of rows, all of colour τ_j. -/
abbrev ColouredTableau (c : m → Φ) (τ : J → Φ) (h : J → ℕ) : Type :=
  ∀ j : J, Fin (h j) → {a // c a = τ j}

variable (S : Type) [CommRing S] (I : ColouredTableau c τ h)

/-- For a coloured column filling I, the polynomial over S that is the product over columns j of
the minor with rows I_j on the first h_j columns. -/
def minorProduct : MatrixPoly m S := ∏ j : J, minor S fun s ↦ (I j s).1

/-- The weight `New.diagramWeight N κ` equals the weight `New.GL.columnWeight` of the family having
`κ τ h` columns of colour `τ` and height `h`, for every `τ` and `h < N τ`: its columns are the
triples `⟨τ, h, j⟩` with `j < κ τ h`, of colour `τ` and height `h`. -/
lemma diagramWeight_eq_columnWeight [Fintype Φ] (N : Φ → ℕ) (κ : Φ → ℕ → ℕ) :
    diagramWeight N κ =
      columnWeight (fun j : Σ τ : Φ, Σ h : Fin (N τ), Fin (κ τ h) ↦ j.fst)
        fun j : Σ τ : Φ, Σ h : Fin (N τ), Fin (κ τ h) ↦ (j.snd.fst : ℕ) := by
  -- `↓`: the sums over the sigma type must be split before the definitions unfold
  simp [↓Fintype.sum_sigma, diagramWeight, sum_range, columnWeight]

omit [DecidableEq m] in
/-- For an assignment I of h_j rows of colour τ_j to each column j, the product of minors
`New.GL.minorProduct` of I is a Borel semi-invariant: it lies in `New.nabla` for the weight
`New.GL.columnWeight` of τ, h. -/
lemma minorProduct_mem_nabla : minorProduct R I ∈ nabla R c (columnWeight τ h) := by
  -- each minor is a semi-invariant, and semi-invariants form a graded monoid
  rw [minorProduct, columnWeight]
  apply SetLike.prod_mem_graded
  exact fun j _ ↦ minor_mem_nabla fun s ↦ (I j s).prop

/-- Bordering one minor: take a tuple `I` of `k` rows other than `x` and append the row `x` if
`e = 1`. After `New.GL.rowExpansion x`, the new minor has leading term `X k ^ e` times the old
minor, where `X k` is the variable of row `x` in column `k`. -/
lemma hasLeadingTerm_rowExpansion_minor_border {k e : ℕ} (I : Fin k → {a : m // a ≠ x})
    (he_le_one : e ≤ 1) :
    HasLeadingTerm
      (rowExpansion x (minor S fun s : Fin (k + e) ↦ if hs : s < k then (I ⟨s, hs⟩).val else x))
      (Finsupp.single k e) (minor S I) := by
  interval_cases e
  · -- the minor does not involve row `x`
    have h_const : rowExpansion x (minor S fun s : Fin (k + 0) ↦
        if hs : s < k then (I ⟨s, hs⟩).val else x) = monomial (Finsupp.single k 0) (minor S I) := by
      simp [rowExpansion, (I _).prop, monomial_eq, minor, det_apply']
    rw [h_const]
    exact .of_monomial
  · -- Expand along the last row: column `s` contributes a cofactor times `X (x, s)`.
    let cofactor (s : Fin (k + 1)) : MatrixPoly {a // a ≠ x} S :=
      (-1) ^ (k + s.val) * det (of fun a t ↦ X (I a, (s.succAbove t).val))
    -- The variable of the last column is the largest.
    have h_lt (s : Fin (k + 1)) (hs : s ≠ last k) :
        Finsupp.single s.val 1 ≺[columnOrder] Finsupp.single k 1 := by
      grind [columnOrder_lt_of_eq_above k]
    have h_expand : rowExpansion x (minor S fun s : Fin (k + 1) ↦
        if hs : s < k then (I ⟨s, hs⟩).val else x) =
          ∑ s : Fin (k + 1), monomial (Finsupp.single s.val 1) (cofactor s) := by
      rw [minor, det_succ_row _ (last k), map_sum]
      refine sum_congr rfl fun s _ ↦ ?_
      simp [cofactor, rowExpansion, (I _).prop, monomial_eq, mul_comm, mul_left_comm,
        mul_assoc, det_apply']
    have h_last : cofactor (last k) = minor S I := by simp [cofactor, minor]
    rw [h_expand, ← h_last]
    exact .sum (δ := fun s : Fin (k + 1) ↦ Finsupp.single s.val 1) (G := cofactor)
      (fun s ↦ .of_monomial) (last k) (fun s _ ↦ h_lt s) (absurd (mem_univ (last k)))

/-- Bordering. Let `γ` lie in `interlacing` of the weight `l` of the columns at the colour of the
row `x`, that is `γ i ≤ l i - l (i + 1)` for all `i`, so `γ` is the amount by which `l` is lowered
to an interlacing weight. Then (a) there are heights `k` whose column weight is that of `h` minus
`γ` placed in colour `c x`. For every filling `I` of heights `k` by rows other than `x` there is a
filling `K` of heights `h` such that (b) over every commutative ring `R`, the expansion of
`minorProduct R K` in the variables of row `x` has no monomial above the one of exponent `γ` in
`columnOrder`, and the coefficient of that monomial is `minorProduct R I`, and (c) the entries of
`K` are those of `I` together with `degree γ` copies of `x`. -/
lemma exists_bordering (h : J → ℕ) (hγ : γ ∈ interlacing ((columnWeight τ h).curry (c x))) :
    ∃ k : J → ℕ,
      -- (a)
      columnWeight τ h = γ.mapDomain (fun i : ℕ ↦ (c x, i)) + columnWeight τ k ∧
      -- every filling `I` of heights `k` that avoids `x` has a lift `K` of heights `h` such that
      ∀ I : ColouredTableau (c ∘ ((↑) : {a : m // a ≠ x} → m)) τ k, ∃ K : ColouredTableau c τ h,
        -- (b)
        (∀ (R : Type) [CommRing R],
          HasLeadingTerm (rowExpansion x (minorProduct R K)) γ (minorProduct R I)) ∧
        -- (c)
        ∀ y : m → ℂ,
          ∏ j : J, ∏ s : Fin (h j), y (K j s) =
            y x ^ Finsupp.degree γ * ∏ j : J, ∏ s : Fin (k j), y (I j s) := by
  classical
  -- Among the columns of the colour of `x` and of height `i + 1` choose `γ i` and shorten them by
  -- one. A filling `I` of the shortened columns is lifted by putting `x` back at the end.
  let taller (i : ℕ) : Finset J := {j ∈ {j | τ j = c x} | i < h j}
  have h_weight (i : ℕ) : (columnWeight τ h).curry (c x) i = #(taller i) := by
    simp [columnWeight, taller, Finsupp.single_apply, sum_ite, ite_and]
  -- interlacing says that at least `γ i` columns of this colour have height exactly `i + 1`
  have h_count (i : ℕ) : γ i ≤ #(taller i) - #(taller (i + 1)) := by
    simpa only [h_weight] using (mem_interlacing_iff _).mp hγ i
  have h_exists_S (i : ℕ) : ∃ S ⊆ taller i \ taller (i + 1), #S = γ i :=
    exists_subset_card_eq ((h_count i).trans (le_card_sdiff (taller (i + 1)) (taller i)))
  choose S h_S_sub card_S using h_exists_S
  have h_of_mem_S {i : ℕ} {j : J} (hj : j ∈ S i) : τ j = c x ∧ h j = i + 1 := by grind
  clear hγ h_S_sub h_count h_weight taller
  -- `e j = 1` for the chosen columns and `0` for the others; `k` are the new heights.
  let e (j : J) : ℕ := if ∀ i, j ∉ S i then 0 else 1
  have h_e_le_one (j : J) : e j ≤ 1 := by grind
  obtain ⟨k, rfl⟩ : ∃ k : J → ℕ, h = k + e := le_iff_exists_add'.mp (by grind [Pi.le_def])
  -- `γ i` counts the columns chosen at height `i + 1`, which now have height `k j = i`
  have h_γ_eq : γ = ∑ j, Finsupp.single (k j) (e j) := by
    ext i
    have h_chosen (j : J) : (if j ∈ S i then 1 else 0) = Finsupp.single (k j) (e j) i := by
      grind [Pi.add_apply]
    simp [Finsupp.finsetSum_apply, ← h_chosen, card_S]
  subst h_γ_eq
  refine ⟨k, ?weights, fun I ↦
    ⟨fun j s ↦ ⟨if hs : s < k j then I j ⟨s, hs⟩ else x, ?colour⟩, fun R _ ↦ ?lead, ?entries⟩⟩
  case weights =>
    -- a chosen column loses the entry `(c x, k j)` of its weight
    have h_column (j : J) :
        ∑ i ∈ range (k j + e j), Finsupp.single (τ j, i) 1 =
          Finsupp.single (c x, k j) (e j) + ∑ i ∈ range (k j), Finsupp.single (τ j, i) 1 := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (h_e_le_one j) with h_e_zero | h_e_one
      · simp [h_e_zero]
      · have h_colour : τ j = c x := by grind
        rw [h_e_one, sum_range_succ, h_colour, add_comm]
    simp only [columnWeight, mapDomain_finsetSum, mapDomain_single, Pi.add_apply, h_column,
      sum_add_distrib]
  case colour =>
    -- the appended row `x` has the colour of its column
    grind [Pi.add_apply]
  case lead =>
    -- leading terms multiply, column by column
    simp only [minorProduct, map_prod]
    exact .prod fun j ↦ by simpa using hasLeadingTerm_rowExpansion_minor_border R
                             (fun s ↦ (I j s).val) (h_e_le_one j)
  case entries =>
    -- in each column, the lifted filling adds `e j` copies of `x`
    simp [prod_univ_add, mul_comm, prod_mul_distrib, prod_pow_eq_pow_sum]

/-! ### The recursion for alternants -/

/-- Column reduction for a matrix of powers. Let `p` be a monotone family of exponents and `i` a
row. Subtracting from each column `j + 1` the power `x i ^ (p (j + 1) - p j)` times column `j`
keeps the determinant of `(x a ^ p j)`, and turns the entry `x a ^ p (j + 1)` into `x a - x i`
times the sum of `x a ^ k * x i ^ (p (j + 1) - 1 - k)` over `p j ≤ k < p (j + 1)`. -/
lemma _root_.Matrix.det_pow_eq_det_sub_mul_geom_sum {N : ℕ} (x : Fin (N + 1) → R)
    (i : Fin (N + 1)) (p : Fin (N + 1) → ℕ) (h_mono : ∀ j : Fin N, p j.castSucc ≤ p j.succ) :
    det (of fun a j : Fin (N + 1) ↦ x a ^ p j) =
      det (of fun a : Fin (N + 1) ↦ vecCons (x a ^ p 0) fun j : Fin N ↦ (x a - x i) *
        ∑ k ∈ Ico (p j.castSucc) (p j.succ), x a ^ k * x i ^ (p j.succ - 1 - k)) := by
  refine det_eq_of_forall_col_eq_smul_add_pred (fun j ↦ x i ^ (p j.succ - p j.castSucc))
    (fun _ ↦ rfl) fun a j ↦ ?_
  simp only [of_apply, cons_val_succ, mul_geom_sum₂_Ico _ _ (h_mono j)]
  ring

/-- The branching rule for alternants. Here `alternant x l` for `x : Fin (N + 1) → ℂ` is
`det (x a ^ (l (N - j) + j))` over `0 ≤ a, j ≤ N`, or zero if `l (N + 1) ≠ 0`, and `interlacing l`
is the set of `γ` with `γ k ≤ l k - l (k + 1)` for all `k`, so that `l - γ` interlaces `l`. For
antitone `l` and an index `i`, the alternant of `l` is `(-1) ^ i * ∏ a ≠ i, (x a - x i)` times the
sum, over `γ ∈ interlacing l`, of `x i ^ |γ|` times the alternant of `l - γ` in the other `N`
variables. -/
lemma alternant_succ {N : ℕ} (hl_anti : Antitone l) (i : Fin (N + 1)) (x : Fin (N + 1) → ℂ) :
    alternant x l =
      (-1) ^ i.val * (∏ a : Fin N, (x (i.succAbove a) - x i)) *
        ∑ γ ∈ interlacing l, x i ^ Finsupp.degree γ * alternant (x ∘ i.succAbove) (l - γ) := by
  -- Column `j` has exponent `p j`. Subtract from each column but the first a power of `x i` times
  -- the column before: row `i` becomes `(x i ^ l N, 0, …, 0)` and the entry `(a, j + 1)` becomes
  -- `x a - x i` times a geometric sum. Expand along row `i`, then each geometric sum.
  -- used by `grind` in the bijection below
  have h_beyond {n : ℕ} (hn : N + 1 ≤ n) : l n ≤ l (N + 1) := hl_anti hn
  let p (j : Fin (N + 1)) : ℕ := l j.rev + j
  have h_mono (j : Fin N) : p j.castSucc ≤ p j.succ := add_le_add (hl_anti (by grind)) (by simp)
  rw [alternant, interlacing, det_pow_eq_det_sub_mul_geom_sum x i p h_mono, det_succ_row _ i]
  -- Write both sides as sums over permutations, the left side also over the exponents `g`.
  simp [p, alternant, sum_univ_succ, det_apply', prod_univ_sum, Finset.mul_sum,
    Equiv.prod_comp _ fun a ↦ x (i.succAbove a) - x i, -val_rev, prod_mul_distrib,
    prod_pow_eq_pow_sum]
  rw [univ.sum_comm, ite_sum_zero, ← sum_filter, ← sum_filter]
  -- Both sides are now sums over permutations `σ` of `Fin N`: on the left also over the exponents
  -- `g j` chosen from the geometric sums, on the right also over the interlacing `γ`.
  show ∑ g ∈ Fintype.piFinset (fun j : Fin N ↦ Ico (p j.castSucc) (p j.succ)) with l (N + 1) = 0,
      ∑ σ : Equiv.Perm (Fin N), (-1) ^ (i : ℕ) * x i ^ l N * (((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ((∏ a : Fin N, (x (i.succAbove a) - x i)) * ((∏ j : Fin N, x (i.succAbove (σ j)) ^ g j) *
          x i ^ ∑ j : Fin N, (l (j.succ.rev : ℕ) + (j : ℕ) - g j)))) =
    ∑ γ ∈ interlacing l with l N - γ N = 0,
      ∑ σ : Equiv.Perm (Fin N), ((-1) ^ (i : ℕ) * ∏ a : Fin N, (x (i.succAbove a) - x i)) *
        (x i ^ Finsupp.degree γ * (((Equiv.Perm.sign σ : ℤ) : ℂ) *
          ∏ j : Fin N, x (i.succAbove (σ j)) ^ (l (j.rev : ℕ) - γ (j.rev : ℕ) + (j : ℕ))))
  -- A choice of one exponent `g j` from each geometric sum is the same as an interlacing `γ` with
  -- `γ N = l N`: the partition `μ = l - γ` has `μ (N - 1 - j) + j = g j`.
  -- (`alternant` of `μ` vanishes unless `μ N = 0`. If `l (N + 1) ≠ 0` there is no such `γ`, and
  -- the left side is zero too.)
  clear h_mono
  let μ (g : Fin N → ℕ) (n : ℕ) : ℕ := if hn : n < N then g (rev ⟨n, hn⟩) - rev ⟨n, hn⟩ else 0
  refine sum_bij' (fun g hg ↦ onFinset (range (N + 1)) (fun n ↦ l n - μ g n) ?support)
    (fun γ _ j ↦ (l - γ) j.rev + j) ?to_mem ?inv_mem ?left_inv ?right_inv ?terms
  case support => grind
  -- the four conditions of the bijection are one computation with `μ`
  case to_mem | inv_mem | left_inv | right_inv =>
    simp [μ, interlacing, le_tsub_iff_left (hl_anti _), -val_rev, Finsupp.le_def]
    grind
  case terms =>
    simp [μ, degree_eq_weight_one, weight_apply, sum_range_succ, sum_range,
      ← rev_bijective.sum_comp (l · - _), -val_rev]
    grind

end New.GL

end Bordering

/-!
## The leading term of a semi-invariant in one row

Throughout, `f` is a Borel semi-invariant and `G * X_x ^ γ` is its leading term in the variables
`X (x, i)` of one row `x`, where `X_x ^ γ` is the monomial of exponent `γ` in these variables.
-/

section Interlacing

open MvPolynomial Finset Finsupp Algebra MonomialOrder

/-- The map `aevalTower g y` is `eval₂` with the coefficient map `g`. -/
private lemma MvPolynomial.aevalTower_apply {S R A σ : Type*} [CommSemiring S] [CommSemiring R]
    [CommSemiring A] [Algebra S R] [Algebra S A] (g : R →ₐ[S] A) (y : σ → A)
    (p : MvPolynomial σ R) : aevalTower g y p = eval₂ (g : R →+* A) y p :=
  rfl

namespace New.GL

/-- Let the exponents `n` and `γ` agree outside the columns `i` and `i + 1` and have the same sum
`n i + n (i + 1) = γ i + γ (i + 1)`, in the pointwise form that a comparison of coefficients
gives. If `n i ≤ γ i` and `n ≠ γ`, then `γ` is below `n` for `columnOrder`. -/
private lemma columnOrder_lt_of_forall_add_ite_eq {γ n : ℕ →₀ ℕ} {i : ℕ}
    (h_eq : ∀ a : ℕ, (if i + 1 = a then n i else 0) + ((if i = a then n (i + 1) else 0) + n a) =
      (if i + 1 = a then γ i else 0) + ((if i = a then γ (i + 1) else 0) + γ a))
    (h_le : n i ≤ γ i) (h_ne : n ≠ γ) : γ ≺[columnOrder] n := by
  have h_sum : n (i + 1) + n i = γ (i + 1) + γ i := by simpa using h_eq i
  have h_off (a : ℕ) (ha : a ≠ i) (ha' : a ≠ i + 1) : n a = γ a := by
    simpa [Ne.symm ha, Ne.symm ha'] using h_eq a
  -- `n i = γ i` would force `n = γ`, so `n i < γ i` and hence `γ (i + 1) < n (i + 1)`.
  have h_lt_i : n i < γ i := by
    refine h_le.lt_of_ne fun h_eq_i ↦ h_ne (Finsupp.ext fun a ↦ ?_)
    rcases eq_or_ne a i with rfl | ha
    · exact h_eq_i
    rcases eq_or_ne a (i + 1) with rfl | ha'
    · lia
    exact h_off a ha ha'
  have h_lt_succ : γ (i + 1) < n (i + 1) := by lia
  exact columnOrder_lt_of_eq_above (i + 1) n (fun a ha ↦ (h_off a (by lia) (by lia)).symm) h_lt_succ

variable {Φ m : Type} [DecidableEq m] {R : Type} [CommRing R]
  {c : m → Φ} {x : m} {l : Φ × ℕ →₀ ℕ} {f : MatrixPoly m R}

/-- Let `f` be a Borel semi-invariant of weight `l` for the row colouring `c` (`f ∈ nabla R c l`),
and let `γ` be the leading exponent of `f` in the variables `X (x, i)` of the row `x`, for the order
`columnOrder` (which compares the highest column first). Then `γ i ≤ l (c x, i) - l (c x, i + 1)`
for every column `i`, with truncated subtraction: `γ` lies in `interlacing` of the weight at the
colour of `x`. -/
lemma degree_rowExpansion_mem_interlacing (hf : f ∈ nabla R c l) :
    columnOrder.degree (rowExpansion x f) ∈ interlacing (l.curry (c x)) := by
  classical
  -- Let `v, v'` be the columns `i, i + 1` of the colour of `x`. Semi-invariance under the block
  -- `!![s, -1; 0, T]` gives `f (s v + s T v', -v) = s ^ l i * T ^ l (i + 1) * f (v + T v', v')`.
  -- On the left `T` enters only as `s T`, so no term has more `T` than `s`. On the right, if
  -- `G X_x ^ γ` is the leading term of `f` in row `x`, then `G` is a coefficient of
  -- `T ^ (l (i + 1) + γ i) * s ^ l i`.
  set γ : ℕ →₀ ℕ := columnOrder.degree (rowExpansion x f)
  suffices h_bound : ∀ i : ℕ, γ i ≤ l.curry (c x) i - l.curry (c x) (i + 1) by
    exact (mem_interlacing_iff _).mpr h_bound
  intro i
  rw [Finsupp.curry_apply, Finsupp.curry_apply]
  by_contra! h_lt : l (c x, i) - l (c x, i + 1) < γ i
  -- As `γ ≠ 0`, the polynomial `rowExpansion x f` is not zero, nor is its leading coefficient `G`.
  have hG : (rowExpansion x f).coeff γ ≠ 0 := by grind [degree_zero, coeff_degree_eq_zero_iff]
  -- Coefficients lie in `P`, polynomials in `s` and `T`: `T` is `Polynomial.X` and `s` is `.C .X`.
  -- `θ` replaces `v` by `v + T v'` in the rows other than `x`.
  let P : Type _ := Polynomial (Polynomial (MatrixPoly {a // a ≠ x} R))
  let θ : MatrixPoly {a // a ≠ x} R →ₐ[R] P :=
    aeval fun y ↦ .CC (X y) + .X * .CC (single (c x, i) (X (y.1, i + 1)) (c y.1, y.2))
  have hθ (p : MatrixPoly {a // a ≠ x} R) : (θ p).coeff 0 = .C p := by
    induction p using MvPolynomial.induction_on with
    | C r => simp [P, θ, Polynomial.algebraMap_apply]
    | add p q hp hq => rw [map_add, Polynomial.coeff_add, hp, hq, map_add]
    | mul_X p y hp =>
      have h_X : (θ (X y)).coeff 0 = .C (X y) := by simp [P, θ]
      rw [map_mul, Polynomial.mul_coeff_zero, hp, h_X, map_mul]
  -- `Ψ` does the same in row `x`, at `v = 0` and `v' = X i * X (i + 1)`.
  let Ψ : MatrixPoly m R →ₐ[R] MvPolynomial ℕ P :=
    (aevalTower ((mapAlgHom θ).comp
        (algHom R (MatrixPoly {a // a ≠ x} R) (MvPolynomial ℕ (MatrixPoly {a // a ≠ x} R)))) fun j ↦
        (C Polynomial.X * X (i + 1)) ^ single i 1 j * X i ^ single (i + 1) 1 j * X j).comp
      (rowExpansion x).toAlgHom
  -- `b` is the identity matrix but for the block `!![s, -1; 0, T]`.
  let b : Φ × ℕ × ℕ → MvPolynomial ℕ P := fun (τ, j, k) ↦
    single j (C (.C .X ^ single (c x, i) 1 (τ, j) * .X ^ single (c x, i + 1) 1 (τ, j))) k -
      single (c x, i) (single (j + 1) 1 k) (τ, j)
  -- `Ψ` sends `X_x ^ γ` to `T ^ γ i` times the monomial of exponent `δ`.
  let δ : ℕ →₀ ℕ := single (i + 1) (γ i) + (single i (γ (i + 1)) + γ)
  -- Left side: the substitution factors through `scale : T ↦ s T`. An entry of `y b` (`y = Ψ ∘ X`)
  -- is `scale` of the entry of `y` plus the value at `T = 0` of the entry of `y b - y`.
  let scale : P →ₐ[R] P :=
    .restrictScalars R (Polynomial.aeval (R := Polynomial (MatrixPoly {a // a ≠ x} R)) (.C .X * .X))
  have h_factor : aeval (borelMul c b (Ψ ∘ X)) = (mapAlgHom scale).comp
      (aeval (mapAlgHom (Polynomial.aeval 0) ∘ (borelMul c b (Ψ ∘ X) - Ψ ∘ X) + Ψ ∘ X)) := by
    refine algHom_ext fun ⟨y, j⟩ ↦ ?_
    -- Casework on the row `y` and on the column `j` against `i` and `i + 1`; each case is a ring
    -- identity.
    by_cases hy : y = x
    · simp +zetaDelta [rowExpansion, ite_and, mul_sub, hy, single_apply, algHom, mul_assoc,
        borelMul]
      split_ifs <;> subst_vars <;> simp_all [sub_eq_zero, mul_assoc] <;> ring
    · simp +zetaDelta [rowExpansion, ite_and, mul_sub, hy, single_apply, algHom, mul_assoc,
        borelMul]
      split_ifs <;> subst_vars <;> simp_all
      ring
  -- After `T ↦ s T` the coefficient of `T ^ a` is divisible by `s ^ a`.
  have h_scale (p : P) {a k : ℕ} (hk : k < a) : ((scale p).coeff a).coeff k = 0 := by
    simp [P, scale, ← Polynomial.comp_eq_aeval, Polynomial.coeff_mul_X_pow', hk.not_ge]
  have h_left : (((aeval (borelMul c b (Ψ ∘ X)) f).coeff δ).coeff (l (c x, i + 1) + γ i)).coeff
      (l (c x, i)) = 0 := by
    have h_deg_lt : l (c x, i) < l (c x, i + 1) + γ i := by lia
    rw [h_factor, AlgHom.comp_apply, mapAlgHom_apply, coeff_map]
    exact h_scale _ h_deg_lt
  -- Right side: the weight factor, and the coefficient of `T ^ γ i` at `δ` in `Ψ f`.
  have h_weight :
      (l.prod fun p k ↦ b (p.1, p.2, p.2) ^ k) = C (.C .X ^ l (c x, i) * .X ^ l (c x, i + 1)) := by
    -- The flags stop `simp` from splitting the powers `s ^ [p = (c x, i)]` into cases, and from
    -- rewriting `C (a ^ n)` as `C a ^ n`.
    simp [b, prod_mul_distrib, -pow_ite, -Prod.mk.injEq, prod_pow_eq_pow_sum, ↓if_mem_support, prod,
      single_apply, mul_pow, ← pow_mul, -C_pow]
  have h_top : (((Ψ f).coeff δ).coeff (γ i)).coeff 0 = (rowExpansion x f).coeff γ := by
    -- Expand `f` along row `x` and apply `Ψ` term by term; only the term of `γ` contributes.
    have h_expand : (Ψ f).coeff δ = ∑ n ∈ (rowExpansion x f).support,
        θ ((rowExpansion x f).coeff n) *
          (.X ^ n i * (X (i + 1) ^ n i * (X i ^ n (i + 1) * monomial n 1) : MvPolynomial ℕ P).coeff
            δ) := by
      rw [AlgHom.comp_apply, MvPolynomial.aevalTower_apply, eval₂_eq]
      -- Flags as in `h_weight`; `-map_aeval` keeps `θ` applied to the coefficients.
      simp [prod_mul_distrib, -pow_ite, prod_pow_eq_pow_sum, -map_aeval, ↓if_mem_support,
        algHom, single_apply, mul_pow, ← map_pow, mul_assoc, ← pow_mul, ← map_prod, -C_pow]
    rw [h_expand, Polynomial.finsetSum_coeff, Polynomial.finsetSum_coeff, Finset.sum_eq_single γ]
    · simp [P, δ, hθ, X_pow_eq_monomial, Polynomial.coeff_mul_X_pow']
    · -- Another exponent `n` reaching `δ` with `n i ≤ γ i` has `n i < γ i`, hence
      -- `γ (i + 1) < n (i + 1)` and equal entries beyond: it exceeds the leading exponent `γ`.
      intro n hn hne
      have h_not_lt : ¬ γ ≺[columnOrder] n := fun h_lt ↦
        MvPolynomial.mem_support_iff.mp hn (coeff_eq_zero_of_lt h_lt)
      -- The term of `n` is nonzero only if `n` reaches `δ` with `n i ≤ γ i`.
      suffices h_vanish : (∀ a : ℕ,
          (if i + 1 = a then n i else 0) + ((if i = a then n (i + 1) else 0) + n a) =
            (if i + 1 = a then γ i else 0) + ((if i = a then γ (i + 1) else 0) + γ a)) →
          n i ≤ γ i → ((θ ((rowExpansion x f).coeff n)).coeff (γ i - n i)).coeff 0 = 0 by
        simpa [P, δ, X_pow_eq_monomial, Polynomial.coeff_mul_X_pow', Finsupp.ext_iff,
          apply_ite Polynomial.coeff, DFunLike.ite_apply, single_apply, ite_apply] using h_vanish
      intro h_shape h_le
      exact absurd (columnOrder_lt_of_forall_add_ite_eq h_shape h_le hne) h_not_lt
    · intro hγ
      exact absurd (MvPolynomial.mem_support_iff.mpr hG) hγ
  -- By semi-invariance the coefficient in `h_left` is the one in `h_top`, so `G = 0`.
  apply hG
  rw [← h_top, ← h_left, mem_nabla.mp hf (MvPolynomial ℕ P) b (Ψ ∘ X), h_weight, ← aeval_unique]
  -- `← map_pow` gathers powers inside `C`, which `C_pow` would undo.
  simp [P, Polynomial.coeff_X_pow_mul', ← map_pow, mul_assoc, -C_pow]

/-- Let `γ` be the leading exponent of `f` in the variables of the row `x` (for `columnOrder`, the
lexicographic order that compares exponents at the highest column first), and let `f` be a Borel
semi-invariant of weight `γ + l`, where `γ` is placed at the colour `c x` (`γ.mapDomain (c x, ·)`).
Then the leading coefficient `G` of `f` in the row `x`, a polynomial in the other rows, is a Borel
semi-invariant of weight `l` for the colouring `c` restricted to the rows other than `x`. -/
lemma HasLeadingTerm.leadingCoeff_mem_nabla
    (hf : f ∈ nabla R c
      ((columnOrder.degree (rowExpansion x f)).mapDomain (fun i : ℕ ↦ (c x, i)) + l)) :
    columnOrder.leadingCoeff (rowExpansion x f) ∈ nabla R (c ∘ (↑)) l := by
  -- Let `G X_x ^ γ` be the leading term of `f` in row `x`. Compare the coefficients of `X_x ^ γ`
  -- in `f (y β) = ∏ β ^ (γ + l) * f y` for a generic upper triangular `β`. As `(y β) (x, j)` is
  -- `β j j * y (x, j)` plus smaller terms, the left one is `G (y β) * ∏ β j j ^ γ j`; the factor
  -- `∏ β j j ^ γ j` cancels.
  set γ : ℕ →₀ ℕ := columnOrder.degree (rowExpansion x f)
  let A : Type _ := MatrixPoly {a // a ≠ x} (MvPolynomial (Φ × ℕ × ℕ) R)
  let β : Φ × ℕ × ℕ → A := C ∘ X
  -- `ρ` substitutes `y β` in the rows other than `x`; `u j` is the entry `(x, j)` of `y β`.
  let ρ : MatrixPoly {a // a ≠ x} R →ₐ[R] A := aeval (borelMul (c ∘ (↑)) β X)
  let u (j : ℕ) : MvPolynomial ℕ A := borelMul c (C ∘ β) (fun p ↦ X p.2) (x, j)
  have hu_lead (j : ℕ) : HasLeadingTerm (u j) (single j 1) (β (c x, j, j)) := by
    -- `u j` is the sum of the `X i * C (β (c x, i, j))` over `i ≤ j`.
    have h_term (i : ℕ) :
        HasLeadingTerm (X i * C (β (c x, i, j))) (single i 1) (β (c x, i, j)) := by
      rw [X, C_apply, monomial_mul_monomial, add_zero, one_mul]
      exact of_monomial
    have h_lt : ∀ i ∈ range (j + 1), i ≠ j → single i 1 ≺[columnOrder] single j 1 := by
      grind [columnOrder_lt_of_eq_above j]
    simpa only [u, borelMul, Function.comp_apply] using
      sum (t := range (j + 1)) h_term j h_lt (absurd (self_mem_range_succ j))
  -- `subst` substitutes `y β` in `f` and expands along row `x`; by the definitions of
  -- `aevalTower` and `eval₂`, `subst f` is a sum over the exponents of `f` in row `x`.
  let subst : MatrixPoly m R →ₐ[R] MvPolynomial ℕ A :=
    (aevalTower ((algHom R A (MvPolynomial ℕ A)).comp ρ) u).comp (rowExpansion x).toAlgHom
  have h_eval : subst f = ∑ n ∈ (rowExpansion x f).support,
      C (ρ ((rowExpansion x f).coeff n)) * n.prod fun j e ↦ u j ^ e :=
    rfl
  -- In this sum the term of `γ` leads.
  have h_lead : HasLeadingTerm (subst f) γ
      (ρ ((rowExpansion x f).coeff γ) * γ.prod fun j e ↦ β (c x, j, j) ^ e) := by
    rw [h_eval]
    refine sum (δ := fun n ↦ n)
      (G := fun n ↦ ρ ((rowExpansion x f).coeff n) * n.prod _) (fun n ↦ ?_) γ
      (fun n hn hne ↦ ?_) fun hγ ↦ ?_
    · simpa using mul (of_monomial (γ := 0)) (finsuppProd_pow hu_lead n)
    · exact lt_of_le_of_ne (columnOrder.le_degree hn) (columnOrder.toSyn.injective.ne hne)
    · simp [MvPolynomial.notMem_support_iff.mp hγ]
  -- The semi-invariance of `f`, with both sides expanded along row `x`; `W` is the weight factor.
  let Ψ : MatrixPoly m R →ₐ[R] MvPolynomial ℕ A :=
    (mapAlgHom (aeval X)).comp (rowExpansion x).toAlgHom
  let W : MvPolynomial ℕ A := (γ.mapDomain (fun i : ℕ ↦ (c x, i)) + l).prod
    fun (p : Φ × ℕ) (k : ℕ) ↦ (C ∘ β) (p.1, p.2, p.2) ^ k
  have h_subst : aeval (borelMul c (C ∘ β) (Ψ ∘ X)) = subst := by
    refine algHom_ext fun ⟨y, j⟩ ↦ ?_
    by_cases hy : y = x <;> simp [rowExpansion, Ψ, ρ, u, subst, hy, borelMul, algHom]
  have h_semi : subst f = W * Ψ f := by
    have h_nabla : aeval (borelMul c (C ∘ β) (Ψ ∘ X)) f = W * aeval (Ψ ∘ X) f :=
      mem_nabla.mp hf (MvPolynomial ℕ A) (C ∘ β) (Ψ ∘ X)
    rwa [← aeval_unique, h_subst] at h_nabla
  -- The factor to cancel is a monomial in the generic entries, hence regular.
  have h_reg : IsRegular (γ.prod fun j e ↦ β (c x, j, j) ^ e) := by
    simpa [β, Finsupp.prod, ← map_pow, ← map_prod, -C_pow] using .monomial (.prod (by simp))
  -- Membership in `nabla` is by definition the identity `ρ G = ∏ β ^ l * G` for the generic `β`.
  -- Multiplied by the regular factor, its left side is the coefficient at `γ` of `subst f` (by
  -- `h_lead`), and the right side that of `W * Ψ f`.
  have h_rhs : (W * Ψ f).coeff γ =
      ((l.prod fun (p : Φ × ℕ) (k : ℕ) ↦ (X (p.1, p.2, p.2) : MvPolynomial (Φ × ℕ × ℕ) R) ^ k) •
        (aeval X : MatrixPoly {a // a ≠ x} R →ₐ[R] A)
          (columnOrder.leadingCoeff (rowExpansion x f))) *
        γ.prod fun j e ↦ β (c x, j, j) ^ e := by
    -- `W` is a constant, so it comes out of the coefficient; it is the product of the factors for
    -- `l` and for `γ`. `↓` splits this product before the definitions unfold.
    simp [A, β, Ψ, γ, W, leadingCoeff, ↓prod_add_index', pow_add, ↓prod_mapDomain_index,
      ← map_pow, Finsupp.prod, ← map_prod, mul_assoc, coeff_map, -C_pow, Algebra.smul_def,
      MvPolynomial.algebraMap_eq]
    ring
  rw [← h_semi, h_lead.coeff_eq] at h_rhs
  exact h_reg.right h_rhs

end New.GL

end Interlacing

/-!
## The basis theorem and the character identity

The proof of `New.GL.exists_isStdMinorFamily` is an induction on the number of rows by leading
terms in one row.
-/

section MinorBasis

open MvPolynomial Finset MonomialOrder Submodule Finsupp Nat

namespace New.GL

/-- A standard family of fillings `I` for rows coloured by `c` and columns `j` of colour `τ j` and
height `h j`: each `I i` (a `ColouredTableau`) gives column `j` an `h j`-tuple of rows of colour
`τ j`; `minorProduct R (I i)` is the product of the minors on these rows and the first `h j`
columns. -/
structure IsStdMinorFamily {Φ J m ι : Type} [Fintype m] [Fintype J] [Fintype ι]
    {c : m → Φ} {τ : J → Φ} {h : J → ℕ} (I : ι → ColouredTableau c τ h) : Prop where
  /-- Over every commutative ring the products of minors are linearly independent. -/
  linearIndependent (R : Type) [CommRing R] :
    LinearIndependent R fun i : ι ↦ minorProduct R (I i)
  /-- Over every commutative ring the span of the products of minors contains the
  semi-invariants of weight `columnWeight τ h`. -/
  nabla_le_span (R : Type) [CommRing R] :
    nabla R c (columnWeight τ h) ≤ span R (Set.range fun i : ι ↦ minorProduct R (I i))
  /-- If `t` is the only colour and `e` enumerates the rows, then the sum over the fillings of the
  products of the `x a` over their entries `a`, times the alternant of the zero weight, is the
  alternant of the weight `columnWeight τ h (t, ·)`. -/
  character [Subsingleton Φ] (t : Φ) (N : ℕ) (e : Fin N ≃ m) (x : m → ℂ) :
    (∑ i : ι, ∏ j : J, ∏ s : Fin (h j), x (I i j s)) * alternant (x ∘ e) 0 =
      alternant (x ∘ e) fun k : ℕ ↦ columnWeight τ h (t, k)

section LeadingTerms

variable {Φ m R : Type} [DecidableEq m] [CommRing R] {y : m}

/-- If `p i` has leading term `q i` times the monomial of exponent `γ` in the row `y` for every `i`,
then a combination of the `p i` has as leading term the same combination of the `q i`, times that
monomial. Here `HasLeadingTerm F γ G` says that no exponent of `F` exceeds `γ` for `columnOrder`
(lexicographic, comparing exponents at the highest column first) and that the coefficient of the
monomial of exponent `γ` is `G`; `rowExpansion y` writes a polynomial as one in the variables of the
row `y` over the polynomials in the other rows. -/
lemma HasLeadingTerm.rowExpansion_combination {ι : Type} {γ : ℕ →₀ ℕ} {p : ι → MatrixPoly m R}
    {q : ι → MatrixPoly {a : m // a ≠ y} R}
    (h_lead : ∀ i : ι, HasLeadingTerm (rowExpansion y (p i)) γ (q i)) (a : ι →₀ R) :
    HasLeadingTerm (rowExpansion y (a.sum fun (i : ι) (r : R) ↦ r • p i)) γ
      (a.sum fun (i : ι) (r : R) ↦ r • q i) := by
  have h_above (i : ι) (δ : ℕ →₀ ℕ) (hδ : γ ≺[columnOrder] δ) :
      (rowExpansion y (p i)).coeff δ = 0 :=
    coeff_eq_zero_of_lt ((h_lead i).degree_le.trans_lt hδ)
  refine ⟨?_, ?_⟩
  · -- No exponent above `γ` occurs in any `p i`, hence none in the combination.
    simp +contextual [Finsupp.sum, degree_le_iff, not_imp_comm, h_above]
  · simp [Finsupp.sum, fun i ↦ (h_lead i).coeff_eq]

/-- Polynomials `p γ i` with leading terms `q γ i` times the monomial of exponent `γ` in the row
`y` (`HasLeadingTerm`), for distinct exponents `γ` from a finite set `Γ`, are linearly independent
if for each exponent `γ` the coefficients `q γ i` are. -/
lemma linearIndependent_of_hasLeadingTerm {Γ : Finset (ℕ →₀ ℕ)} {ι : Γ → Type}
    {p : ∀ γ : Γ, ι γ → MatrixPoly m R} {q : ∀ γ : Γ, ι γ → MatrixPoly {a : m // a ≠ y} R}
    (h_lead : ∀ (γ : Γ) (i : ι γ), HasLeadingTerm (rowExpansion y (p γ i)) γ (q γ i))
    (h_indep : ∀ γ : Γ, LinearIndependent R (q γ)) :
    LinearIndependent R fun i : Σ γ : Γ, ι γ ↦ p i.fst i.snd := by
  -- In a relation `a ≠ 0` take the largest `γ` that occurs. The coefficient of that monomial is a
  -- relation among the `q γ i`, so the `γ`-part of `a` vanishes.
  refine linearIndependent_iff.mpr fun a ha ↦ by_contra fun ha_ne ↦ ?_
  have h_nonempty : a.splitSupport.Nonempty := by simpa [splitSupport] using ha_ne
  obtain ⟨γ, hγ, hγ_max⟩ :=
    a.splitSupport.exists_max_image (fun δ ↦ columnOrder.toSyn δ.val) h_nonempty
  have h_lt : ∀ δ ∈ a.splitSupport, δ ≠ γ → δ.val ≺[columnOrder] γ.val := fun δ hδ h_ne ↦
    lt_of_le_of_ne (hγ_max δ hδ) fun h_eq ↦ h_ne (Subtype.ext (columnOrder.toSyn.injective h_eq))
  have h_top : HasLeadingTerm
      (∑ δ ∈ a.splitSupport, rowExpansion y ((a.split δ).sum fun i r ↦ r • p δ i))
      γ ((a.split γ).sum fun i r ↦ r • q γ i) :=
    .sum (fun δ ↦ .rowExpansion_combination (h_lead δ) (a.split δ)) γ h_lt (absurd hγ)
  have h_rel : (a.split γ).sum (fun i r ↦ r • q γ i) = 0 := by
    rw [linearCombination_apply, sigma_sum] at ha
    simp [← h_top.coeff_eq, ← map_sum, ha]
  exact (mem_splitSupport_iff_nonzero a γ).mp hγ (linearIndependent_iff.mp (h_indep γ) _ h_rel)

/-- Let `γ` run over the exponents interlacing the weight `l` at the colour of the row `y`, and let
`l' γ` be `l` lowered by `γ`. Borel semi-invariants (`nabla`) `p γ i` of weight `l` with leading
terms `q γ i` times the monomial of exponent `γ` in the row `y` span all semi-invariants of weight
`l`, if for each `γ` the span of the `q γ i` contains the semi-invariants of weight `l' γ` in the
other rows. -/
lemma nabla_le_span_of_hasLeadingTerm {c : m → Φ} {l : Φ × ℕ →₀ ℕ}
    {ι : interlacing (l.curry (c y)) → Type} {l' : interlacing (l.curry (c y)) → Φ × ℕ →₀ ℕ}
    {p : ∀ γ : interlacing (l.curry (c y)), ι γ → MatrixPoly m R}
    {q : ∀ γ : interlacing (l.curry (c y)), ι γ → MatrixPoly {a : m // a ≠ y} R}
    (h_weight : ∀ γ : interlacing (l.curry (c y)),
      l = γ.val.mapDomain (fun k : ℕ ↦ (c y, k)) + l' γ)
    (h_mem : ∀ (γ : interlacing (l.curry (c y))) (i : ι γ), p γ i ∈ nabla R c l)
    (h_lead : ∀ (γ : interlacing (l.curry (c y))) (i : ι γ),
      HasLeadingTerm (rowExpansion y (p γ i)) γ (q γ i))
    (h_span : ∀ γ : interlacing (l.curry (c y)),
      nabla R (fun a : {a : m // a ≠ y} ↦ c a) (l' γ) ≤ span R (Set.range (q γ))) :
    nabla R c l ≤
      span R (Set.range fun i : Σ γ : interlacing (l.curry (c y)), ι γ ↦ p i.fst i.snd) := by
  -- Induction on the leading exponent of `f` in the variables of row `y`.
  intro f
  induction f using (wellFounded_lt.onFun
    (f := fun f ↦ columnOrder.toSyn (columnOrder.degree (rowExpansion y f)))).induction with
  | h f ih =>
    intro hf
    -- The leading exponent `γ` interlaces, and the leading coefficient is a semi-invariant for
    -- the other rows, hence a combination `a` of the `q γ i`.
    let γ : interlacing (l.curry (c y)) :=
      ⟨columnOrder.degree (rowExpansion y f), degree_rowExpansion_mem_interlacing hf⟩
    have h_coeff_mem : columnOrder.leadingCoeff (rowExpansion y f) ∈
        nabla R (fun a : {a : m // a ≠ y} ↦ c a) (l' γ) :=
      HasLeadingTerm.leadingCoeff_mem_nabla (by rwa [← h_weight γ])
    obtain ⟨a, ha⟩ : ∃ a : ι γ →₀ R,
        (a.sum fun i r ↦ r • q γ i) = columnOrder.leadingCoeff (rowExpansion y f) :=
      mem_span_range_iff_exists_finsupp.mp (h_span γ h_coeff_mem)
    -- The same combination `g` of the `p γ i` has the same leading term as `f`.
    let g : MatrixPoly m R := a.sum fun i r ↦ r • p γ i
    have hg_span :
        g ∈ span R (Set.range fun i : Σ δ : interlacing (l.curry (c y)), ι δ ↦ p i.fst i.snd) :=
      mem_span_range_iff_exists_finsupp.mpr
        ⟨a.mapDomain (Sigma.mk γ), sum_mapDomain_index_inj sigma_mk_injective⟩
    have hg_mem : g ∈ nabla R c l := sum_mem fun i _ ↦ smul_mem _ _ (h_mem γ i)
    have hg_lead :
        HasLeadingTerm (rowExpansion y g) γ (columnOrder.leadingCoeff (rowExpansion y f)) := by
      rw [← ha]
      exact .rowExpansion_combination (h_lead γ) a
    -- So `f - g` has a smaller leading exponent or is zero.
    have h_le : columnOrder.degree (rowExpansion y (f - g)) ≼[columnOrder] γ.val := by
      rw [map_sub]
      exact degree_sub_le.trans (sup_le le_rfl hg_lead.degree_le)
    have h_coeff : (rowExpansion y (f - g)).coeff γ = 0 := by
      rw [map_sub, coeff_sub, hg_lead.coeff_eq]
      exact sub_self _
    refine (sub_mem_iff_left _ hg_span).mp ?_
    rcases h_le.lt_or_eq with h_lt | h_eq
    · exact ih (f - g) h_lt (sub_mem hf hg_mem)
    · -- The leading coefficient of `f - g` vanishes, so `f - g = 0`.
      rw [← columnOrder.toSyn.injective h_eq, coeff_degree_eq_zero_iff,
        EmbeddingLike.map_eq_zero_iff] at h_coeff
      simp [h_coeff]

end LeadingTerms

/-- At each colour `t` the number of columns of height above `k` does not increase with `k`. -/
lemma antitone_columnWeight_curry {Φ J : Type} [Fintype J] (τ : J → Φ) (h : J → ℕ) (t : Φ) :
    Antitone ((columnWeight τ h).curry t) := by
  classical
  have h_count (k : ℕ) : (columnWeight τ h).curry t k = #{j : J | τ j = t ∧ k < h j} := by
    simp [columnWeight, card_filter, ite_and, single_apply]
  intro a b hab
  rw [h_count, h_count]
  -- A column of height above `b` also has height above any `a ≤ b`.
  gcongr

/-- Rows `m` are coloured by `c`; column `j : J` has colour `τ j` and height `h j`, and a
`ColouredTableau c τ h` gives it an `h j`-tuple of rows of colour `τ j`. With no rows there is a
standard family (`IsStdMinorFamily`) of these: the one empty filling if all heights are zero, and
the empty family otherwise. -/
lemma exists_isStdMinorFamily_of_isEmpty {Φ J m : Type} [Fintype m] [IsEmpty m] [Fintype J]
    (c : m → Φ) (τ : J → Φ) (h : J → ℕ) :
    ∃ (ι : Type) (_ : Fintype ι) (I : ι → ColouredTableau c τ h), IsStdMinorFamily I := by
  -- Polynomials are constants, and an enumeration `Fin N ≃ m` forces `N = 0`.
  rcases eq_or_ne h 0 with rfl | h_ne
  · refine ⟨Unit, inferInstance, nofun, ⟨?indep, ?span, ?character⟩⟩
    case indep =>
      intro R _
      simp [Fintype.linearIndependent_iff, minorProduct, minor, ← C_mul', Unique.forall_iff]
    case span =>
      intro R _ f _
      rw [f.eq_C_of_isEmpty]
      simp [minorProduct, minor, ← one_eq_span]
    case character =>
      intro _ t N e x
      obtain rfl : N = 0 := by simpa using Fintype.card_congr e
      simp [alternant, columnWeight, univ_eq_empty]
  · have h_sum : ∑ j, h j ≠ 0 := by simpa using Function.ne_iff.mp h_ne
    refine ⟨Empty, inferInstance, nofun,
      fun R _ ↦ linearIndependent_empty_type, fun R _ f hf ↦ ?_, fun t N e x ↦ ?_⟩
    · -- The weight is not zero, so semi-invariance for the zero matrix kills every constant.
      obtain ⟨r, rfl⟩ : ∃ r : R, f = C r := ⟨f.coeff 0, f.eq_C_of_isEmpty⟩
      have h_semi : r = ((columnWeight τ h).prod fun (p : Φ × ℕ) (k : ℕ) ↦ (0 : R) ^ k) * r := by
        simpa using mem_nabla.mp hf R 0 0
      have h_prod_zero : ((columnWeight τ h).prod fun (p : Φ × ℕ) (k : ℕ) ↦ (0 : R) ^ k) = 0 := by
        simp [columnWeight, pow_add, ← prod_finsetSum_index, prod_pow_eq_pow_sum, h_sum]
      have h_r : r = 0 := by rwa [h_prod_zero, zero_mul] at h_semi
      simp [h_r]
    · obtain rfl : N = 0 := by simpa using Fintype.card_congr e
      simpa [alternant, columnWeight, univ_eq_empty, Subsingleton.elim _ t, single_apply] using
        Function.ne_iff.mp h_ne

/-- Take finitely many rows coloured by `c`, and finitely many columns `j` of colour `τ j` and
height `h j`. Then there is a finite type `ι` and a family `I` of fillings indexed by it that is
standard in the sense of `IsStdMinorFamily`. Each `I i` gives column `j` an `h j`-tuple of rows of
colour `τ j`, and has minor product `minorProduct R (I i)`: the product of the minors on these rows
and the first `h j` columns.

This is an existence form of the standard basis theorem for Schur modules (Akin–Buchsbaum–Weyman),
stated for products of minors with coloured rows; the index type is not identified with the
semistandard tableaux. -/
lemma exists_isStdMinorFamily {Φ J m : Type} [Fintype m] [Fintype J] (c : m → Φ)
    (τ : J → Φ) (h : J → ℕ) :
    ∃ (ι : Type) (_ : Fintype ι) (I : ι → ColouredTableau c τ h), IsStdMinorFamily I := by
  classical
  -- Induction on the number of rows. Fix a row `y` and expand polynomials in its variables. For
  -- each exponent `γ` interlacing the weight, take the family for the other rows and the weight
  -- lowered by `γ`, and lift its members by `exists_bordering`; the lifts have leading terms `y^γ`
  -- times the smaller products, which gives independence and spanning.
  induction h_card : Nat.card m using Nat.strongRec generalizing m h with | ind n ih => ?_
  rcases isEmpty_or_nonempty m with hm | ⟨⟨y⟩⟩
  · exact exists_isStdMinorFamily_of_isEmpty c τ h
  -- For each `γ`, the heights `k γ` give the weight lowered by `γ` (`h_weight`), and `lift γ`
  -- borders the fillings that avoid `y` (`h_lift`, `h_monomial`), by `exists_bordering`.
  have h_border : ∀ γ : interlacing ((columnWeight τ h).curry (c y)), ∃ k : J → ℕ,
      columnWeight τ h = γ.val.mapDomain (fun i : ℕ ↦ (c y, i)) + columnWeight τ k ∧
      ∀ I : ColouredTableau (c ∘ (↑) : {a : m // a ≠ y} → Φ) τ k, ∃ K : ColouredTableau c τ h,
        (∀ (R : Type) [CommRing R],
          HasLeadingTerm (rowExpansion y (minorProduct R K)) γ (minorProduct R I)) ∧
        ∀ z : m → ℂ, ∏ j : J, ∏ s : Fin (h j), z (K j s) =
          z y ^ Finsupp.degree γ.val * ∏ j : J, ∏ s : Fin (k j), z (I j s) :=
    fun γ ↦ exists_bordering h γ.prop
  choose k h_weight lift h_lift h_monomial using h_border
  -- The induction hypothesis: standard families `I γ` for the other rows.
  have h_fewer : Nat.card {a : m // a ≠ y} < n :=
    h_card.subst (Finite.card_subtype_lt (x := y) (not_not_intro rfl))
  have h_family : ∀ γ : interlacing ((columnWeight τ h).curry (c y)),
      ∃ (ι : Type) (_ : Fintype ι)
        (I : ι → ColouredTableau (c ∘ (↑) : {a : m // a ≠ y} → Φ) τ (k γ)), IsStdMinorFamily I :=
    fun γ ↦ ih _ h_fewer (c ∘ (↑) : {a : m // a ≠ y} → Φ) (k γ) rfl
  choose ι hι_fintype I hI using h_family
  refine ⟨Sigma ι, inferInstance, fun i ↦ lift i.fst (I i.fst i.snd), fun R _ ↦ ?_,
    fun R _ ↦ ?_, ?_⟩
  · exact linearIndependent_of_hasLeadingTerm (p := fun γ i ↦ minorProduct R (lift γ (I γ i)))
      (fun γ i ↦ h_lift γ (I γ i) R) fun γ ↦ (hI γ).linearIndependent R
  · exact nabla_le_span_of_hasLeadingTerm (p := fun γ i ↦ minorProduct R (lift γ (I γ i)))
      h_weight (fun γ i ↦ minorProduct_mem_nabla (lift γ (I γ i)))
      (fun γ i ↦ h_lift γ (I γ i) R) fun γ ↦ (hI γ).nabla_le_span R
  · -- The character: both sides obey the same recursion `alternant_succ` in the row `y`.
    intro _ t N e x
    rcases N with _ | N
    · exact nomatch e.symm y
    have h_only : interlacing 0 = {0} := by simp [interlacing]
    obtain rfl : t = c y := Subsingleton.elim t (c y)
    -- Write both weights as finitely supported functions, the form that `alternant_succ` takes.
    change _ * alternant (x ∘ e) ⇑(0 : ℕ →₀ ℕ) =
      alternant (x ∘ e) ⇑((columnWeight τ h).curry (c y))
    -- Expand both alternants at the index of `y`; the common factor `± ∏ (x a - x y)` cancels and
    -- the two sums over `γ` are compared term by term.
    rw [alternant_succ _ (antitone_columnWeight_curry τ h (c y)) (e.symm y),
      ← (interlacing _).sum_coe_sort, alternant_succ 0 antitone_const (e.symm y),
      h_only, mul_left_comm, Fintype.sum_sigma, univ.sum_mul]
    congr with γ
    -- For each `γ` use the identity for the other rows, enumerated by `e` with `y` left out.
    let e' : Fin N ≃ {a : m // a ≠ y} :=
      .optionSubtype _ ⟨(finSuccEquiv' (e.symm y)).symm.trans e, e.apply_symm_apply y⟩
    have h_rest : (∑ i : ι γ, ∏ j : J, ∏ s : Fin (k γ j), x (I γ i j s)) *
        alternant (fun i : Fin N ↦ x (e' i)) 0 =
          alternant (fun i : Fin N ↦ x (e' i)) fun n : ℕ ↦ columnWeight τ (k γ) (c y, n) :=
      (hI γ).character (c y) N e' fun a ↦ x a
    -- `e'` is `e` composed with the embedding that skips the index of `y`.
    have h_e' : (fun i : Fin N ↦ x (e' i)) = (x ∘ e) ∘ (e.symm y).succAbove := by
      simp [funext_iff, e', finSuccEquiv'_symm_some]
    rw [h_e'] at h_rest
    -- The weight lowered by `γ` is that of `k γ` (`h_weight γ`), and a lift adds `x y ^ |γ|` to the
    -- product over the entries (`h_monomial`); so both sides are `x y ^ |γ|` times the sides of
    -- `h_rest`.
    have h_lowered : (⇑((columnWeight τ h).curry (c y)) - ⇑γ.val) =
        fun n : ℕ ↦ columnWeight τ (k γ) (c y, n) := by
      simp [funext_iff, h_weight γ, Prod.mk_right_injective]
    rw [h_lowered, ← h_rest]
    simp [h_monomial, ← univ.mul_sum, mul_assoc]

end New.GL

end MinorBasis

end
