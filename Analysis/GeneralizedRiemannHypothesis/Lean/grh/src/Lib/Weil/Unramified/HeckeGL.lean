import Lib.Adelic.Unitary.CongruenceLevels
import Lib.LocalGL.Iwahori.ParahoricStructure

/-!
# Hecke operators of GL_n at a finite place and local criteria for principal level

Let w be a finite place with uniformiser ϖ, let K = `New.localIntGL` = GL_n(O_w), and let k_w be the
residue field. `New.basicDoubleCoset` n w j is the set of g with g and ϖ g⁻¹ integral and det g of
order j. T_j = `New.heckeGL` is the action of its indicator function with vol K = 1. On K-fixed
vectors, T_j is computed as a sum over subspaces of k_w^n, and T_i and T_j are related when
n = i + j.

## Main definitions and results

* `New.basicCosetRep`, `New.basicDoubleCoset_eq`: a representative for each subspace;
  `New.basicDoubleCoset` is one double coset.
* `New.heckeGL_eq_sum`: on K-fixed vectors, T_j is a sum over the subspaces of dimension j.
* `New.heckeGL_dual`: for n = i + j, T_j is ϖ times the operator of the inverse coset of T_i.
* `New.sub_one_mem_span_iff_atPlace`: for an integral point, a congruence modulo `a` is tested at
  the primes dividing `a`.
* `New.inf_supportedOn_le_principalLevel`: integral points supported on primes that, with their
  conjugates, do not divide `a` have principal level `a`.
* `New.block_embFin`: the block matrix `diag (γ, 1)`, relabelled along `ε`, commutes with the
  embedding into finite adeles.

Notions from other files:
* `New.levelSpace`: For a representation π of G, a subgroup K and a character χ of K, the submodule
  of vectors v with π(k)v = χ(k)v for all k in K.
* `New.heckeFun`: For a function f on G, the operator ∑ f(g)π(g), summed over chosen representatives
  g of G/K (zero if infinitely many terms are nonzero): the action of f for vol K = 1.
* `New.U.block`: The block diagonal embedding U(1_m) × U(1_l) → U(1_n) of unitary groups of identity
  matrices, along a bijection of the disjoint union of m and l with n.

## Relation to the literature

Known result: the decomposition of the double coset of diag(ϖ 1_j, 1) in GL_n(E_w) into single
cosets, indexed by the subspaces of dimension j of k_w^n.

See also `Lib.Adelic.Unitary.CongruenceLevels`.
-/

noncomputable section

/-!
## Basic double cosets of GL_n at a place, indexed by subspaces

For g in `New.basicDoubleCoset` n w j, the coset K g is determined by the kernel of g mod w
(`New.residueKer`), a subspace of k_w^n of dimension j. Every such subspace occurs.

Valuations are multiplicative: `v x ≤ 1` means integral and `v ϖ = exp (-1)`.
-/

section HeckeGL

open Matrix IsLocalRing Module Valued DoubleCoset Set Finset WithZero Projectivization

namespace New

section

variable (n : Type*)
  {A W E : Type*} [Fintype n] [DecidableEq n] [Field E] [NumberField E]
  (w : FinPlace E) [CommRing A] [AddCommGroup W] [Module A W]

/-- The ring of integers O_w of the local field E_w is compact. -/
instance : CompactSpace 𝒪[LocField w] := compactSpace_LocInt w

/-- The group GL_n(O_w) = `New.localIntGL` n w is compact. -/
instance : CompactSpace (localIntGL n w) := isCompact_iff_compactSpace.mp (isCompact_localIntGL w)

/-! ### Congruence subgroups of GL_n(O_w) -/

/-- The subgroup of GL_n(O_w) of matrices congruent to 1 modulo 𝔭^(m+1), 𝔭 the maximal ideal of
O_w. -/
def localCongruence (m : ℕ) : Subgroup (GL n (LocField w)) :=
  congruenceGL (v.leSubmodule (exp (-m.succ))) id

end

variable {n : Type*} {A W E : Type*} [Fintype n] [DecidableEq n] [Field E] [NumberField E]
  {w : FinPlace E} [CommRing A] [AddCommGroup W] [Module A W]
  {π : Representation A (GL n (LocField w)) W} {j : ℕ} {g : GL n (LocField w)} {i : ℕ}
  {g' : GL n (LocField w)} {m : Type*} {ϖ : (LocField w)ˣ} {z : Matrix m n (LocField w)}
  (U : Submodule (ResField w) (n → ResField w))

attribute [-simp] WithZero.inv_exp
attribute [local simp] WithZero.exp_neg

/-- A matrix g lies in `New.localCongruence` n w m exactly when it lies in GL_n(O_w) and every
entry of g - 1 has valuation at most exp (-(m + 1)), that is, lies in 𝔭^(m+1). -/
lemma mem_localCongruence {m : ℕ} :
    g ∈ localCongruence n w m ↔
      g ∈ intGL n v.integer ∧ ∀ a b : n, v ((g.val - 1) a b) ≤ exp (-(m.succ : ℤ)) :=
  Iff.rfl

/-- The congruence subgroups `New.localCongruence` n w m are open in GL_n(E_w). -/
lemma isOpen_localCongruence {m : ℕ} : (localCongruence n w m).IsOpen := by
  refine isOpen_congruenceGL (isOpen_integer _) ?_
  -- The level is the closed ball of radius `v (ϖ ^ (m + 1))`, which is open.
  have h_ball : ((v (R := LocField w)).leSubmodule (exp (-(m.succ : ℤ))) : Set (LocField w)) =
      {x | v.restrict x ≤ v.restrict ((uniformizer w ^ m.succ : (LocField w)ˣ) : LocField w)} := by
    ext x
    rw [Set.mem_ofPred_eq, v.restrict_le_iff]
    simp [v_uniformizer]
  rw [h_ball]
  exact isOpen_closedBall _ ((uniformizer w ^ m.succ).isUnit.map v.restrict).ne_zero

/-- The first congruence subgroup is the kernel of the reduction of GL_n(O_w). -/
lemma mem_localCongruence_zero :
    g ∈ localCongruence n w 0 ↔ ∃ h : g ∈ intGL n v.integer, reduceGL ⟨g, h⟩ = 1 := by
  calc g ∈ localCongruence n w 0
      ↔ ∃ _ : g ∈ intGL n v.integer, ∀ a b : n, v ((g.val - 1) a b) ≤ exp (-((0 : ℕ).succ : ℤ)) :=
        exists_prop.symm
    _ ↔ ∃ h_int : g ∈ intGL n v.integer, reduceGL ⟨g, h_int⟩ = 1 := by
        refine exists_congr fun h_int ↦ ?_
        -- The reduction is `1` iff each entry of `g - 1` has residue `0` (`intGL.map_eq_one`),
        -- that is, valuation `< 1`, which is `≤ exp (-1)`.
        refine (intGL.map_eq_one.trans (forall₂_congr fun a b ↦ ?_)).symm
        refine residue_eq_zero_iff_valuation_lt_one.trans ?_
        simp [← lt_mul_exp_iff_le]

/-- Every neighbourhood s of 1 contains, for all sufficiently large m, the group
`New.localCongruence` of matrices congruent to 1 modulo 𝔭^(m+1), 𝔭 the prime at w. -/
lemma eventually_localCongruence_subset {s : Set (GL n (LocField w))} (hs : s ∈ nhds 1) :
    ∀ᶠ m : ℕ in Filter.atTop, (localCongruence n w m : Set (GL n (LocField w))) ⊆ s := by
  -- It suffices that the levels `𝔭 ^ (m + 1)` eventually lie in each basic ball around `0`.
  refine eventually_congruenceGL_subset
    ((hasBasis_nhds_zero _ _).smallSets.tendsto_right_iff.mpr fun γ _ ↦ ?_) hs
  obtain ⟨N, hN⟩ : ∃ N : ℕ, exp (-(N : ℤ)) < MonoidWithZeroHom.ValueGroup₀.embedding γ.val :=
    exists_exp_neg_natCast_lt (by simp)
  filter_upwards [Filter.eventually_ge_atTop N] with m hm x hx
  have h_exp : exp (-(m.succ : ℤ)) ≤ exp (-(N : ℤ)) := by grind [exp_le_exp]
  exact v.restrict_lt_iff_lt_embedding.mpr ((hx.trans h_exp).trans_lt hN)

/-- Lifting the exponent in GL_n(E_w): if the natural number q lies in the prime 𝔭 of w and
g ≡ 1 mod 𝔭, then g^(q^k) ≡ 1 mod 𝔭^(k+1). -/
lemma pow_pow_mem_localCongruence {q : ℕ} (hq : (q : NumberField.RingOfIntegers E) ∈ w.asIdeal)
    (hg_zero : g ∈ localCongruence n w 0) (k : ℕ) :
    g ^ q ^ k ∈ localCongruence n w k := by
  induction k with
  | zero => simpa using hg_zero
  | succ k ih =>
    obtain ⟨hg_int, -⟩ := mem_localCongruence.mp hg_zero
    refine mem_localCongruence.mpr ⟨pow_mem hg_int _, fun a b ↦ ?_⟩
    -- With `x = g ^ q ^ k`, factor `x ^ q - 1 = (x - 1) * ∑ l < q, x ^ l`. The first factor lies in
    -- `𝔭 ^ (k + 1)` by induction, so the entries of the second must be shown to lie in `𝔭`.
    have h_factor : (g ^ q ^ (k + 1)).val - 1 =
        ((g ^ q ^ k).val - 1) * ∑ l ∈ range q, (g ^ q ^ k).val ^ l := by
      rw [mul_geom_sum, ← Units.val_pow_eq_pow_val, ← pow_mul, ← pow_succ]
    have h_exp : exp (-((k + 1).succ : ℤ)) = exp (-(k.succ : ℤ)) * exp (-1) := by
      rw [← exp_add]
      grind
    rw [h_factor, h_exp]
    refine v_matrix_mul_le (mem_localCongruence.mp ih).right (fun a b ↦ ?_) a b
    -- Indeed `∑ l < q, x ^ l = ∑ l < q, (x ^ l - 1) + q • 1`, with `x ^ l ≡ 1 mod 𝔭` and `q ∈ 𝔭`.
    let P : Submodule v.integer (LocField w) := v.leSubmodule (exp (-1))
    have h_sum : ∑ l ∈ range q, (((g ^ q ^ k) ^ l).val - 1) a b ∈ P :=
      sum_mem fun l _ ↦ (pow_mem (pow_mem hg_zero (q ^ k)) l).right a b
    have h_q : (if a = b then (q : LocField w) else 0) ∈ P := by
      simp_all [P, apply_ite, ← lt_mul_exp_iff_le, ← w.intValuation_lt_one_iff_mem,
        ← v_algebraMap_eq_intValuation]
    simpa [P, Matrix.sum_apply, one_apply] using add_mem h_sum h_q

/-! ### Reduction of matrices and the kernel of the reduction -/

/-- The map from E_w to the residue field at w that reduces integral elements and sends all
others to 0. -/
def residueOrZero (x : LocField w) : ResField w :=
  if h : v x ≤ 1 then residue (LocInt w) ⟨x, h⟩ else 0

/-- The kernel, in column vectors over the residue field at w, of the entrywise reduction
`New.residueOrZero` of the matrix z. -/
abbrev residueKer (z : Matrix m n (LocField w)) : Submodule (ResField w) (n → ResField w) :=
  (z.map residueOrZero).mulVecLin.ker

lemma residueOrZero_coe (y : LocInt w) : residueOrZero y.val = residue (LocInt w) y :=
  dite_eq_left y.prop

/-- `New.residueOrZero` x vanishes exactly when x is not a unit of the local integers, that is
when v x ≠ 1. -/
@[simp]
lemma residueOrZero_eq_zero {x : LocField w} : residueOrZero x = 0 ↔ v x ≠ 1 := by
  rw [residueOrZero, dite_eq_right_iff]
  -- An integral element has residue `0` exactly when its valuation is `< 1`.
  exact (forall_congr' fun _ ↦ residue_eq_zero_iff_valuation_lt_one).trans (by grind)

lemma residueOrZero_eq_zero_iff_lt {x : LocField w} (hx_le : v x ≤ 1) :
    residueOrZero x = 0 ↔ v x < 1 :=
  residueOrZero_eq_zero.trans hx_le.lt_iff_ne.symm

omit [DecidableEq n] in
/-- For matrices z and y with integral entries, the entrywise reduction `New.residueOrZero` of
z * y is the product of the reductions of z and of y. -/
lemma map_residueOrZero_mul {y : Matrix n n (LocField w)} (hz : ∀ (i : m) (j : n), v (z i j) ≤ 1)
    (hy : ∀ i j : n, v (y i j) ≤ 1) :
    (z * y).map residueOrZero = z.map residueOrZero * y.map residueOrZero := by
  ext a b
  -- The entry of `z * y` comes from a sum of products in the local integers.
  let s : LocInt w := ∑ k, ⟨z a k, hz a k⟩ * ⟨y k b, hy k b⟩
  simpa [s, mul_apply, residueOrZero, hz, hy] using residueOrZero_coe s

omit [DecidableEq n] in
/-- For a matrix x over a field k with columns indexed by n, the number of columns minus the rank
of x is the dimension of the kernel of x acting on column vectors. -/
lemma card_sub_rank_eq_finrank_ker {k : Type*} [Field k] (x : Matrix m n k) :
    Fintype.card n - x.rank = finrank k x.mulVecLin.ker := by
  grind [finrank_pi, rank, x.mulVecLin.finrank_range_add_finrank_ker]

/-- Over a field with q elements, the subgroup H of GL_n of matrices whose i-th column vanishes
off the diagonal (the stabiliser of a line) has index 1 + q + ⋯ + q^(n − 1). -/
lemma index_stabilizer_line {F : Type*} [Field F] [Finite F] (i : n) {H : Subgroup (GL n F)}
    (hH : ∀ g : GL n F, g ∈ H ↔ ∀ j ≠ i, g j i = 0) :
    H.index = ∑ j ∈ Finset.range (Fintype.card n), Nat.card F ^ j := by
  -- `GL n F` acts transitively on the projective space (`SL n F` does), and `H` is the stabiliser
  -- of a point.
  let p : Projectivization F (n → F) := .mk F (Pi.single i 1) (by simp)
  have h_stab : H = MulAction.stabilizer (GL n F) p := by
    ext g
    simp [hH, p, Projectivization.mk_eq_mk_iff', funext_iff, Pi.single_apply, Units.smul_def,
      ite_eq_iff', forall_and, eq_comm (a := (0 : F))]
  have h_transitive : MulAction.IsPretransitive (GL n F) (Projectivization F (n → F)) :=
    .of_smul_eq SpecialLinearGroup.toGL rfl
  rw [h_stab, MulAction.index_stabilizer_of_transitive,
    Projectivization.card_of_finrank _ _ (finrank_pi F)]

/-! ### The double cosets and their parametrisation by subspaces -/

/-- For a uniformiser ϖ of E_w and a set s of indices, the diagonal matrix with ϖ on s and 1
elsewhere lies in the double coset `New.basicDoubleCoset` n w #s. -/
lemma diagGL_ite_mem_basicDoubleCoset (hϖ : v ϖ.val = exp (-1)) (s : Finset n) :
    diagGL (fun i : n ↦ if i ∈ s then ϖ else 1) ∈ basicDoubleCoset n w #s := by
  classical
  -- Each condition is read off the diagonal entries. `coe_units_inv` is left out so that the
  -- inverse stays the image of a unit under `diagGL`.
  simp +decide [basicDoubleCoset, -coe_units_inv, ← map_inv, diagonal_apply, apply_ite, hϖ,
    ite_apply]

/-- For a uniformiser ϖ of E_w and a set s of indices, the kernel of the reduction modulo w of
the diagonal matrix with ϖ on s and 1 elsewhere has dimension #s. -/
lemma finrank_residueKer_diagGL (hϖ : v ϖ.val = exp (-1)) (s : Finset n) :
    finrank (ResField w) (residueKer (diagGL fun i : n ↦ if i ∈ s then ϖ else 1).val) = #s := by
  classical
  -- The reduction is diagonal with `0` on `s` and `1` off `s`, so its rank is `#sᶜ`.
  rw [residueKer, ← card_sub_rank_eq_finrank_ker]
  simp +decide [apply_ite, hϖ, ite_apply, rank_diagonal, ← card_compl]

/-- For a uniformiser ϖ of E_w and a set s of indices, the diagonal matrix with ϖ on s and 1
elsewhere lies in the double coset `New.basicDoubleCoset` with j = #s, and the kernel of its
reduction has dimension #s. -/
lemma diagGL_mem_basicDoubleCoset (hϖ : v ϖ.val = exp (-1)) (s : Finset n) :
    diagGL (fun i : n ↦ if i ∈ s then ϖ else 1) ∈ basicDoubleCoset n w #s ∧
      finrank (ResField w) (residueKer (diagGL fun i : n ↦ if i ∈ s then ϖ else 1).val) = #s :=
  ⟨diagGL_ite_mem_basicDoubleCoset hϖ s, finrank_residueKer_diagGL hϖ s⟩

/-- The set `New.basicDoubleCoset` n w j is stable under multiplication on both sides by elements
of GL_n(O_w) = `New.localIntGL` n w. -/
lemma mul_mul_mem_basicDoubleCoset (hg : g ∈ basicDoubleCoset n w j) {k k' : GL n (LocField w)}
    (hk : k ∈ localIntGL n w) (hk' : k' ∈ localIntGL n w) :
    k * g * k' ∈ basicDoubleCoset n w j := by
  obtain ⟨hg_int, hg_inv, hg_det⟩ := hg
  refine ⟨v_matrix_mul_le (v_matrix_mul_le hk.isIntMatrix hg_int) hk'.isIntMatrix,
    v_matrix_mul_le hk'.isIntMatrix_inv (v_matrix_mul_le hg_inv hk.isIntMatrix_inv), ?_⟩
  -- The determinants of `k` and `k'` have valuation `1`.
  simp [(mem_intGL_iff_det.mp hk).right, (mem_intGL_iff_det.mp hk').right, hg_det]

/-- For g in the double coset of diag(ϖ 1_j, 1) in GL_n(E_w) and a matrix z over E_w with n
columns, z g⁻¹ is integral if and only if z is integral and the kernel of g mod w lies in
that of z mod w. -/
lemma v_mul_inv_le_one_iff (hg : g ∈ basicDoubleCoset n w j) :
    (∀ (a : m) (b : n), v ((z * g⁻¹.val) a b) ≤ 1) ↔
      (∀ (a : m) (b : n), v (z a b) ≤ 1) ∧ residueKer g.val ≤ residueKer z := by
  -- One direction multiplies `z g⁻¹` by `g`, the other multiplies `z` by the integral matrix
  -- `ϖ g⁻¹`, whose columns reduce into the kernel of `g` mod `w`.
  obtain ⟨hg_int, hg_inv, -⟩ := hg
  constructor
  · -- Write `z = (z g⁻¹) g` as a product of integral matrices, and reduce.
    intro h_int
    refine ⟨by simpa using v_matrix_mul_le h_int hg_int, fun x hx ↦ ?_⟩
    have h_red : z.map residueOrZero =
        (z * g⁻¹.val).map residueOrZero * g.val.map residueOrZero := by
      simpa using map_residueOrZero_mul h_int hg_int
    have hx_zero : g.val.map residueOrZero *ᵥ x = 0 := by simpa using hx
    rw [LinearMap.mem_ker, mulVecLin_apply, h_red, ← mulVec_mulVec, hx_zero, mulVec_zero]
  · -- The matrix `y = ϖ g⁻¹` is integral and `g y = ϖ` reduces to `0`, so the columns of the
    -- reduction of `y` lie in `residueKer g ≤ residueKer z`. Hence `z y` reduces to `0`, and
    -- dividing its entries by `ϖ` leaves the entries of `z g⁻¹` integral.
    rintro ⟨hz, h_ker⟩ a b
    set y : Matrix n n (LocField w) := (uniformizer w).val • g⁻¹.val with hy_def
    have hy (i j : n) : v (y i j) ≤ 1 := by simpa [hy_def, field] using hg_inv i j
    have h_col : (y.map residueOrZero)ᵀ b ∈ residueKer g.val :=
      calc (g.val.map residueOrZero * y.map residueOrZero)ᵀ b
        _ = ((g.val * y).map residueOrZero)ᵀ b := by rw [map_residueOrZero_mul hg_int hy]
        _ = 0 := by simp [hy_def, funext_iff, one_apply, apply_ite v, ite_eq_iff]
    have h_zero : residueOrZero ((z * y) a b) = 0 :=
      calc (z * y).map residueOrZero a b
        _ = (z.map residueOrZero * y.map residueOrZero) a b := by rw [map_residueOrZero_mul hz hy]
        _ = 0 := congrFun (h_ker h_col) a
    have h_lt : v ((z * y) a b) < 1 :=
      (residueOrZero_eq_zero_iff_lt (v_matrix_mul_le hz hy a b)).mp h_zero
    have h_entry : (z * g⁻¹.val) a b = (uniformizer w).val⁻¹ * (z * y) a b := by
      simp [hy_def, Matrix.mul_smul]
    rw [h_entry]
    exact v_uniformizer_inv_mul_le_one_iff.mpr h_lt

/-- For g in `New.basicDoubleCoset` n w j and g' in `New.basicDoubleCoset` n w i, the element
g g'⁻¹ lies in GL_n(O_w) if and only if g and g' have the same kernel mod w. -/
lemma mul_inv_mem_localIntGL_iff (hg : g ∈ basicDoubleCoset n w j)
    (hg' : g' ∈ basicDoubleCoset n w i) :
    g * g'⁻¹ ∈ localIntGL n w ↔ residueKer g.val = residueKer g'.val := by
  -- Apply `v_mul_inv_le_one_iff` to `g * g'⁻¹` and to its inverse `g' * g⁻¹`.
  have h_left : (∀ a b : n, v ((g.val * g'⁻¹.val) a b) ≤ 1) ↔
      residueKer g'.val ≤ residueKer g.val := by
    simpa [show ∀ a b : n, v (g.val a b) ≤ 1 from hg.left] using
      v_mul_inv_le_one_iff hg' (z := g.val)
  have h_right : (∀ a b : n, v ((g'.val * g⁻¹.val) a b) ≤ 1) ↔
      residueKer g.val ≤ residueKer g'.val := by
    simpa [show ∀ a b : n, v (g'.val a b) ≤ 1 from hg'.left] using
      v_mul_inv_le_one_iff hg (z := g'.val)
  -- Entries in the local integers are those of valuation at most `1`. `coe_units_inv` is left out
  -- so that `h_left` and `h_right` apply as stated.
  simp [mem_intGL, mem_LocInt, -coe_units_inv, h_left, h_right, le_antisymm_iff, and_comm]

/-- Let g lie in `New.basicDoubleCoset` n w j and let U have the same dimension as the kernel of g
mod w. Then some k in the same double coset has kernel U mod w and lies in g GL_n(O_w). -/
lemma exists_residueKer_eq_and_inv_mul_mem_localIntGL (hg : g ∈ basicDoubleCoset n w j)
    (h_finrank : finrank (ResField w) (residueKer g.val) = finrank (ResField w) U) :
    ∃ k ∈ basicDoubleCoset n w j, residueKer k.val = U ∧ k⁻¹ * g ∈ localIntGL n w := by
  -- Take an automorphism `e` of `k_w ^ n` that maps `U` onto `residueKer g`, and lift it to
  -- `l ∈ localIntGL n w`. The element sought is `g * l`.
  obtain ⟨e, he⟩ : ∃ e : (n → ResField w) ≃ₗ[ResField w] (n → ResField w),
      ∀ x : U, (LinearEquiv.ofFinrankEq U (residueKer g.val) h_finrank.symm x : n → ResField w) =
        e x :=
    U.exists_linearEquiv_restrict_eq _
  obtain ⟨l, hl⟩ : ∃ l : localIntGL n w, GeneralLinearGroup.toLin (reduceGL l) = .ofLinearEquiv e :=
    GeneralLinearGroup.toLin.surjective.comp reduceGL_surjective _
  have h_red : ((l : GL n (LocField w)).val.map residueOrZero).mulVecLin = e := by
    -- The entries of `l` are integral, so `residueOrZero` reduces them as `reduceGL` does.
    refine Eq.trans (congrArg mulVecLin ?_) (congrArg Units.val hl)
    ext i j
    exact residueOrZero_coe ⟨(l : GL n (LocField w)) i j, l.property.isIntMatrix i j⟩
  -- `U` lies in the preimage of `residueKer g` under `e` and has the same dimension.
  have h_comap : U = (residueKer g.val).comap e.toLinearMap := by
    refine U.eq_of_le_of_finrank_eq (fun x hx ↦ ?_) ?_
    · rw [Submodule.mem_comap, LinearEquiv.coe_coe, ← he ⟨x, hx⟩]
      exact Submodule.coe_mem _
    · rw [← h_finrank, (e.ofSubmodule' _).finrank_eq]
  have hg_int : ∀ a b : n, v (g.val a b) ≤ 1 := hg.1
  have h_mem : g * l ∈ basicDoubleCoset n w j := by
    simpa using mul_mul_mem_basicDoubleCoset hg (one_mem (localIntGL n w)) l.property
  refine ⟨g * l, h_mem, ?_, by simp⟩
  -- Reduction is multiplicative, so `residueKer (g * l)` is that same preimage.
  rw [residueKer, Units.val_mul, map_residueOrZero_mul hg_int l.property.isIntMatrix, mulVecLin_mul,
    h_red, h_comap, LinearMap.ker_comp]

omit [DecidableEq n] in
lemma exists_card_eq_finrank : ∃ s : Finset n, #s = finrank (ResField w) U := by
  obtain ⟨s, -, hs⟩ := exists_subset_card_eq (U.finrank_le.trans_eq (finrank_pi _))
  exact ⟨s, hs⟩

/-- Every subspace U of k_w^n is the kernel of the reduction modulo w of some element of
`New.basicDoubleCoset` n w j with j = dim U. -/
lemma exists_mem_basicDoubleCoset_residueKer_eq :
    ∃ k ∈ basicDoubleCoset n w (finrank (ResField w) U), residueKer k.val = U := by
  -- Start from the diagonal matrix with `ϖ` on a set `s` of `dim U` indices, and move the kernel
  -- of its reduction onto `U` by `exists_residueKer_eq_and_inv_mul_mem_localIntGL`.
  obtain ⟨s, hs⟩ := exists_card_eq_finrank U
  let d : GL n (LocField w) := diagGL fun i : n ↦ if i ∈ s then uniformizer w else 1
  have hd_mem : d ∈ basicDoubleCoset n w (finrank (ResField w) U) := by
    simpa [d, hs] using diagGL_ite_mem_basicDoubleCoset (v_uniformizer w) s
  have hd_finrank : finrank (ResField w) (residueKer d.val) = finrank (ResField w) U :=
    (finrank_residueKer_diagGL (v_uniformizer w) s).trans hs
  obtain ⟨k, hk_mem, hk_ker, -⟩ :=
    exists_residueKer_eq_and_inv_mul_mem_localIntGL U hd_mem hd_finrank
  exact ⟨k, hk_mem, hk_ker⟩

/-- For a subspace U of k_w^n (k_w the residue field at w), a chosen element of the double coset
`New.basicDoubleCoset` n w j of diag(ϖ 1_j, 1), j = dim U, whose reduction modulo w has kernel U.
As U runs over the subspaces of dimension j, these elements represent the cosets K g in that
double coset, K = GL_n(O_w). -/
def basicCosetRep : GL n (LocField w) :=
  (exists_mem_basicDoubleCoset_residueKer_eq U).choose

lemma basicCosetRep_mem_basicDoubleCoset :
    basicCosetRep U ∈ basicDoubleCoset n w (finrank (ResField w) U) :=
  (exists_mem_basicDoubleCoset_residueKer_eq U).choose_spec.left

lemma residueKer_basicCosetRep : residueKer (basicCosetRep U).val = U :=
  (exists_mem_basicDoubleCoset_residueKer_eq U).choose_spec.right

/-- The representative `New.basicCosetRep` U lies in `basicDoubleCoset` d with d = dim U, that is,
in GL_n(O_w) diag(ϖ 1_d, 1) GL_n(O_w). The kernel of its reduction modulo w is U. -/
lemma basicCosetRep_mem_and_residueKer_eq :
    basicCosetRep U ∈ basicDoubleCoset n w (finrank (ResField w) U) ∧
    residueKer (basicCosetRep U).val = U :=
  ⟨basicCosetRep_mem_basicDoubleCoset U, residueKer_basicCosetRep U⟩

/-- For g in `New.basicDoubleCoset` n w j, the kernel of the reduction of g modulo w has
dimension j. -/
lemma finrank_residueKer (hg : g ∈ basicDoubleCoset n w j) :
    finrank (ResField w) (residueKer g.val) = j := by
  -- `g` and `basicCosetRep (residueKer g)` have the same kernel, so they differ by an element of
  -- `localIntGL n w` and their determinants have the same order.
  have h_mem : basicCosetRep (residueKer g.val) ∈
      basicDoubleCoset n w (finrank (ResField w) (residueKer g.val)) :=
    basicCosetRep_mem_basicDoubleCoset (residueKer g.val)
  have h_Kw : basicCosetRep (residueKer g.val) * g⁻¹ ∈ localIntGL n w :=
    (mul_inv_mem_localIntGL_iff h_mem hg).mpr (residueKer_basicCosetRep _)
  have h_det : v (basicCosetRep (residueKer g.val) * g⁻¹).val.det = 1 :=
    (mem_intGL_iff_det.mp h_Kw).right
  obtain ⟨-, -, h_det_rep⟩ := h_mem
  obtain ⟨-, -, hg_det⟩ := hg
  simpa [h_det_rep, hg_det, inv_mul_eq_one₀] using h_det

/-- For every g in the set `New.basicDoubleCoset` of index j, that set is the double coset GL_n(O_w)
g GL_n(O_w). -/
lemma basicDoubleCoset_eq (hg : g ∈ basicDoubleCoset n w j) :
    basicDoubleCoset n w j = doubleCoset g (localIntGL n w) (localIntGL n w) := by
  ext x
  rw [mem_doubleCoset]
  constructor
  · -- The kernels of the reductions of `g` and `x` both have dimension `j`. Choose `y` in the coset
    -- `x localIntGL` with the same kernel as `g`; then `y g⁻¹ ∈ localIntGL`.
    intro hx
    obtain ⟨y, hy, h_ker, h_coset⟩ := exists_residueKer_eq_and_inv_mul_mem_localIntGL
      (residueKer g.val) hx (by rw [finrank_residueKer hg, finrank_residueKer hx])
    exact ⟨y * g⁻¹, (mul_inv_mem_localIntGL_iff hy hg).mpr h_ker, y⁻¹ * x, h_coset, by group⟩
  · rintro ⟨k, hk, k', hk', rfl⟩
    exact mul_mul_mem_basicDoubleCoset hg hk hk'

lemma le_card_of_mem_basicDoubleCoset (hg : g ∈ basicDoubleCoset n w j) :
    j ≤ Fintype.card n := by
  simp [← finrank_residueKer hg, ← card_sub_rank_eq_finrank_ker]

/-- The space k_w^n over the finite residue field has finitely many subspaces. -/
instance : Fintype (Submodule (ResField w) (n → ResField w)) := .ofFinite _

lemma transposeGL_mem_basicDoubleCoset :
    transposeGL g ∈ basicDoubleCoset n w j ↔ g ∈ basicDoubleCoset n w j := by
  simp only [basicDoubleCoset, Set.mem_ofPred_eq]
  -- Transposing permutes the entries of `g` and of `g⁻¹` and keeps the determinant.
  refine and_congr forall_comm (and_congr forall_comm ?_)
  simp

/-! ### The Hecke operators on vectors fixed by GL_n(O_w) -/

/-- The indicator function of `New.basicDoubleCoset` n w j is invariant on both sides under
K = GL_n(O_w) and is nonzero on finitely many cosets g K (`New.IsHeckeFunction`). -/
@[simp]
lemma isHeckeFunction_basicDoubleCoset (j : ℕ) :
    IsHeckeFunction (localIntGL n w) ((basicDoubleCoset n w j).indicator
      (1 : GL n (LocField w) → A)) := by
  obtain h_empty | ⟨g, hg⟩ := (basicDoubleCoset n w j).eq_empty_or_nonempty
  · simp [h_empty, IsHeckeFunction, HasFiniteCosets]
  · rw [basicDoubleCoset_eq hg]
    exact isHeckeFunction_doubleCoset (isOpen_localIntGL w) g

/-- The function g ↦ 1_D(g⁻¹), D = `New.basicDoubleCoset` n w j, is invariant under right
multiplication by GL_n(O_w). -/
lemma indicator_basicDoubleCoset_mul_inv (j : ℕ) (g : GL n (LocField w)) (k : localIntGL n w) :
    (basicDoubleCoset n w j).indicator (1 : GL n (LocField w) → A) (g * k)⁻¹ =
      (basicDoubleCoset n w j).indicator 1 g⁻¹ := by
  simp

/-- Let x be fixed by K = GL_n(O_w), and let D = `New.basicDoubleCoset` j, which is K diag(ϖ 1_j, 1)
K for j ≤ n. Then the Hecke operator `heckeFun` of the function g ↦ 1_D(g⁻¹) sends x to ∑_U
π(γ_U⁻¹)x. The sum runs over the j-dimensional subspaces U of k_w^n (k_w the residue field), and
γ_U = `New.basicCosetRep` U is the chosen element of D whose reduction modulo w has kernel U. -/
lemma heckeFun_basicDoubleCoset_inv {x : W} (hx : x ∈ levelSpace (A := A) π (localIntGL n w)) :
    heckeFun π (localIntGL n w) (fun g : GL n (LocField w) ↦
      (basicDoubleCoset n w j).indicator 1 g⁻¹) x =
      ∑ U ∈ {U : Submodule (ResField w) (n → ResField w) | finrank (ResField w) U = j},
        π (basicCosetRep U)⁻¹ x := by
  -- The elements `(basicCosetRep U)⁻¹`, `dim U = j`, represent the cosets `g⁻¹ localIntGL` with `g`
  -- in the double coset, because such a coset is determined by `residueKer g`, and
  -- `residueKer (basicCosetRep U) = U`.
  have h_coset_iff {i : ℕ} {g : GL n (LocField w)} (U : Submodule (ResField w) (n → ResField w))
      (hg : g ∈ basicDoubleCoset n w i) :
      (↑(basicCosetRep U)⁻¹ : GL n (LocField w) ⧸ localIntGL n w) = ↑g⁻¹ ↔
        U = residueKer g.val := by
    rw [QuotientGroup.eq, inv_inv, mul_inv_mem_localIntGL_iff (basicCosetRep_mem_basicDoubleCoset U)
      hg, residueKer_basicCosetRep U]
  let S : Finset (Submodule (ResField w) (n → ResField w)) := {U | finrank (ResField w) U = j}
  -- Distinct subspaces give distinct cosets.
  have h_inj :
      InjOn (fun U ↦ (↑(basicCosetRep U)⁻¹ : GL n (LocField w) ⧸ localIntGL n w))
        (SetLike.coe S) := by
    intro U _ V _ h_eq
    rw [(h_coset_iff U (basicCosetRep_mem_basicDoubleCoset V)).mp h_eq, residueKer_basicCosetRep]
  -- The coset of `g⁻¹` is represented by the subspace `residueKer g`, which has dimension `j`.
  have h_cover : ∀ g : GL n (LocField w), (basicDoubleCoset n w j).indicator 1 g⁻¹ ≠ (0 : A) →
      ∃ U ∈ S, (↑(basicCosetRep U)⁻¹ : GL n (LocField w) ⧸ localIntGL n w) = g := by
    refine inv_surjective.forall.mpr fun g h_ne ↦ ?_
    have hg : g ∈ basicDoubleCoset n w j := by simpa using mem_of_indicator_ne_zero h_ne
    exact ⟨residueKer g.val, by simp [S, finrank_residueKer hg], (h_coset_iff _ hg).mpr rfl⟩
  -- `heckeFun_eq_sum` sums over these representatives; the indicator is `1` at each of them.
  calc heckeFun π (localIntGL n w) (fun g ↦ (basicDoubleCoset n w j).indicator 1 g⁻¹) x
      = ∑ U ∈ S, (basicDoubleCoset n w j).indicator 1 ((basicCosetRep U)⁻¹)⁻¹ •
          π (basicCosetRep U)⁻¹ x :=
        (heckeFun_eq_sum (f := fun g ↦ (basicDoubleCoset n w j).indicator 1 g⁻¹)
          (indicator_basicDoubleCoset_mul_inv j) hx h_inj h_cover).right
    _ = ∑ U ∈ S, π (basicCosetRep U)⁻¹ x := by
        refine sum_congr rfl fun U hU ↦ ?_
        obtain rfl : finrank (ResField w) U = j := by simpa [S] using hU
        simp [basicCosetRep_mem_basicDoubleCoset]

/-- Let T_j = `heckeGL` j be the Hecke operator of the double coset K diag(ϖ 1_j, 1) K,
K = GL_n(O_w). On a K-fixed vector x, T_j x is the sum of π(γ_Uᵀ) x over the j-dimensional subspaces
U of k_w^n. Here γ_U = `New.basicCosetRep` U is the chosen element of that double coset whose
reduction modulo w has kernel U. -/
lemma heckeGL_eq_sum {x : W} (hx : x ∈ levelSpace (A := A) π (localIntGL n w)) :
    heckeGL π j x =
      ∑ U ∈ {U : Submodule (ResField w) (n → ResField w) | finrank (ResField w) U = j},
        π (transposeGL (basicCosetRep U)) x := by
  classical
  -- Twist `π` by the inverse transpose `invTransposeGL`, which preserves `localIntGL`, and apply
  -- `heckeFun_basicDoubleCoset_inv` to the twist, which sends `(basicCosetRep U)⁻¹` to
  -- `π (transposeGL (basicCosetRep U))`.
  have hx' : x ∈ levelSpace (π.comp invTransposeGL.toMonoidHom) (localIntGL n w) := by simp_all
  have h_Kw (g : GL n (LocField w)) : invTransposeGL g ∈ localIntGL n w ↔ g ∈ localIntGL n w := by
    simp
  -- `invTransposeGL` is an involution by definition.
  have h_twist (g : GL n (LocField w)) :
      π g x = (π.comp invTransposeGL.toMonoidHom) (invTransposeGL g) x :=
    rfl
  -- The inverse transpose of `g⁻¹` is the transpose of `g`, which lies in the same double coset.
  have h_indicator (g : GL n (LocField w)) :
      (basicDoubleCoset n w j).indicator (1 : GL n (LocField w) → A) g =
        (basicDoubleCoset n w j).indicator 1 (invTransposeGL g)⁻¹ :=
    if_congr transposeGL_mem_basicDoubleCoset.symm rfl rfl
  calc heckeGL π j x
    _ = heckeFun (π.comp invTransposeGL.toMonoidHom) (localIntGL n w)
        (fun g ↦ (basicDoubleCoset n w j).indicator 1 g⁻¹) x :=
      heckeFun_comp (f := fun g ↦ (basicDoubleCoset n w j).indicator 1 g⁻¹)
        invTransposeGL.toMonoidHom (indicator_basicDoubleCoset_mul_inv j) hx'
        (isHeckeFunction_basicDoubleCoset j).left invTransposeGL.surjective h_Kw h_twist h_indicator
    _ = _ := heckeFun_basicDoubleCoset_inv hx'

/-- Let ϖ be a uniformiser of E_w and n = i + j. Then ϖ x lies in `New.basicDoubleCoset` n w j
exactly when x⁻¹ lies in `New.basicDoubleCoset` n w i: the two integrality conditions are
exchanged, and det (ϖ x) has order n = i + j plus that of det x. -/
lemma scalar_mul_mem_basicDoubleCoset_iff (hϖ : Valued.v ϖ.val = exp (-1))
    (hn : Fintype.card n = i + j) (x : GL n (LocField w)) :
    GeneralLinearGroup.scalar n ϖ * x ∈ basicDoubleCoset n w j ↔
      x⁻¹ ∈ basicDoubleCoset n w i := by
  -- The two integrality conditions trade places: `v (ϖ y) = exp (-1) * v y`. And
  -- `det (ϖ x) = ϖ ^ n * det x`.
  refine Iff.trans ?_ and_left_comm
  have h_entry (y : LocField w) : (exp 1)⁻¹ * Valued.v y ≤ 1 ↔ Valued.v y ≤ exp 1 := by
    simp [field]
  have h_det : (exp (j : ℤ))⁻¹ * (exp (i : ℤ))⁻¹ * Valued.v x.val.det = (exp (j : ℤ))⁻¹ ↔
      Valued.v x⁻¹.val.det = (exp (i : ℤ))⁻¹ := by
    simp [field]
  -- `coe_units_inv` is left out so that `(ϖ x)⁻¹` stays a unit, whose determinant `← map_inv`
  -- reads.
  simp [basicDoubleCoset, -coe_units_inv, ← map_inv, hϖ, hn, h_entry, h_det]

/-- Let ϖ be a uniformiser of E_w, n = i + j, and x fixed by GL_n(O_w). Acting on x by the
indicator of the inverse of the double coset of T_i and then by the scalar matrix ϖ gives
T_j x. -/
lemma heckeGL_dual {x : W} (hx : x ∈ levelSpace (A := A) π (localIntGL n w))
    (hϖ : v ϖ.val = exp (-1)) (hn : Fintype.card n = i + j) :
    π (GeneralLinearGroup.scalar n ϖ)
        (heckeFun π (localIntGL n w) (fun g : GL n (LocField w) ↦
          (basicDoubleCoset n w i).indicator 1 g⁻¹)
          x) =
      heckeGL π j x := by
  classical
  -- Acting by `ϖ⁻¹` on `T_j x` translates the indicator function of `New.basicDoubleCoset` n w j
  -- by `ϖ`, which turns it into `g ↦ 1_D(g⁻¹)`, D = `New.basicDoubleCoset` n w i.
  have h_right_inv (g : GL n (LocField w)) (k : localIntGL n w) :
      (basicDoubleCoset n w j).indicator (1 : GL n (LocField w) → A) (g * k) =
        (basicDoubleCoset n w j).indicator 1 g := by
    simp
  have h_indicator :
      (fun g : GL n (LocField w) ↦
        (basicDoubleCoset n w j).indicator (1 : GL n (LocField w) → A) ((.scalar n ϖ)⁻¹⁻¹ * g)) =
        fun g ↦ (basicDoubleCoset n w i).indicator 1 g⁻¹ := by
    simp [indicator_apply, scalar_mul_mem_basicDoubleCoset_iff hϖ hn]
  have h_shift :
      heckeFun π (localIntGL n w) (fun g ↦ (basicDoubleCoset n w i).indicator 1 g⁻¹) x =
        π (.scalar n ϖ)⁻¹ (heckeGL π j x) := by
    rw [← h_indicator, heckeGL]
    exact heckeFun_comp_inv_mul (isHeckeFunction_basicDoubleCoset j).left h_right_inv hx
      (.scalar n ϖ)⁻¹
  rw [eq_comm, ← π.inv_apply_eq_iff]
  exact h_shift.symm

/-- On a GL_n(O_w)-fixed vector x, the Hecke operator T_0 = `New.heckeGL` π 0 acts as the
identity. -/
lemma heckeGL_zero {x : W} (hx : x ∈ levelSpace (A := A) π (localIntGL n w)) :
    heckeGL π 0 x = x := by
  -- The sum has the single term `U = ⊥`, whose representative `γ` lies in `localIntGL` and so fixes
  -- `x`.
  set γ : GL n (LocField w) :=
    transposeGL (basicCosetRep (⊥ : Submodule (ResField w) (n → ResField w))) with hγ
  obtain ⟨h_int, -, h_det⟩ : γ ∈ basicDoubleCoset n w 0 := by
    simpa using transposeGL_mem_basicDoubleCoset.mpr (basicCosetRep_mem_basicDoubleCoset ⊥)
  have h_Kw : γ ∈ localIntGL n w := mem_intGL_iff_det.mpr ⟨h_int, by simpa using h_det⟩
  simp [heckeGL_eq_sum hx, filter_eq', ← hγ, mem_levelSpace.mp hx ⟨_, h_Kw⟩]

end New

end HeckeGL

/-! ## Local criteria for principal level and block embeddings -/

section PrincipalLevelCriteria

open NumberField Matrix Valued

namespace New

variable {E n n' : Type} [Field E] [NumberField E] [IsCMField E] [Fintype n] [DecidableEq n]
  [Fintype n'] {a : 𝓞 E}

/-- Let `g` be in `New.stdLevel E n`. The `(i, j)` entry of `g - 1` lies in the `Ô`-ideal generated
by `a` if and only if a local condition holds at every finite place `u` with `a ∈ u`. The condition
is that the valuation of the `(i, j)` entry of `g_u - 1` is at most the valuation of `a` at `u`. -/
lemma sub_one_mem_span_iff_atPlace {g : Gf E n} {i j : n} (hg : g ∈ stdLevel E n) :
    ((g : Matrix n n (𝔸f E)) - 1) i j ∈ Ô E ∙ algebraMap (𝓞 E) (𝔸f E) a ↔
      ∀ u : FinPlace E, a ∈ u.asIdeal → v (((g.atPlace u).val - 1) i j) ≤ u.intValuation a := by
  -- The entries of `g - 1` are integral, so only the places that divide `a` are left to test.
  refine mem_span_iff_valuation_le.trans ?_
  have h_int_entry : ((g : Matrix n n (𝔸f E)) - 1) i j ∈ Ô E := by
    aesop (add simp [mem_stdLevel, Matrix.one_apply])
  refine (and_iff_right h_int_entry).trans (forall₂_congr fun u _ ↦ ?_)
  -- At `u`, the entry of `g - 1` is the entry of `g_u - 1`.
  aesop (add simp Matrix.one_apply)

/-- Suppose that for every place `w` in `S`, neither `w` nor its conjugate `star w` contains `a`.
Then every element of `New.stdLevel E n` lying in `New.Gf.supportedOn n S` lies in
`New.principalLevel n a`. -/
lemma inf_supportedOn_le_principalLevel {S : Set (FinPlace E)}
    (h_not_mem : ∀ w ∈ S, a ∉ w.asIdeal ∧ a ∉ (star w).asIdeal) :
    stdLevel E n ⊓ Gf.supportedOn n S ≤ principalLevel n a := by
  intro g ⟨h_int, h_supp⟩
  refine ⟨h_int, fun i j ↦ ?_⟩
  rw [← mem_span_singleton_iff_exists_mul, sub_one_mem_span_iff_atPlace h_int]
  -- A place that divides `a` lies outside `S ∪ S̄`, so the component of `g` there is `1`.
  intro u hu
  have hu_star : star u ∉ S := fun hu_S ↦ (h_not_mem _ hu_S).right (by rwa [star_star])
  simp [Gf.mem_supportedOn.mp h_supp u (fun hu_S ↦ (h_not_mem u hu_S).left hu) hu_star]

/-- Let `γ` be in the unitary group `U` (`New.U`) of the standard space of `E` with basis `n`.
Form the block matrix `diag (γ, 1)`, relabelled along `ε : n ⊕ Unit ≃ n'` by `New.U.block`. This
block construction commutes with the embedding into the finite adelic group: on the left
`New.Space.embFin`, on the right `New.stdEmbFin`. -/
lemma block_embFin {E : Type} [Field E] [CMType E]
    [DecidableEq n'] (ε : n ⊕ Unit ≃ n') (γ : U (stdSpace E n).J) :
    U.block ε ((stdSpace E n).embFin γ, 1) = stdEmbFin (U.block ε (γ, 1)) := by
  -- Compare the matrices in `GL n' (𝔸f E)`; the right side is the image of the block matrix of `γ`
  -- (`stdSpace_embFin`).
  apply Subtype.ext
  refine (Units.ext ?_).trans (stdSpace_embFin _).symm
  -- Entrywise, both are `diag (γ, 1)` with entries mapped to the finite adeles.
  simp [U.block_val, stdSpace_embFin, ← submatrix_map, fromBlocks_map]

end New

end PrincipalLevelCriteria

end
