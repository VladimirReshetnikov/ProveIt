import Lib.Adelic.TraceFormula.ChangingSigns

/-!
# Eigenline reflections of a separable matrix, and the term of the count at a marked triple

Invariance properties of the terms of the point count `New.Variety.countTerm`, a function on
GL_n(E)-orbits of triples (coset xK, rational matrix y, index μ of a root), the type
`MarkedTriple (levelGU n 𝔑) n`.

* `New.Variety.isReflection_markedReflection` and
  `New.Variety.exists_eq_markedReflection_iff_of_ratConj_eq` (bundled as
  `New.Variety.isReflection_markedReflection_and_exists_eq_iff`): for y with separable
  characteristic polynomial, the matrices `New.Variety.markedReflection y i` are reflections, and
  each reflection that commutes with y equals exactly one of them.
* `New.Variety.countTerm_mk`: the term of an orbit may be computed at any representative.
* `New.Variety.finsum_countTerm_eq_sum`: the weighted count as a finite sum over the support of the
  count of weight 1.

`New.Variety.IsReflection J` says J = u wᵀ - 1 with w · u = 2. `New.Variety.ratConj z` conjugates by
Φ_{v₀}(z), the image of z in GL_n(ℂ) under the fixed embedding Φ v₀ : E → ℂ used throughout.
`New.Variety.IsSignedFrame x J` says that x is a frame for a rational form whose signature is given
by J.

Notions from other files:
* `New.Variety.heckeAlgebra`: the Hecke algebra of level K(𝔑): the subalgebra of elements ∑ a_g [g]
  of ℂ[GL_n(𝔸_f)] that are supported on `GUPlus E n` and whose function ∑ a_g 1_{gK} is left
  K(𝔑)-invariant.
* `New.Variety.levelGU`: the principal level K(𝔑), the similitudes in `GL_n(Ô E)` that are congruent
  to `1` modulo `𝔑`.
* `New.Variety.toFinGL`: The diagonal embedding of GL_n(E) in GL_n of the finite adeles of E.
* `New.Variety.heckeCosetFn f`: for f = ∑ a_g [g] in the Hecke algebra, the function ∑ a_g 1_{gK} on
  the cosets of the level `K`.
* `New.Variety.eigenReflection ε y μ`: if `ε` holds, the matrix `New.Variety.markedReflection y μ`,
  a polynomial in Φ_{v₀}(y) that is `1` on the eigenline of the `μ`-th listed root of the
  characteristic polynomial and `-1` on the other eigenlines; if `ε` fails, the identity.

## Relation to the literature

Known; see `Lib.Shimura.Transfer.WeightOccurs` and `Lib.Shimura.TraceFormula.MarkedDefiniteSums` for
sources.
-/

open NumberField Finset Matrix Polynomial Lagrange MulAction Quotient ConjAct

namespace New.Variety

variable {E n : Type} [Field E] [CMBase E] [Fintype n] [DecidableEq n] {x g : GL n (𝔸f E)}
  {ℓ : Matrix n n ℂ} {y : GL n E} {𝔑 : 𝓞 E} {f : heckeAlgebra n ℂ 𝔑}

/-- For y, z in GL_n(E), conjugating the eigenline reflection `New.Variety.eigenReflection` of y by
Φ_{v₀}(z) gives the eigenline reflection of zyz⁻¹. -/
lemma ratConj_eigenReflection {ε : Prop} {μ : n} (z : GL n E) :
    ratConj z (eigenReflection ε y μ) = eigenReflection ε (z * y * z⁻¹) μ := by
  simp [eigenReflection, ratConj, ← aeval_smul, units_smul_def, ← map_inv]

/-- The signature condition is unchanged when `x` is multiplied by a similitude `g` (an element of
`GU E n`) on the right, or by a rational `z` on the left with `ℓ` conjugated by `z`. -/
lemma isSignedFrame_mul_iff (z : GL n E) (hg_GU : g ∈ GU E n) :
    IsSignedFrame (x * g) ℓ ↔ IsSignedFrame (toFinGL z * x) (ratConj z ℓ) :=
  ⟨fun hx ↦ by simpa [mul_assoc] using hx.mul z (inv_mem hg_GU),
    fun hx ↦ by simpa [ratConj] using hx.mul z⁻¹ hg_GU⟩

/-- If the unweighted count `countTerm ε f 1` has finite support, the count with weight `w` is a
finite sum over that support. For the chosen representative `(xK, y, μ)` of an orbit, the weight is
read at the characteristic polynomial of `y` and at the mark `μ`. -/
lemma finsum_countTerm_eq_sum {ε : Prop} (w : E[X] → n → ℂ)
    (h_fin : (countTerm ε f 1).support.Finite) :
    ∑ᶠ c : orbitRel.Quotient (GL n E) (MarkedTriple (levelGU n 𝔑) n), countTerm ε f w c =
      ∑ c ∈ h_fin.toFinset, countTerm ε f 1 c * w c.out.2.1.val.charpoly c.out.2.2 := by
  -- The weight `w` factors out of each term, so the terms vanish off the support of
  -- `countTerm ε f 1`.
  have h_term (c : orbitRel.Quotient (GL n E) (MarkedTriple (levelGU n 𝔑) n)) :
      countTerm ε f w c = countTerm ε f 1 c * w c.out.2.1.val.charpoly c.out.2.2 := by
    rcases h_out : c.out with ⟨q, z, μ⟩
    simp [countTerm, h_out, ite_mul]
  rw [funext h_term, finsum_eq_sum_of_support_subset]
  -- The remaining goal: the support of the weighted term lies in that of `countTerm ε f 1`.
  simp

/-- For `y` with separable characteristic polynomial, some `k` conjugates the diagonal matrix of
the listed roots `numberedRoots (Φ v₀) _` of that polynomial to Φ_{v₀}(y), and the diagonal matrix
with `1` at `i` and `-1` elsewhere to `markedReflection y i`, for every `i`. -/
private lemma exists_conj_diagonal_markedReflection (hy_sep : y.val.charpoly.Separable) :
    ∃ k : GL n ℂ,
      y.val.map (Φ v₀) = toConjAct k • diagonalAlgHom ℂ (numberedRoots (Φ v₀) y.val.charpoly) ∧
      ∀ i : n, markedReflection y i = toConjAct k • (diagonal (Pi.single i 2) - 1) := by
  set ρ : n ↪ ℂ := numberedRoots (Φ v₀) y.val.charpoly
  obtain ⟨k, hk⟩ : IsConj (diagonal ρ) (y.val.map (Φ v₀)) :=
    isConj_diagonal_of_isRoot_charpoly (isRoot_numberedRoots hy_sep _)
  have hy_diag : y.val.map (Φ v₀) = toConjAct k • diagonalAlgHom ℂ ρ := by
    simp [units_smul_def, hk.eq]
  refine ⟨k, hy_diag, fun i ↦ ?_⟩
  -- The Lagrange polynomial takes the value `±1` at each listed root.
  have h_eval : aeval (ρ : n → ℂ) (interpolate univ ρ fun j : n ↦ if j = i then 1 else -1) =
      fun j : n ↦ Pi.single i (2 : ℂ) j - 1 := by
    ext j
    simp only [aeval_pi_apply, coe_aeval_eq_eval, eval_interpolate_univ_node]
    grind
  rw [markedReflection_eq_aeval, hy_diag, aeval_smul, aeval_algHom_apply, h_eval,
    diagonalAlgHom_apply, ← diagonal_one, diagonal_sub]

/-- For `y` with separable characteristic polynomial, `markedReflection y i` is a reflection (a
matrix `u wᵀ - 1` with `w ⬝ᵥ u = 2`). It is the polynomial in Φ_{v₀}(y) that is `1` on the
eigenline of the `i`-th listed root `numberedRoots (Φ v₀) _ i` of the characteristic polynomial and
`-1` on the other eigenlines. -/
lemma isReflection_markedReflection (hy_sep : y.val.charpoly.Separable) (i : n) :
    IsReflection (markedReflection y i) := by
  obtain ⟨k, h_eig⟩ : ∃ k : GL n ℂ,
      markedReflection y i = toConjAct k • (diagonal (Pi.single i 2) - 1) :=
    (exists_conj_diagonal_markedReflection hy_sep).imp fun k ⟨_, h_eig⟩ ↦ h_eig i
  -- Take for `u` the `i`-th basis vector and for `w` twice that vector.
  have h_uw : diagonal (Pi.single i 2) = vecMulVec (Pi.single i (1 : ℂ)) (Pi.single i 2) := by
    ext a b
    grind [vecMulVec_apply, diagonal_apply]
  rw [h_eig, h_uw, units_smul_def, ofConjAct_toConjAct]
  exact IsReflection.conj k ⟨Pi.single i 1, Pi.single i 2, by simp, rfl⟩

/-- Let `y` have separable characteristic polynomial, and let `J` be a reflection fixed by
conjugation with Φ_{v₀}(y). Then `J` equals `markedReflection y i` for exactly one `i`, and
Φ_{v₀}(y) acts on the image of `J + 1` by the `i`-th listed root `numberedRoots (Φ v₀) _ i` of its
characteristic polynomial. -/
lemma exists_eq_markedReflection_iff_of_ratConj_eq (hy_sep : y.val.charpoly.Separable)
    {J : Matrix n n ℂ} (hJ : IsReflection J) (h_fix : ratConj y J = J) :
    ∃ i : n, y.val.map (Φ v₀) * (J + 1) = numberedRoots (Φ v₀) y.val.charpoly i • (J + 1) ∧
      ∀ j : n, J = markedReflection y j ↔ i = j := by
  -- Diagonalise: Φ_{v₀}(y) = k • diagonal ρ with distinct `ρ i`; then `markedReflection y i` is
  -- `k • (2 e_i e_iᵀ - 1)`. A reflection `k • (u wᵀ - 1)` that commutes with `k • diagonal ρ` has
  -- `u wᵀ` diagonal, so `u wᵀ = 2 e_i e_iᵀ` for one `i`.
  set ρ : n ↪ ℂ := numberedRoots (Φ v₀) y.val.charpoly
  obtain ⟨k, hy_diag, h_eig⟩ : ∃ k : GL n ℂ, y.val.map (Φ v₀) = toConjAct k • diagonalAlgHom ℂ ρ ∧
      ∀ i : n, markedReflection y i = toConjAct k • (diagonal (Pi.single i 2) - 1) :=
    exists_conj_diagonal_markedReflection hy_sep
  -- In the basis `k` the reflection `J` is `u wᵀ - 1` with `w ⬝ᵥ u = 2`.
  obtain ⟨u, w, h_dot, hJ_uw⟩ : IsReflection ((toConjAct k)⁻¹ • J) := by
    simpa [units_smul_def] using hJ.conj k⁻¹
  obtain rfl : J = toConjAct k • (vecMulVec u w - 1) := inv_smul_eq_iff.mp hJ_uw
  -- As `J` is fixed, `diagonal ρ` commutes with `u wᵀ`; so `u a * w b = 0` for `a ≠ b`.
  have h_comm : diagonal ρ * vecMulVec u w = vecMulVec u w * diagonal ρ := by
    rw [ratConj, units_smul_def, ofConjAct_toConjAct, Units.mul_inv_eq_iff_eq_mul] at h_fix
    simpa [hy_diag, ← smul_mul', mul_sub, sub_mul, smul_left_cancel_iff] using h_fix
  have h_diag (a b : n) : a = b ∨ u a = 0 ∨ w b = 0 := by
    have h_entry : ρ a * (u a * w b) = u a * w b * ρ b := by
      simpa [diagonal_mul, mul_diagonal, vecMulVec_apply] using congrFun₂ h_comm a b
    have h_prod : (ρ a - ρ b) * (u a * w b) = 0 := by linear_combination h_entry
    simpa [sub_eq_zero] using h_prod
  -- Some term `w i * u i` of `w ⬝ᵥ u = 2` is not zero; by `h_diag`, `u` and `w` vanish off `i`.
  obtain ⟨i, -, h_wu_ne⟩ := exists_ne_zero_of_sum_ne_zero (h_dot.trans_ne two_ne_zero)
  have h_off (b : n) (hb : b ≠ i) : w b * u b = 0 := by grind [h_diag b i]
  have h_wu_two : w i * u i = 2 := by rw [← h_dot, dotProduct, Fintype.sum_eq_single i h_off]
  have h_uw : vecMulVec u w = diagonal (Pi.single i 2) := by
    ext a b
    grind [vecMulVec_apply, diagonal_apply]
  rw [h_uw]
  refine ⟨i, ?_, fun j ↦ ?_⟩
  · -- `J + 1 = k • diagonal (Pi.single i 2)`, on which Φ_{v₀}(y) acts by `ρ i`.
    have h_ρ : diagonal ρ * diagonal (Pi.single i (2 : ℂ)) = ρ i • diagonal (Pi.single i 2) := by
      simp +contextual [← diagonal_smul, Pi.single_apply]
    simp [smul_sub, hy_diag, ← smul_mul', h_ρ, smul_comm (ρ i)]
  · rw [h_eig, smul_left_cancel_iff, sub_left_inj, diagonal_injective.eq_iff]
    exact ⟨fun h ↦ by simpa [Pi.single_apply] using congrFun h i, fun h ↦ by rw [h]⟩

/-- For `y` with separable characteristic polynomial, each `markedReflection y i` is a reflection
(`isReflection_markedReflection`), and a reflection `J` fixed by conjugation with Φ_{v₀}(y) equals
`markedReflection y i` for exactly one `i`, whose eigenline contains the image of `J + 1`
(`exists_eq_markedReflection_iff_of_ratConj_eq`). -/
lemma isReflection_markedReflection_and_exists_eq_iff (hy_sep : y.val.charpoly.Separable) :
    (∀ i : n, IsReflection (markedReflection y i)) ∧
    ∀ J : Matrix n n ℂ, IsReflection J → ratConj y J = J →
      ∃ i : n, y.val.map (Φ v₀) * (J + 1) = numberedRoots (Φ v₀) y.val.charpoly i • (J + 1) ∧
        ∀ j : n, J = markedReflection y j ↔ i = j :=
  ⟨isReflection_markedReflection hy_sep, fun _ hJ h_fix ↦
    exists_eq_markedReflection_iff_of_ratConj_eq hy_sep hJ h_fix⟩

/-- Under the permutation representation of a group `G` on `k[H]`, the coefficient of `g • v` at
`g • q` is the coefficient of `v` at `q`. -/
private lemma _root_.Representation.coeff_ofMulAction_smul {G H k : Type*} [Group G] [MulAction G H]
    [Semiring k] (g : G) (v : MonoidAlgebra k H) (q : H) :
    (Representation.ofMulAction k G H g v).coeff (g • q) = v.coeff q := by
  simp

/-- For `x` in the level `K = levelGU n 𝔑`, the function `heckeCosetFn f` of an element `f` of the
Hecke algebra takes the same value at the cosets of `x⁻¹ g x` and of `g`. -/
lemma heckeAlgebra.heckeCosetFn_conj (hx_level : x ∈ levelGU n 𝔑) :
    heckeCosetFn f (x⁻¹ * g * x) = heckeCosetFn f g := by
  -- `f` sends the basis vector of the coset `K` to the vector `v` whose coefficients are the values
  -- of `heckeCosetFn f`; as `f` lies in the Hecke algebra, `v` is fixed by `x ∈ K`.
  set π := Representation.ofMulAction ℂ (GL n (𝔸f E)) (GL n (𝔸f E) ⧸ levelGU n 𝔑)
  set v : MonoidAlgebra ℂ (GL n (𝔸f E) ⧸ levelGU n 𝔑) :=
    π.asAlgebraHom f.val (MonoidAlgebra.single ⟦1⟧ 1)
  have h_fixed : π x v = v := by simpa using f.2.2 single_one_mem_levelSpace ⟨x, hx_level⟩
  calc heckeCosetFn f ↑(x⁻¹ * g * x) = v.coeff (x⁻¹ • ↑g) := by
        simp [v, π, cosetFn, QuotientGroup.mk_mul_of_mem _ hx_level]
    _ = (π x v).coeff (x • x⁻¹ • ↑g) := (Representation.coeff_ofMulAction_smul x v _).symm
    _ = heckeCosetFn f ↑g := by rw [h_fixed, smul_inv_smul, heckeCosetFn, cosetFn]

/-- If the function `heckeCosetFn f` of an element `f` of the Hecke algebra does not vanish at the
coset of `g`, then `g` lies in `GUPlus E n`, the similitudes whose inverse has integral
entries. -/
lemma heckeAlgebra.mem_GUPlus_of_ne_zero (hg_ne : heckeCosetFn f g ≠ 0) : g ∈ GUPlus E n := by
  -- `g` lies in the coset of some `d` in `GUPlus E n`, and the level is contained in `GUPlus E n`.
  obtain ⟨d, hd_mem, hd_coset⟩ : ∃ d ∈ GUPlus E n, (d : GL n (𝔸f E) ⧸ levelGU n 𝔑) = g :=
    spanOn.exists_mem_of_cosetFn_ne_zero f.2.1 hg_ne
  simpa using mul_mem hd_mem (mem_GUPlus_of_mem_levelGU (QuotientGroup.eq.mp hd_coset))

open scoped Classical in
/-- The term `countTerm ε f w` of the orbit of the triple `(xK, y, μ)` may be computed at this
triple: if `x` is a signed frame for `eigenReflection ε y μ`, it is
`heckeCosetFn f (invAutInFrame y x) * w (charpoly y) μ` with `invAutInFrame y x = x⁻¹ y⁻¹ x`, and
otherwise it is `0`. (`countTerm` itself reads a chosen representative.) -/
lemma countTerm_mk {ε : Prop} {μ : n} {w : E[X] → n → ℂ} :
    countTerm ε f w ⟦(x, y, μ)⟧ =
      if IsSignedFrame x (eigenReflection ε y μ) then
        heckeCosetFn f (invAutInFrame y x) * w y.val.charpoly μ
      else 0 := by
  -- The chosen representative of the orbit is the translate of `(x, y, μ)` by some `z`.
  obtain ⟨z, hz : (⟦toFinGL z * x⟧, z * y * z⁻¹, μ) = _⟩ :=
    mk_out (s := orbitRel (GL n E) (MarkedTriple (levelGU n 𝔑) n)) (⟦x⟧, y, μ)
  -- The chosen representative of the coset of `toFinGL z * x` is `toFinGL z * x * k`, `k` in the
  -- level.
  obtain ⟨⟨k, hk_level⟩, hk_out⟩ := QuotientGroup.mk_out_eq_mul (levelGU n 𝔑) (toFinGL z * x)
  have h_charpoly : (z * y * z⁻¹).val.charpoly = y.val.charpoly := by simp
  have h_aut : invAutInFrame (z * y * z⁻¹) (toFinGL z * x * k) = k⁻¹ * invAutInFrame y x * k := by
    simp [invAutInFrame, mul_assoc]
  -- Conjugation by `k` does not change the value of `f`.
  rw [← heckeAlgebra.heckeCosetFn_conj hk_level, countTerm, ← hz]
  -- Neither the signature condition nor the characteristic polynomial sees `z` and `k`.
  dsimp only
  rw [hk_out, h_aut, h_charpoly, ← ratConj_eigenReflection, mul_assoc,
    ← isSignedFrame_mul_iff z (inv_mem (Subgroup.mem_inf.mp hk_level).left), mul_inv_cancel_right]

end New.Variety
