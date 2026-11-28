import Lib.GaloisRep.Main.Defs
import Lib.LocalGL.Iwahori.HeckeDegrees

/-!
# Chains of roots of the Hecke polynomial of a spherical vector

Let ρ be a smooth representation of GL_N(E_w) with an invariant scalar product B, q = `w.q` the norm
of w, and x ≠ 0 a vector fixed by GL_N(O_w) = `localIntGL` with eigenvalues t_j for the Hecke
operators `heckeGL ρ j`. Its Hecke polynomial is P = `heckePoly q N t`, where
`heckePoly q m t` = Σ_{j ≤ m} (−1)^j q^(j(j−1)/2) t_j X^(m−j).

* `New.Patching.HasRootChain`: P(dX) is (X − 1)(X − q)⋯(X − q^(t−1)) times a divisor of a given
  polynomial.
* `New.Patching.isRoot_chain_of_norm`: a root c with |c|² q^k = q^N starts a chain c, cq, …,
  cq^(k−1) of roots.
* `New.Patching.pairing_aeval_heckeCoset_eq_zero`: of a chain of roots, the operator U of diag(ϖ, 1,
  …, 1) at the level `proIwahori` sees only the top one. If P is a chain with top root c' times S,
  then x is orthogonal to (U − c') S(U) y for every y fixed by `proIwahori`.
* `New.Patching.chain_lemma`: the common source of both results, with a lower bound for the top root
  of a chain (`New.Patching.le_norm_sq_of_isRoot_of_not_isRoot_mul`).

Notions from other files:
* `New.heckeGL`: The j-th Hecke operator on a representation π of GL_n(E_w): the action
  (`New.heckeFun`) of the indicator function of `New.basicDoubleCoset` j, for K = GL_n(O_w).
* `New.proIwahori`: The pro-p Iwahori subgroup of GL_n(O_w): matrices that are upper triangular with
  ones on the diagonal modulo the maximal ideal. `New.partialHecke ρ r m x` is a partial Hecke sum
  of translates of x, with `partialHecke ρ 0 m x = heckeGL ρ m x` and `partialHecke ρ r 0 x = x`.

## Relation to the literature

Known result: the Satake parameters of unitary unramified representations of GL_N come in chains.
Both statements follow from Tadić's classification of the unitary dual and the geometric lemma of
Bernstein and Zelevinsky. The file proves them directly, by two counts of hyperplanes: a root c with
cq not a root has |c|² ≥ q^(N−2), and with the symmetry y ↦ q^(N−1)/ȳ of the roots this gives the
chain; the same counts let the roots of a chain below the top one be cancelled one at a time.
Source: Tadić, Classification of unitary representations in irreducible representations of general
linear group (non-archimedean case), Ann. ENS 19 (1986); Bernstein, P-invariant distributions on
GL(N), LNM 1041 (1983) for the inequality at the ends of segments.
-/

open ComplexOrder Finset Module New Pi Polynomial Valued Complex

/-- P has the chain of roots d, dq, …, dq^{t−1}, and the other factor divides e after scaling:
P(dX) equals (X − 1)(X − q)⋯(X − q^{t−1}) times a divisor of the polynomial e. -/
def New.Patching.HasRootChain (P e : ℂ[X]) (q d : ℂ) (t : ℕ) : Prop :=
  ∃ S : ℂ[X], P.comp (C d * X) = (∏ i ∈ range t, (X - C (q ^ i))) * S ∧ S ∣ e

variable {E : Type _} [Field E] [NumberField E] {w : FinPlace E} {N : ℕ} [NeZero N]
  {ρ : Rep ℂ (GL (Fin N) (LocField w))} [IsSmoothRep ρ.ρ]
  {B : ρ →ₗ⋆[ℂ] ρ →ₗ[ℂ] ℂ} {x : ρ} {P : ℂ[X]} {t : ℕ → ℂ}

omit [NeZero N] [IsSmoothRep ρ.ρ] in
/-- If `U'` is adjoint to `U` on a set `S` that `U` keeps, then on `S` the conjugate of `G`,
evaluated at `U'`, is adjoint to `G (U)`. -/
lemma New.Patching.adjoint_aeval_map_starRingEnd {U U' : End ℂ ρ} (S : Set ρ)
    (adj : ∀ y ∈ S, U y ∈ S ∧ ∀ a : ρ, B (U' a) y = B a (U y)) (G : ℂ[X]) (a : ρ) :
    ∀ y ∈ S, B (aeval U' (G.map (starRingEnd ℂ)) a) y = B a (aeval U G y) := by
  induction G using recOnHorner generalizing a with
  | M0 => simp
  | MC G c _ _ ih => simp_all
  | MX G _ ih => simp_all [mul_comm]

omit [NeZero N] [IsSmoothRep ρ.ρ] in
/-- Let `x` be fixed by `GL_N(O_w)` and `ϖ` a uniformiser. Then `x` is the translate by
`diag(ϖ⁻¹, …, ϖ⁻¹)` of the top partial Hecke sum `partialHecke ρ 0 N x`. -/
private lemma New.Patching.eq_apply_partialHecke_zero_top
    (hx : x ∈ levelSpace ρ.ρ (localIntGL (Fin N) w)) {ϖ : (LocField w)ˣ}
    (hϖ : v ϖ.val = WithZero.exp (-1)) :
    x = ρ.ρ (diagGL fun _ : Fin N ↦ ϖ⁻¹) (partialHecke ρ.ρ 0 N x) := by
  let ρ' : Representation ℂ (GL (Fin N) (LocField w)) ρ := ρ.ρ.comp invTransposeGL.toMonoidHom
  have hx' : x ∈ levelSpace ρ' (localIntGL (Fin N) w) := by simp_all [ρ']
  have h_sum : 0 + (N + 0) = N := by simp
  have h_dual :
      partialHecke ρ' 0 0 x = ρ.ρ (diagGL fun _ : Fin N ↦ ϖ⁻¹) (partialHecke ρ.ρ 0 N x) := by
    simpa [ρ'] using partialHecke_dual hϖ hx N h_sum
  rw [← h_dual, partialHecke_zero_right hx']

omit [IsSmoothRep ρ.ρ] in
/-- Let `x` be fixed by `GL_N(O_w)` and `ϖ` a uniformiser. Then `x` is the translate by
`diag(1, ϖ⁻¹, …, ϖ⁻¹)` of the top partial Hecke sum `partialHecke ρ 1 (N - 1) x`. -/
private lemma New.Patching.eq_apply_partialHecke_one_top
    (hx : x ∈ levelSpace ρ.ρ (localIntGL (Fin N) w)) {ϖ : (LocField w)ˣ}
    (hϖ : v ϖ.val = WithZero.exp (-1)) :
    x = ρ.ρ (diagGL fun i : Fin N ↦ if i = 0 then 1 else ϖ⁻¹)
      (partialHecke ρ.ρ 1 (N - 1) x) := by
  let ρ' : Representation ℂ (GL (Fin N) (LocField w)) ρ := ρ.ρ.comp invTransposeGL.toMonoidHom
  have hx' : x ∈ levelSpace ρ' (localIntGL (Fin N) w) := by simp_all [ρ']
  have h_sum : 1 + (N - 1 + 0) = N := by grind [NeZero.ne N]
  have h_dual : partialHecke ρ' 1 0 x =
      ρ.ρ (diagGL fun i : Fin N ↦ if i = 0 then 1 else ϖ⁻¹) (partialHecke ρ.ρ 1 (N - 1) x) := by
    simpa [ρ', Nat.lt_one_iff, Fin.val_eq_zero_iff] using partialHecke_dual hϖ hx (N - 1) h_sum
  rw [← h_dual, partialHecke_zero_right hx']

/-- Let `x` be fixed by `GL_N(O_w)`, let `ϖ` be a uniformiser (valuation `exp (-1)`), and let `a` be
the inverse of `ρ(diag(ϖ, 1, …, 1))`. Write `M(y)` for the mean of `ρ` over `proIwahori` applied to
`y`, and let `partialHecke ρ r m x` be the partial Hecke sum of `ρ g x` over the cosets in
`New.partialCosets r m`. If `1 + (i + 1 + j) = N`, the count of `New.partialHecke_hyperplane_count`,
read in the dual representation, gives `q^(N-1) • M(a (partialHecke ρ 1 (i+1) x)) = q^j • (M(a
(partialHecke ρ 0 (i+1) x)) - partialHecke ρ 1 i x)`, where `q = w.q`. -/
lemma New.Patching.compactMean_apply_inv_partialHecke_one_succ
    (hx : x ∈ levelSpace ρ.ρ (localIntGL (Fin N) w)) {ϖ : (LocField w)ˣ}
    (hϖ : v ϖ.val = WithZero.exp (-1)) {i j : ℕ} (h_sum : 1 + (i + 1 + j) = N) :
    (w.q ^ (N - 1) : ℂ) • compactMean ρ.ρ proIwahori
        (ρ.ρ (diagGL (mulSingle 0 ϖ))⁻¹ (partialHecke ρ.ρ 1 (i + 1) x)) =
      (w.q ^ j : ℂ) • (compactMean ρ.ρ proIwahori
          (ρ.ρ (diagGL (mulSingle 0 ϖ))⁻¹ (partialHecke ρ.ρ 0 (i + 1) x)) -
        partialHecke ρ.ρ 1 i x) := by
  let ρ' : Representation ℂ (GL (Fin N) (LocField w)) ρ := ρ.ρ.comp invTransposeGL.toMonoidHom
  have hx' : x ∈ levelSpace ρ' (localIntGL (Fin N) w) := by simp_all [ρ']
  -- `diagGL c₀` and `diagGL c₁` are the matrices of `partialHecke_dual` for `m = 0` and `m = 1`
  let c₀ (_ : Fin N) : (LocField w)ˣ := ϖ⁻¹
  let c₁ (i : Fin N) : (LocField w)ˣ := if i = 0 then 1 else ϖ⁻¹
  have single_eq : mulSingle 0 ϖ = c₀⁻¹ * c₁ := by aesop
  have dual₀ (i : ℕ) {j : ℕ} (h_sum : 0 + (i + j) = N) :
      partialHecke ρ' 0 j x = ρ.ρ (diagGL c₀) (partialHecke ρ.ρ 0 i x) := by
    simpa [ρ', c₀] using partialHecke_dual hϖ hx i h_sum
  have dual₁ (i : ℕ) {j : ℕ} (h_sum : 1 + (i + j) = N) :
      partialHecke ρ' 1 j x = ρ.ρ (diagGL c₁) (partialHecke ρ.ρ 1 i x) := by
    simpa [ρ', c₁, Nat.lt_one_iff, Fin.val_eq_zero_iff] using partialHecke_dual hϖ hx i h_sum
  -- the map `φ` is admissible because `diagGL c₁` conjugates `invTransposeGL k⁻¹` into
  -- `proIwahori`
  let φ : End ℂ ρ := compactMean ρ.ρ proIwahori * ρ.ρ (diagGL c₁⁻¹)
  have hφ (k : GL (Fin N) (LocField w)) (h_row : ∀ i ≠ (0 : Fin N), ∀ l ≠ i, k.val i l = 0)
      (hk : k⁻¹ ∈ proIwahori) (z : ρ) : φ (ρ' k⁻¹ z) = φ z := by
    have conj_mem :
        (permGL 1 * diagGL c₁)⁻¹ * invTransposeGL k⁻¹ * (permGL 1 * diagGL c₁) ∈ proIwahori := by
      obtain ⟨-, -, hk_diag⟩ := mem_proIwahori.mp (inv_mem hk)
      obtain ⟨hk_int, -⟩ := hk
      have hk_dual : invTransposeGL k⁻¹ ∈ localIntGL (Fin N) w :=
        (invTransposeGL_mem_intGL _).mpr hk_int
      refine mem_proIwahori_iff_blockParahoric.mpr
        (conj_monomial_mem_blockParahoric c₁ 1 _ (d := 0) ⟨⟨hk_dual, nofun⟩, hk_diag⟩ ?_)
      -- the valuation condition on the entries, row by row
      suffices h_log : ∀ a b : Fin N, k.val b a = 0 ∨
          ((if b = 0 then (0 : ℤ) else 1) + if b < a then 1 else 0) ≤ if a = 0 then 0 else 1 by
        simpa [c₁, invTransposeGL, transposeGL,
          apply_ite fun u : (LocField w)ˣ ↦ WithZero.log (v u.val), hϖ] using h_log
      grind
    simpa [φ, ρ'] using compactMean_apply (ρ := ρ.ρ) conj_mem (ρ.ρ (diagGL c₁⁻¹) z)
  have h_count : (w.q : ℂ) ^ (Fin.rev (0 : Fin N)).val •
        φ (ρ' (diagGL (mulSingle 0 ϖ)) (partialHecke ρ' ((0 : Fin N).val + 1) j x)) =
      φ ((w.q : ℂ) ^ j • (partialHecke ρ' (0 : Fin N).val (j + 1) x -
        partialHecke ρ' ((0 : Fin N).val + 1) (j + 1) x)) :=
    partialHecke_hyperplane_count hϖ hx' 0 hφ j
  rw [Fin.val_zero, dual₁ _ h_sum, dual₀ (i + 1) (by lia : 0 + (i + 1 + (j + 1)) = N),
    dual₁ i (by lia : 1 + (i + (j + 1)) = N)] at h_count
  have inv_diag (t : Fin N → (LocField w)ˣ) :
      invTransposeGL (diagGL t) = diagGL (t⁻¹ : Fin N → (LocField w)ˣ) :=
    Units.ext (Matrix.diagonal_transpose _)
  -- `partialHecke ρ.ρ 1 i x` is fixed by `proIwahori`, so the mean leaves it unchanged
  have h_fixed : compactMean ρ.ρ proIwahori (partialHecke ρ.ρ 1 i x) = partialHecke ρ.ρ 1 i x :=
    compactMean_eq_self _ (levelSpace_anti (proIwahori_le_blockParahoric fun _ _ h ↦ by omega)
      (partialHecke_mem_levelSpace hx))
  simpa [φ, ρ', single_eq, inv_diag, h_fixed] using h_count

omit [IsSmoothRep ρ.ρ] in
/-- Let `x` be fixed by `GL_N(O_w)` and `ϖ` a uniformiser. The inverse of `ρ(diag(ϖ, 1, …, 1))`
carries the top partial Hecke sum `partialHecke ρ 0 N x` to `partialHecke ρ 1 (N - 1) x`. -/
lemma New.Patching.apply_inv_partialHecke_zero_top
    (hx : x ∈ levelSpace ρ.ρ (localIntGL (Fin N) w)) {ϖ : (LocField w)ˣ}
    (hϖ : v ϖ.val = WithZero.exp (-1)) :
    ρ.ρ (diagGL (mulSingle 0 ϖ))⁻¹ (partialHecke ρ.ρ 0 N x) = partialHecke ρ.ρ 1 (N - 1) x := by
  -- both sides are translates of `x`
  let c₀ (_ : Fin N) : (LocField w)ˣ := ϖ⁻¹
  let c₁ (i : Fin N) : (LocField w)ˣ := if i = 0 then 1 else ϖ⁻¹
  have single_eq : mulSingle 0 ϖ = c₀⁻¹ * c₁ := by aesop
  have h_top : ρ.ρ (diagGL c₀) (partialHecke ρ.ρ 0 N x) =
      ρ.ρ (diagGL c₁) (partialHecke ρ.ρ 1 (N - 1) x) :=
    (eq_apply_partialHecke_zero_top hx hϖ).symm.trans (eq_apply_partialHecke_one_top hx hϖ)
  simpa [single_eq, ρ.ρ.inv_apply_eq_iff] using h_top

omit [NeZero N] [IsSmoothRep ρ.ρ] in
/-- Let `x` be fixed by `GL_N(O_w)` and `ϖ` a uniformiser. The top partial Hecke sum
`partialHecke ρ 0 N x` vanishes only for `x = 0`. -/
lemma New.Patching.eq_zero_of_partialHecke_zero_top
    (hx : x ∈ levelSpace ρ.ρ (localIntGL (Fin N) w)) {ϖ : (LocField w)ˣ}
    (hϖ : v ϖ.val = WithZero.exp (-1))
    (h_top : partialHecke ρ.ρ 0 N x = 0) : x = 0 := by
  rw [eq_apply_partialHecke_zero_top hx hϖ, h_top, map_zero]

variable (hx : x ∈ levelSpace ρ.ρ (localIntGL (Fin N) w)) in
include hx in
/-- Let x be fixed by GL_N(O_w) (`hx`) and ϖ a uniformiser, and let a be the inverse of ρ(diag(ϖ, 1,
…, 1)). Then (a) the count of `New.partialHecke_hyperplane_count`, read in the dual representation,
gives, for i + 1 + j = N − 1, a recursion between the mean over `proIwahori` of a applied to the
partial Hecke sums `partialHecke ρ 0` and `partialHecke ρ 1`; (b) a carries `partialHecke ρ 0 N x`
to `partialHecke ρ 1 (N - 1) x`; (c) `partialHecke ρ 0 N x` vanishes only for x = 0. -/
lemma New.Patching.partialHecke_hyperplane_count_dual {ϖ : (LocField w)ˣ}
    (hϖ : v ϖ.val = WithZero.exp (-1)) :
    let a : ρ →ₗ[ℂ] ρ := ρ.ρ (diagGL (mulSingle 0 ϖ))⁻¹
    -- (a)
    (∀ i j : ℕ, 1 + (i + 1 + j) = N →
      (w.q ^ (N - 1) : ℂ) • compactMean ρ.ρ proIwahori (a (partialHecke ρ.ρ 1 (i + 1) x)) =
        (w.q ^ j : ℂ) •
          (compactMean ρ.ρ proIwahori (a (partialHecke ρ.ρ 0 (i + 1) x)) -
            partialHecke ρ.ρ 1 i x)) ∧
    -- (b)
    a (partialHecke ρ.ρ 0 N x) = partialHecke ρ.ρ 1 (N - 1) x ∧
    -- (c)
    (partialHecke ρ.ρ 0 N x = 0 → x = 0) := by
  intro a
  exact ⟨fun i j h_sum ↦ compactMean_apply_inv_partialHecke_one_succ hx hϖ h_sum,
    apply_inv_partialHecke_zero_top hx hϖ, eq_zero_of_partialHecke_zero_top hx hϖ⟩

omit [NeZero N] [IsSmoothRep ρ.ρ] in
/-- Suppose that `P (U)` kills `y`, and that `(P / (X - c)) (U)` still kills `y` for every root
`c ≠ 0` of `P` for which `q * c` is also a root. Let `P = (∏ i < k, (d X - q ^ i)) * R`. If
`q ^ k / d` is a root of `P`, then `R (U)` kills `y`: the chain `q ^ i / d`, `i < k`, cancels. -/
lemma New.Patching.aeval_cofactor_eq_zero {U : End ℂ ρ} {y : ρ} {P : ℂ[X]} {q d : ℂ} (hq : 1 < q)
    (aeval_P : aeval U P y = 0)
    (two_roots :
      ∀ {c : ℂ} (F : ℂ[X]), (X - C c) * F = P → P.IsRoot (q * c) → c ≠ 0 → aeval U F y = 0)
    (hd : d ≠ 0) (k : ℕ) (R : ℂ[X]) (hroot : P.IsRoot (q ^ k / d))
    (hP : P = (∏ i ∈ range k, (C d * X - C (q ^ i))) * R) :
    aeval U R y = 0 := by
  induction k generalizing R with
  | zero => simpa [hP] using aeval_P
  | succ k ih =>
    simp only [prod_range_succ, mul_assoc, pow_succ', mul_div_assoc] at hP hroot
    -- `U` scales `R (U) y` by `q ^ k / d`, and the shorter product `Q` at `U` kills it.
    have h_root_k : P.IsRoot (q ^ k / d) := by simp [hP, field]
    have eigen_R : U (aeval U R y) = (d⁻¹ * q ^ k) • aeval U R y := by
      -- `-map_pow` is needed: without it the normal forms of `ih` and of the goal differ.
      simpa [sub_eq_zero, ← eq_inv_smul_iff₀ hd, smul_smul, -map_pow] using ih _ h_root_k hP
    set Q : ℂ[X] := ∏ i ∈ range k, (C d * X - C (q ^ i))
    have cancel : (X - C (q ^ k / d)) * (d • Q * R) = P :=
      Polynomial.funext fun a ↦ by simp [hP, field]
    have killed : aeval U Q (aeval U R y) = 0 := by
      simpa [hd] using two_roots _ cancel hroot (by simp [(one_pos.trans hq).ne', hd])
    -- `Q` does not vanish at that scalar, as `1 < q`.
    have eval_ne : Q.eval (d⁻¹ * q ^ k) ≠ 0 := by
      simp +contextual [Q, eval_prod, prod_eq_zero_iff, hd, sub_eq_zero,
        (pow_lt_pow_right₀ hq _).ne']
    rwa [End.aeval_apply_of_mem_apply_eq_smul eigen_R, smul_eq_zero_iff_right eval_ne] at killed

omit [NeZero N] [IsSmoothRep ρ.ρ] in
/-- If `R (U)` kills every `T j` and the adjoint `U'` of `U` keeps the span of `T 0, …, T n`, then
the conjugate of `R`, evaluated at `U'`, kills `T 0`. -/
lemma New.Patching.aeval_conj_eq_zero {U U' : End ℂ ρ} {T : ℕ → ρ} {R : ℂ[X]} {n : ℕ} {a : ℂ}
    {b c : ℕ → ℂ} (hB : ∀ f ≠ (0 : ρ), 0 < B f f) (adj : ∀ y z : ρ, B (U' y) z = B y (U z))
    (kills_T : ∀ j : ℕ, aeval U R (T j) = 0) (U'_first : U' (T 0) = a • T n)
    (rec_U' : ∀ i < n, U' (T i.succ) = b i • (c i • U' (T 0) - T i)) :
    aeval U' (R.map (starRingEnd ℂ)) (T 0) = 0 := by
  have kills_span (F : ℂ[X]) : ∀ j ≤ n, aeval U R (aeval U' F (T j)) = 0 := by
    induction F using recOnHorner with
    | M0 => simp
    | MC F a _ _ ih => simp +contextual [ih, kills_T]
    | MX F _ ih =>
      rintro (_ | j) hj
      · simp [U'_first, ih]
      · simp [rec_U' j hj, U'_first, ih n, ih j (by lia)]
  -- The vector of the statement lies in that span, so it is orthogonal to itself.
  refine by_contra fun hne ↦ (hB _ hne).ne' ?_
  rw [adjoint_aeval_map_starRingEnd ⊤ (fun y _ ↦ ⟨trivial, fun z ↦ adj z y⟩) R _ _ trivial,
    kills_span _ 0 (Nat.zero_le n), map_zero]

/-- The Hecke polynomial of degree `m + 1` is `X` times that of degree `m`, plus the constant
`(-1) ^ (m + 1) * q ^ ((m + 1).choose 2) * t (m + 1)`. -/
private lemma New.Patching.heckePoly_succ (q m : ℕ) :
    heckePoly q (m + 1) t =
      X * heckePoly q m t + ((-1) ^ (m + 1) * q ^ (m + 1).choose 2 * t (m + 1)) • 1 := by
  ext k
  cases k with
  | zero => simp [coeff_one]
  | succ k => simp [coeff_one]

omit [NeZero N] [IsSmoothRep ρ.ρ] in
/-- Let `U (T j) = q ^ j • (t (j + 1) • T 0 - T (j + 1))` for all `j`, and `t 0 • T 0 = T 0`. Then
the Hecke polynomial of degree `m`, evaluated at `U`, sends `T 0` to
`(-1) ^ m * q ^ (m.choose 2)` times `T m`. -/
private lemma New.Patching.aeval_heckePoly_apply (U : End ℂ ρ) (T : ℕ → ρ) {q : ℕ}
    (ht_zero : t 0 • T 0 = T 0)
    (rec_U : ∀ j : ℕ, U (T j) = (q : ℂ) ^ j • (t j.succ • T 0 - T j.succ)) (m : ℕ) :
    aeval U (heckePoly q m t) (T 0) = ((-1) ^ m * q ^ m.choose 2 : ℂ) • T m := by
  induction m with
  | zero => simpa [heckePoly] using ht_zero
  | succ m ih =>
    -- write the next polynomial by `heckePoly_succ`; `U (T m)` is given by `rec_U`
    suffices h_lin :
        ((-1) ^ m * (q : ℂ) ^ m.choose 2) • (q : ℂ) ^ m • (t (m + 1) • T 0 - T (m + 1)) +
        ((-1) ^ (m + 1) * (q : ℂ) ^ (m + m.choose 2) * t (m + 1)) • T 0 =
        ((-1) ^ (m + 1) * (q : ℂ) ^ (m + m.choose 2)) • T (m + 1) by
      simpa [heckePoly_succ, ih, rec_U, Nat.choose] using h_lin
    module

omit [NeZero N] [IsSmoothRep ρ.ρ] in
/-- The action of `U'` on the quotient of a Hecke polynomial by `X - c`. Let `p m` be the Hecke
polynomial of degree `m`, with `p m (U) (T 0) = (-1) ^ m * q ^ (m.choose 2) • T m`, let
`T (n + 1) = 0`, and let `U' (T (i + 1)) = q ^ (n - i - 1) • ((t (i + 1) / q ^ n) • U' (T 0) - T i)`
for `i < n` and `U' (T 0) = q ^ n • (t (n + 1))⁻¹ • T n`, as in
`New.Patching.chain_lemma_of_adjoint`. For `m ≤ n + 1` and `c : ℂ` there is a polynomial `D` with
`(X - c) * D = p m - p m (c)` and `U' ((c • D + p m) (U) (T 0)) = (p m (q * c) / q ^ m) • U' (T 0) +
(q ^ n / q) • D (U) (T 0)`. -/
private lemma New.Patching.exists_mul_eq_sub_eval_and_apply (U U' : End ℂ ρ) (T : ℕ → ρ) {q n : ℕ}
    (q_ne : (q : ℂ) ≠ 0) (ht_last : t n.succ ≠ 0) (T_last : T (n + 1) = 0)
    (rec_U' : ∀ i < n,
      U' (T i.succ) = (q : ℂ) ^ (n - i.succ) • ((t i.succ / q ^ n) • U' (T 0) - T i))
    (U'_first : U' (T 0) = (q : ℂ) ^ n • (t n.succ)⁻¹ • T n)
    (aeval_p : ∀ m : ℕ, aeval U (heckePoly q m t) (T 0) = ((-1) ^ m * q ^ m.choose 2 : ℂ) • T m)
    (m : ℕ) (hm : m ≤ n.succ) (c : ℂ) :
    ∃ D : ℂ[X], (X - C c) * D = heckePoly q m t - C ((heckePoly q m t).eval c) ∧
      U' (aeval U (c • D + heckePoly q m t) (T 0)) =
        ((heckePoly q m t).eval (q * c) / q ^ m) • U' (T 0) +
          (q ^ n / q : ℂ) • aeval U D (T 0) := by
  induction m with
  | zero => exact ⟨0, by simp [heckePoly]⟩
  | succ m ih =>
    obtain ⟨D, hD, hU'⟩ := ih (Nat.lt_of_succ_le hm).le
    refine ⟨c • D + heckePoly q m t, ?_, ?_⟩
    · suffices h_poly : (X - C c) * (C c * D + heckePoly q m t) =
          X * heckePoly q m t - C c * C (eval c (heckePoly q m t)) by
        simpa [heckePoly_succ, smul_eq_C_mul] using h_poly
      linear_combination C c * hD
    · -- express everything by the `T j` and use the recursion for `U'`, or its end if `m = n`
      rw [map_add, LinearMap.add_apply, aeval_p]
      obtain rfl | hm : m = n ∨ m < n := by lia
      · simp [heckePoly_succ, T_last, U'_first, aeval_p, Nat.choose] at hU' ⊢
        linear_combination (norm := match_scalars <;> field) c • hU'
      · simp [heckePoly_succ, rec_U' m hm, aeval_p, Nat.choose, pow_sub₀ _ q_ne hm] at hU' ⊢
        linear_combination (norm := match_scalars <;> field) c • hU'

omit [NeZero N] [IsSmoothRep ρ.ρ] in
/-- The root bound behind `New.Patching.chain_lemma_of_adjoint`. Let `B` be positive definite, `U'`
adjoint to `U`, `x ≠ 0`, `1 < q` and `a ≠ 0`. Let `z` be an eigenvector of `U` for `c` with
`c • U' z = (a / q ^ (n + 1)) • U' x + (q ^ n / q) • z` and
`c * B x z * (q ^ (n + 1) - 1) = a * B x x`. Then `q ^ (n + 1) / q ^ 2 ≤ ‖c‖ ^ 2`. -/
private lemma New.Patching.le_norm_sq_of_pairing {U U' : End ℂ ρ} {x z : ρ} {c a : ℂ} {q n : ℕ}
    (hB : ∀ f ≠ (0 : ρ), 0 < B f f) (adj : ∀ a y : ρ, B (U' a) y = B a (U y)) (hq : 1 < (q : ℂ))
    (hx_ne : x ≠ 0) (ha : a ≠ 0) (U_z : U z = c • z)
    (U'_z : c • U' z = (a / q ^ (n + 1)) • U' x + (q ^ n / q : ℂ) • z)
    (pair_x : c * B x z * (q ^ (n + 1) - 1) = a * B x x) :
    (q : ℝ) ^ n.succ / q ^ 2 ≤ ‖c‖ ^ 2 := by
  have pow_sub_pos : 0 < (q : ℂ) ^ (n + 1) - 1 := sub_pos.mpr (one_lt_pow₀ hq n.succ_ne_zero)
  have x_pos : 0 < B x x := hB x hx_ne
  -- `z ≠ 0`, as `a ≠ 0`
  have z_pos : 0 < B z z := hB z fun hz ↦ ha (by simpa [hz, x_pos.ne'] using pair_x)
  -- Pair the formula for `U' z` with `z`.
  have pair_z : (‖c‖ ^ 2 - q ^ n / q) * B z z = starRingEnd ℂ a / q ^ (n + 1) * (c * B x z) := by
    have paired : starRingEnd ℂ c * (c * B z z) =
        starRingEnd ℂ a / q ^ (n + 1) * (c * B x z) + q ^ n / q * B z z := by
      simpa [adj, U_z] using congrArg (fun y : ρ ↦ B y z) U'_z
    linear_combination paired - B z z * mul_conj' c
  have gap : (‖c‖ ^ 2 - q ^ (n + 1) / q ^ 2 : ℂ) =
      ‖a‖ ^ 2 * B x x / q ^ (n + 1) / ((q ^ (n + 1) - 1) * B z z) := by
    rw [eq_div_iff (mul_pos pow_sub_pos z_pos).ne', ← mul_conj' a]
    linear_combination (norm := field) (q ^ (n + 1) - 1) * pair_z +
      starRingEnd ℂ a / q ^ (n + 1) * pair_x
  have gap_nonneg : 0 ≤ (‖c‖ ^ 2 - q ^ (n + 1) / q ^ 2 : ℂ) := gap.ge.trans' (by positivity)
  exact real_le_real.mp (by simpa using gap_nonneg)

omit [NeZero N] [IsSmoothRep ρ.ρ] in
/-- The linear algebra of the chain lemma. Let `B` be a positive definite sesquilinear form, and let
`U`, `U'` be mutually adjoint for `B`. Let `P = heckePoly q (n+1) t` with `1 < q`, `T 0 ≠ 0`,
`t 0 • T 0 = T 0` and `t (n+1) ≠ 0`, and suppose `U (T j) = q^j • (t (j+1) • T 0 - T (j+1))`, `U' (T
(i+1)) = q^(n-i-1) • ((t (i+1) / q^n) • U' (T 0) - T i)` for `i < n`,
`U' (T 0) = q^n • t (n+1)⁻¹ • T n` and `U (T n) = q^n • t (n+1) • T 0`. Then (a) every root `c` of
`P` such that `q * c` is not a root satisfies `q^(n+1) / q^2 ≤ ‖c‖^2`; and (b) if `d ≠ 0`, `q^k / d`
is a root of `P`, and `P = (∏_{i<k} (d X - q^i)) * R`, then `R` with complex-conjugated
coefficients, evaluated at `U'`, kills `T 0`. -/
lemma New.Patching.chain_lemma_of_adjoint (U U' : End ℂ ρ) (T : ℕ → ρ)
    (hB : ∀ f ≠ (0 : ρ), 0 < B f f)
    (adj : ∀ a y : ρ, B (U' a) y = B a (U y)) (adj' : ∀ a y : ρ, B (U a) y = B a (U' y)) {q n : ℕ}
    (hP_def : P = heckePoly q n.succ t) (hq : 1 < (q : ℂ)) (hT_ne : T 0 ≠ 0)
    (ht_zero : t 0 • T 0 = T 0) (ht_last : t n.succ ≠ 0)
    (rec_U : ∀ j : ℕ, U (T j) = (q : ℂ) ^ j • (t j.succ • T 0 - T j.succ))
    (rec_U' : ∀ i < n,
      U' (T i.succ) = (q : ℂ) ^ (n - i.succ) • ((t i.succ / q ^ n) • U' (T 0) - T i))
    (U'_first : U' (T 0) = (q : ℂ) ^ n • (t n.succ)⁻¹ • T n)
    (U_last : U (T n) = (q : ℂ) ^ n • t n.succ • T 0) :
    -- the top root of a chain is large
    (∀ c : ℂ, P.IsRoot c → ¬P.IsRoot (q * c) → q ^ n.succ / q ^ 2 ≤ ‖c‖ ^ 2) ∧
    -- a chain that goes on by one more root can be cancelled
    ∀ d ≠ (0 : ℂ), ∀ (k : ℕ) (R : ℂ[X]), P.IsRoot (q ^ k / d) →
      P = (∏ i ∈ range k, (C d * X - C (q ^ i : ℂ))) * R →
      aeval U' (R.map (starRingEnd ℂ)) (T 0) = 0 := by
  -- Write `x = T 0` and `p m` for the Hecke polynomial cut at degree `m`. Each `p m (U) x` is a
  -- multiple of `T m`. For a root `c` of `P`, the vector `z c = (P / (X - c))(U) x` satisfies
  -- `U (z c) = c • z c`, and the recursion for `U'` computes `U' (z c)`; pairing it with `U' x` and
  -- with `z c` gives the bound, and shows `z c = 0` when `q c` is a root too.
  have q_ne : (q : ℂ) ≠ 0 := (one_pos.trans hq).ne'
  have pow_sub_pos : 0 < (q : ℂ) ^ (n + 1) - 1 := sub_pos.mpr (one_lt_pow₀ hq n.succ_ne_zero)
  have T_last : T (n + 1) = 0 := by simpa [rec_U, q_ne] using U_last
  set x : ρ := T 0
  have aeval_p (m : ℕ) : aeval U (heckePoly q m t) x = ((-1) ^ m * q ^ m.choose 2 : ℂ) • T m :=
    aeval_heckePoly_apply U T ht_zero rec_U m
  have aeval_P : aeval U P x = 0 := by simpa [← hP_def, T_last] using aeval_p n.succ
  -- The formula for `U'` on the quotient `D c` of `P - P (c)` by `X - c`.
  have quot (c : ℂ) : ∃ D : ℂ[X], (X - C c) * D = P - C (P.eval c) ∧
      U' (aeval U (c • D + P) x) =
        (P.eval (q * c) / q ^ n.succ) • U' x + (q ^ n / q : ℂ) • aeval U D x := by
    simpa only [← hP_def] using exists_mul_eq_sub_eval_and_apply U U' T q_ne ht_last T_last rec_U'
      U'_first aeval_p n.succ le_rfl c
  choose D hD hU' using quot
  let z (c : ℂ) : ρ := aeval U (D c) x
  have U'_z (c : ℂ) :
      c • U' (z c) = (P.eval (q * c) / q ^ (n + 1)) • U' x + (q ^ n / q : ℂ) • z c := by
    simpa [aeval_P] using hU' c
  have U_z (c : ℂ) (hc : P.IsRoot c) : U (z c) = c • z c := by
    simpa [aeval_P, hc.eq_zero, sub_eq_zero] using congrArg (aeval U · x) (hD c)
  -- Pair the formula for `U' (z c)` with `U' x`, and use `U (U' x) = q ^ (2 n) x`.
  have pair_U' (y : ρ) : B (U' x) (U' y) = q ^ n * q ^ n * B x y := by
    simp [← adj', U'_first, U_last]
    field_simp [ht_last]
  have pair_x (c : ℂ) (hc : P.IsRoot c) :
      c * B x (z c) * (q ^ (n + 1) - 1) = P.eval (q * c) * B x x := by
    have paired : B (U' x) (c • U' (z c)) =
        B (U' x) ((P.eval (q * c) / q ^ (n + 1)) • U' x + (q ^ n / q : ℂ) • z c) := by rw [U'_z c]
    simp only [map_add, map_smul, pair_U', adj _ (z c), U_z c hc, smul_eq_mul] at paired
    linear_combination (norm := field) q / q ^ n * paired
  refine ⟨fun c hc hqc ↦
    -- Pair the formula for `U' (z c)` with `z c`, which is not `0` as `P (q c) ≠ 0`.
    le_norm_sq_of_pairing hB adj hq hT_ne hqc (U_z c hc) (U'_z c) (pair_x c hc), ?_⟩
  -- If `c ≠ 0` and `q c` are roots, then `U' (z c)` is a multiple of `z c`, and `z c` is
  -- orthogonal to `x`, hence to every `G (U) x`, itself included.
  have two_roots {c : ℂ} (F : ℂ[X]) (hF : (X - C c) * F = P) (hqc : P.IsRoot (q * c)) (hc : c ≠ 0) :
      aeval U F x = 0 := by
    have root : P.IsRoot c := by simp [← hF]
    obtain rfl : F = D c :=
      mul_left_cancel₀ (X_sub_C_ne_zero c) (by simp [hF, hD, root.eq_zero])
    have eigen_z : U' (z c) = c⁻¹ • (q ^ n / q : ℂ) • z c := by
      simpa [eq_inv_smul_iff₀ hc, hqc.eq_zero] using U'_z c
    have orth_x : B x (z c) = 0 := by simpa [hqc.eq_zero, hc, pow_sub_pos.ne'] using pair_x c root
    have orth (G : ℂ[X]) : B (aeval U G x) (z c) = 0 := by
      induction G using recOnHorner with
      | M0 => simp
      | MC G a _ _ ih => simp [ih, orth_x]
      | MX G _ ih => simp [← X_mul, adj', eigen_z, ih]
    exact by_contra fun hz ↦ (hB _ hz).ne' (orth _)
  intro d hd k R hroot hP
  have kills_x : aeval U R x = 0 := aeval_cofactor_eq_zero hq aeval_P two_roots hd k R hroot hP
  refine aeval_conj_eq_zero hB adj (fun j ↦ ?_) (U'_first.trans (smul_smul _ _ (T n))) rec_U'
  -- `T j` is a multiple of `p j (U) x` for the Hecke polynomial `p j` of degree `j`, and `R (U)`
  -- commutes with `p j (U)`.
  simpa [aeval_p, kills_x, q_ne] using congrArg (aeval U · x) (mul_comm R (heckePoly q j t))

/-- Let x ≠ 0 be a spherical eigenvector with Hecke polynomial P in a smooth unitary representation
of GL_N(E_w), q the norm of w, ϖ a uniformiser.
* Root bound: if P(c) = 0 and P(qc) ≠ 0, then |c|² ≥ q^(N−2), written q^N / q² to avoid subtraction.
* Orthogonality: let U be the Hecke operator of diag(ϖ, 1, …, 1) for the group `proIwahori`. If
d ≠ 0 and P(X/d) = ∏_{i ≤ k} (X − q^i) · S with S dividing R, so that c, cq, …, cq^k are roots for
c = 1/d, then x is orthogonal to ((dX − q^k) · R(dX))(U) y for every y fixed by `proIwahori`.

The root bound also follows from Tadić's classification of unitary spherical representations of
GL_N; the proof here is direct and does not use the classification. -/
lemma New.Patching.chain_lemma (hB : IsUnitary ρ.ρ B)
    (hx : x ∈ levelSpace ρ.ρ (localIntGL (Fin N) w))
    (hx_ne : x ≠ 0) (hP_eq : P = heckePoly w.q N t) (ht : ∀ j : ℕ, heckeGL ρ.ρ j x = t j • x)
    {ϖ : (LocField w)ˣ} (hϖ : v ϖ.val = WithZero.exp (-1)) :
    -- root bound: the top root of a chain is large
    (∀ c : ℂ, P.IsRoot c → ¬P.IsRoot (w.q * c) → w.q ^ N / w.q ^ 2 ≤ ‖c‖ ^ 2) ∧
    -- orthogonality to `x`, once all roots but the top one of a chain of `k + 1` are cancelled
    ∀ d ≠ (0 : ℂ), ∀ (k : ℕ) (R : ℂ[X]),
      HasRootChain P R w.q d⁻¹ (k + 1) →
      ∀ y ∈ levelSpace ρ.ρ proIwahori,
        B x
          (aeval (heckeCoset ρ.ρ proIwahori (diagGL (mulSingle 0 ϖ)))
            (((X - C (w.q ^ k : ℂ)) * R).comp (C d * X)) y) = 0 := by
  -- Apply `chain_lemma_of_adjoint` to `T j = partialHecke ρ.ρ 1 j x`, `U = u ϖ` and `U' = u ϖ⁻¹`,
  -- where `u g` is `q ^ (N - 1)` times `ρ (diag (g, 1, …, 1))` between two means over `proIwahori`.
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, N = n + 1 := Nat.exists_eq_succ_of_ne_zero (NeZero.ne N)
  let u (g : (LocField w)ˣ) : End ℂ ρ :=
    (w.q : ℂ) ^ n •
      (compactMean ρ.ρ proIwahori * ρ.ρ (diagGL (mulSingle 0 g)) * compactMean ρ.ρ proIwahori)
  let T (j : ℕ) : ρ := partialHecke ρ.ρ 1 j x
  have avg_T (j : ℕ) : compactMean ρ.ρ proIwahori (T j) = T j :=
    compactMean_eq_self _
      (levelSpace_anti (proIwahori_le_blockParahoric fun _ _ h ↦ by omega)
        (partialHecke_mem_levelSpace hx))
  have T_zero : T 0 = x := partialHecke_zero_right hx
  have avg_x : compactMean ρ.ρ proIwahori x = x := by simpa only [T_zero] using avg_T 0
  have adj (g : (LocField w)ˣ) (y z : ρ) : B (u g⁻¹ y) z = B y (u g z) := by
    simp [u, mulSingle_inv, hB.adjoint_eq_inv, hB.compactMean_adjoint]
  -- The count of hyperplanes (row `0`, tested by the mean) is the recursion for `U`.
  have rec_U (j : ℕ) : u ϖ (T j) = (w.q : ℂ) ^ j • (t j.succ • x - T j.succ) := by
    simpa [u, T, partialHecke_zero_eq_heckeGL, ht, avg_T, avg_x] using
      partialHecke_hyperplane_count hϖ hx 0 (fun _ _ ↦ compactMean_apply) j
  -- The dual count gives the recursion for `U'`, its top degree, and `t N ≠ 0`.
  obtain ⟨dual, dual_last, dual_ne⟩ := partialHecke_hyperplane_count_dual hx hϖ
  have t_last : t n.succ ≠ 0 := by simpa [partialHecke_zero_eq_heckeGL, ht, hx_ne] using dual_ne
  replace dual_last : t n.succ • ρ.ρ (diagGL (mulSingle 0 ϖ))⁻¹ x = T n := by
    simpa [partialHecke_zero_eq_heckeGL, ht] using dual_last
  have rec_U' (i : ℕ) (hi : i < n) :
      u ϖ⁻¹ (T i.succ) = (w.q : ℂ) ^ (n - i.succ) • ((t i.succ / w.q ^ n) • u ϖ⁻¹ x - T i) := by
    simpa [u, T, mulSingle_inv, partialHecke_zero_eq_heckeGL, ht, avg_T, avg_x, smul_smul] using
      dual i (n - i.succ) (by lia)
  have U'_x : u ϖ⁻¹ x = (w.q : ℂ) ^ n • (t n.succ)⁻¹ • T n := by
    rw [← avg_T, ← dual_last]
    simp [u, mulSingle_inv, avg_x, t_last]
  have U_last : u ϖ (T n) = (w.q : ℂ) ^ n • t n.succ • x := by
    simp only [u, LinearMap.smul_apply, End.mul_apply, avg_T]
    simp [← dual_last, avg_x]
  have ht_zero : t 0 • x = x := by rw [← ht, heckeGL_zero hx]
  have linear := chain_lemma_of_adjoint (u ϖ) (u ϖ⁻¹) T hB.pos (adj ϖ) (adj ϖ⁻¹) hP_eq (by simp)
  rw [T_zero] at linear
  obtain ⟨root_bound, kills⟩ := linear hx_ne ht_zero t_last rec_U rec_U' U'_x U_last
  refine ⟨root_bound, ?_⟩
  rintro d hd k _ ⟨S, hS, F, rfl⟩ y hy
  have hP : P = (∏ i ∈ range (k + 1), (C d * X - C (w.q ^ i : ℂ))) * S.comp (C d * X) :=
    Polynomial.funext fun a ↦ by simpa [hd, eval_prod] using congrArg (eval (d * a)) hS
  -- On `proIwahori`-fixed vectors the Hecke operator `H` is `U`, so its adjoint is `U'`.
  set H : End ℂ ρ := heckeCoset ρ.ρ proIwahori (diagGL (mulSingle 0 ϖ))
  have hecke_adj (z : ρ) (hz : z ∈ levelSpace ρ.ρ proIwahori) :
      H z ∈ levelSpace ρ.ρ proIwahori ∧ ∀ a, B (u ϖ⁻¹ a) z = B a (H z) := by
    have hecke_z : H z = u ϖ z := by
      simp [H, u, (heckeCoset_mulSingle_zero_eq hϖ hz).right, hz]
    rw [hecke_z]
    exact ⟨by simp [u], fun a ↦ adj ϖ a z⟩
  -- The cofactor of the first `k` roots, conjugated and evaluated at `U'`, kills `x`.
  set G : ℂ[X] := (C d * X - C (w.q ^ k : ℂ)) * S.comp (C d * X)
  have h_root : P.IsRoot ((w.q : ℂ) ^ k / d) := by simp [hP, prod_range_succ, field]
  have h_factor : P = (∏ i ∈ range k, (C d * X - C (w.q ^ i : ℂ))) * G := by
    rw [hP, prod_range_succ, mul_assoc]
  have killed : aeval (u ϖ⁻¹) (G.map (starRingEnd ℂ)) x = 0 := kills d hd k G h_root h_factor
  have factor : ((X - C (w.q ^ k : ℂ)) * (S * F)).comp (C d * X) = F.comp (C d * X) * G := by
    simp [G]
    ring
  rw [factor, ← adjoint_aeval_map_starRingEnd _ hecke_adj _ x y hy]
  simp [killed]

/-- The top root of a chain is large. Let x ≠ 0 be a spherical Hecke eigenvector in a smooth unitary
representation of GL_N(E_w), with Hecke polynomial P. If P(c) = 0 and P(qc) ≠ 0, then
|c|² ≥ q^(N−2), written q^N / q² to avoid subtraction. -/
lemma New.Patching.le_norm_sq_of_isRoot_of_not_isRoot_mul (hB : IsUnitary ρ.ρ B)
    (hx : x ∈ levelSpace ρ.ρ (localIntGL (Fin N) w)) (hx_ne : x ≠ 0) (hP_eq : P = heckePoly w.q N t)
    (ht : ∀ j : ℕ, heckeGL ρ.ρ j x = t j • x) {c : ℂ} (hc : P.IsRoot c)
    (hqc : ¬P.IsRoot (w.q * c)) :
    (w.q : ℝ) ^ N / w.q ^ 2 ≤ ‖c‖ ^ 2 := by
  obtain ⟨h_bound, -⟩ := chain_lemma hB hx hx_ne hP_eq ht (v_uniformizer w)
  exact h_bound c hc hqc

/-- Let x ≠ 0 be a spherical Hecke eigenvector in a smooth unitary representation of GL_N(E_w), with
Hecke polynomial P. If P(c) = 0 and |c|² q^k = q^N, then c, cq, …, cq^(k−1) are all roots of P.

This also follows from Tadić's classification of the unitary spherical representations of GL_N; the
proof here is direct, from `le_norm_sq_of_isRoot_of_not_isRoot_mul` and the symmetry y ↦ q^(N−1)/ȳ
of the roots of P. -/
lemma New.Patching.isRoot_chain_of_norm (hB : IsUnitary ρ.ρ B)
    (hx : x ∈ levelSpace ρ.ρ (localIntGL (Fin N) w)) (hx_ne : x ≠ 0) (hP_eq : P = heckePoly w.q N t)
    (ht : ∀ j : ℕ, heckeGL ρ.ρ j x = t j • x) {c : ℂ} {k : ℕ} (hc : P.IsRoot c)
    (h_norm : ‖c‖ ^ 2 * w.q ^ k = w.q ^ N) {i : ℕ} (hi : i < k) :
    P.IsRoot (c * w.q ^ i) := by
  -- The roots of `P` are symmetric under `y ↦ q ^ (N - 1) / star y`, which exchanges `c * q ^ i`
  -- and `c * q ^ (k - 1 - i)`. The lower half of the chain comes from
  -- `le_norm_sq_of_isRoot_of_not_isRoot_mul` by induction.
  have hq0 : (w.q : ℂ) ≠ 0 := by simp [w.q_bounds]
  set z : ℂ := B (ρ (.scalar _ (uniformizer w)) x) x
  -- Up to the centre, the adjoint of the `d`-th Hecke operator is the `(N - d)`-th.
  have h_dual (d b : ℕ) (hN : N = d + b) : star (t d) * B x x = t b * z :=
    calc
      _ = B (heckeGL ρ.ρ d x) x := by simp [ht]
      _ =
        B x (heckeFun ρ.ρ (localIntGL (Fin N) w)
          (fun g ↦ (basicDoubleCoset (Fin N) w d).indicator 1 g⁻¹) x) := by
        simpa [Set.indicator, heckeGL] using
          ((isHeckeFunction_basicDoubleCoset d).heckeFun_adjoint B hx hB.map_map_eq hx).right
      _ = B (ρ (.scalar _ (uniformizer w)) x) (heckeGL ρ.ρ b x) := by
        rw [← heckeGL_dual hx (v_uniformizer w) (by simpa using hN), hB.map_map_eq]
      _ = t b * z := by simp [ht, z]
  -- The symmetry of the roots: compare `star (P y)` with `P y'` term by term.
  have h_reflect (y y' : ℂ) (hy : star y * y' * w.q = w.q ^ N)
      (hy' : P.IsRoot y') : P.IsRoot y := by
    have h_star_eval :
        star (P.eval y) * (B x x * w.q ^ N.choose 2) = (-star y) ^ N * z * P.eval y' := by
      simp only [hP_eq, heckePoly, eval_finsetSum, mul_sum, star_sum, sum_mul]
      -- Term `d` on the left is term `b = N - d` on the right: multiply by `q ^ d`, use `h_dual`.
      conv_rhs => rw [← sum_flip]
      refine sum_congr rfl fun d hd ↦ mul_right_cancel₀ (pow_ne_zero d hq0) ?_
      obtain ⟨b, hN⟩ : ∃ b : ℕ, N = d + b := exists_add_of_le (mem_range_succ_iff.mp hd)
      have h_exp : N.choose 2 + d.choose 2 + d = b.choose 2 + N * d := by
        qify [hN, Nat.cast_choose_two]
        ring
      simp only [show N - d = b by lia, show N - b = d by lia]
      calc
        _ = (-1) ^ d * star y ^ b * (star (t d) * B x x) * w.q ^ (N.choose 2 + d.choose 2 + d) := by
          simp
          ring
        _ = (-1) ^ d * star y ^ b * (t b * z) * (w.q ^ b.choose 2 * (star y * y' * w.q) ^ d) := by
          rw [h_dual d b hN, h_exp, hy, pow_add, pow_mul]
        _ = _ := by
          -- the signs: `(-1) ^ (d + b) * (-1) ^ b = (-1) ^ d`
          have h_sign : (-1 : ℂ) ^ b * (-1) ^ b = 1 := by simp [← mul_pow]
          rw [hN, eval_mul, eval_C, eval_pow, eval_X, neg_pow (star y)]
          linear_combination -((-1) ^ d * star y ^ (b + d) * t b * z * (w.q : ℂ) ^ b.choose 2 *
            y' ^ d * (w.q : ℂ) ^ d) * h_sign
    simpa [hy'.eq_zero, hq0, (hB.pos x hx_ne).ne'] using h_star_eval
  induction i using Nat.strongRec with | ind i ih => ?_
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, i + 1 + j = k := Nat.le.dest hi
  -- If `j < i`, then `c * q ^ j` is a root by induction, and so is its mirror image `c * q ^ i`.
  obtain hji | hij : j < i ∨ i ≤ j := lt_or_ge j i
  · refine h_reflect _ _ ?_ (ih j hji (by lia))
    have hC : (‖c‖ : ℂ) ^ 2 * w.q ^ (i + 1 + j) = w.q ^ N := mod_cast h_norm
    simp [← hC, ← Complex.conj_mul']
    ring
  -- Let `0 < i ≤ j`. If `c * q ^ i` is not a root, while `c * q ^ (i - 1)` is,
  -- `le_norm_sq_of_isRoot_of_not_isRoot_mul` bounds `‖c * q ^ (i - 1)‖ ^ 2` below by
  -- `q ^ N / q ^ 2`; with `h_norm` this says `j < i`.
  obtain _ | i := i
  · simpa using hc
  by_contra h_not
  have h_not' : ¬P.IsRoot (w.q * (c * w.q ^ i)) := by grind
  have h_prev : P.IsRoot (c * w.q ^ i) := ih i (Nat.lt_succ_self i) (by lia)
  have h_big : (w.q : ℝ) ^ N / w.q ^ 2 ≤ ‖c * w.q ^ i‖ ^ 2 :=
    le_norm_sq_of_isRoot_of_not_isRoot_mul hB hx hx_ne hP_eq ht h_prev h_not'
  -- multiply by `q ^ k`, use `h_norm`, and compare exponents
  have h_pow : (w.q : ℝ) ^ N * w.q ^ (i + 1 + 1 + j) ≤ w.q ^ N * w.q ^ (2 * i + 2) := by
    rw [div_le_iff₀ (by simp [w.q_bounds]), norm_mul, norm_pow, Complex.norm_natCast] at h_big
    grw [h_big, ← h_norm]
    exact le_of_eq (by ring)
  have hji : j < i + 1 := by
    have h_exp : i + 1 + 1 + j ≤ 2 * i + 2 := (pow_le_pow_iff_right₀ (mod_cast w.one_lt_q)).mp
      (le_of_mul_le_mul_left h_pow (by simp [pow_pos, w.q_bounds]))
    lia
  lia

/-- Of a chain of roots, U sees only the top root. Let x ≠ 0 be a spherical Hecke eigenvector in a
smooth unitary representation of GL_N(E_w), with Hecke polynomial P, and let U be the Hecke operator
of diag(ϖ, 1, …, 1) for the group `proIwahori`. If d ≠ 0 and P(X/d) = ∏_{i ≤ k} (X − q^i) · S with S
dividing R, then x is orthogonal to ((dX − q^k) · R(dX))(U) y for every y fixed by `proIwahori`. -/
lemma New.Patching.pairing_aeval_heckeCoset_eq_zero (hB : IsUnitary ρ.ρ B)
    (hx : x ∈ levelSpace ρ.ρ (localIntGL (Fin N) w)) (hx_ne : x ≠ 0) (hP_eq : P = heckePoly w.q N t)
    (ht : ∀ j : ℕ, heckeGL ρ.ρ j x = t j • x) {ϖ : (LocField w)ˣ}
    (hϖ : v ϖ.val = WithZero.exp (-1)) {d : ℂ} (hd : d ≠ 0) {k : ℕ} {R : ℂ[X]}
    (h_chain : HasRootChain P R w.q d⁻¹ (k + 1)) {y : ρ} (hy : y ∈ levelSpace ρ.ρ proIwahori) :
    B x (aeval (heckeCoset ρ.ρ proIwahori (diagGL (mulSingle 0 ϖ)))
      (((X - C (w.q ^ k : ℂ)) * R).comp (C d * X)) y) = 0 := by
  obtain ⟨-, orthogonal⟩ := chain_lemma hB hx hx_ne hP_eq ht hϖ
  exact orthogonal d hd k R h_chain y hy
