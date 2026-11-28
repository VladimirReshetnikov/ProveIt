import Lib.PadicHodge.Crystalline.HodgeTateForms

/-!
# Hodge frames and Hodge–Tate jumps under operations on representations

This file works with the period ring B_dR⁺, its uniformiser `t` and its residue map θ to ℂ_p. An
invertible matrix `U` of de Rham periods with `N g · g U = U` for `g` near 1 is brought into the
form `New.Period.hodgeMatrix W k` by an algebraic change of basis, and the columns of θ(W) are then
Hodge–Tate vectors. From this the file builds Hodge–Tate frames of potentially crystalline
representations, counts their jumps, and computes the jumps under base change, restriction of
scalars, twists, duals and submodules of products.

## Main definitions and results

* `New.Period.exists_isHodgeFrame`: an invertible `U` over B_dR with `N g · g U = U` becomes
  `hodgeMatrix W k`, with `W` invertible over B_dR⁺, after an algebraic change of basis of
  determinant 1.
* `New.Period.IsPotentiallyCrystalline.exists_isHodgeTateFrame`: there is an invertible `P` over
  `ℂ_[p]` whose columns are Hodge–Tate vectors of weights `k` (`New.Period.IsHodgeTateFrame`); the
  `k i` are the jumps, and the rows of `P⁻¹` form a basis of Hodge–Tate maps
  (`New.Period.hodgeTateMaps`).
* `New.Period.IsPotentiallyCrystalline.exists_hasJumps`: the number of jumps is the rank.
* `New.Period.jump_baseChange`, `New.Period.IsPotentiallyCrystalline.sum_jump_eq_jump_overZp`:
  extension, restriction of scalars.
* `New.Period.jump_twist_of_period`, `New.Period.jump_twist_cyclotomicGp`,
  `New.Period.hasJumps_of_cyclotomicGp_zpow`: twists shift jumps.
* `New.Period.exists_jump_of_jointly_injective`: a jump of a submodule of ∏ S_i is a jump of some
  S_i.

Notions from other files:
* `New.Period.BdRPlus`, `New.Period.BdR` (built for the prime p fixed by the instance `ThePrime p`,
  hence written without `p`): the discrete valuation ring B_dR⁺, with uniformiser `t`
  (`New.Period.tPeriod`) and residue map θ to ℂ_p (`New.Period.thetaBdR`), and its fraction field
  B_dR.
* `New.cyclotomicGp`: The p-adic cyclotomic character χ of G_p = Gal(Q̄_p over Q_p) (`New.Gp`);
  `New.Period.χ` is its composite with `toGp : Γ → G_p`, the map supplied by the class `OverGp Γ p`;
  the "open image" of `toGp` assumed in the lemmas comes with this class.
* `New.Period.nearOne`: The filter 'near 1' on Γ: the pull-back along `toGp` of the filter of
  neighbourhoods of the identity.
* `New.Period.IsPotentiallyCrystalline`: ρ is potentially crystalline: the vectors of Bmax ⊗ T (Bmax
  the crystalline period ring B_max, a ℤ_p-algebra on which G_p acts) fixed by `toGp g ⊗ ρ g` for
  `g` near 1 span Bmax ⊗ T.
* `New.Period.hodgeTateMaps`, `New.Period.jump`: the space of γ-semilinear forms f on T with f(g
  x) = χ(g)^(−u) · g f(x) for g near 1, and its dimension, the multiplicity of the jump u.
* `New.Period.overZp`: A representation of Γ on a module T over a Z_p-algebra R, regarded as a
  Z_p-linear representation.
* `New.Period.HasJumps`: The property of a multiset J of integers that for every integer u the
  multiplicity of the jump u of T at γ equals its count in J.

## Relation to the literature

Known; see `Lib.PadicHodge.Crystalline.Regularity` for sources.
-/

noncomputable section

namespace New.Period

/-!
## The Hodge frame of a Galois-invariant matrix of de Rham periods

`New.Period.BdRPlus` is the discrete valuation ring B_dR⁺ with uniformiser `t`
(`New.Period.tPeriod`; `New.Period.tUnit` as a unit of the field B_dR) and residue map
`New.Period.thetaBdR` to ℂ_p. Galois acts on `t` by the cyclotomic character.

* `New.Period.hodgeMatrix W k`: the matrix `W · diag (t ^ k i)`.

Group elements are `toGp g` with `g` along a filter `F` coarser than `New.Period.nearOne Γ`.
-/

section HodgeFrame

open Matrix nonZeroDivisors BdRPlus IsDiscreteValuationRing IsScalarTower Finset RingHom Function
  Units Filter algebraMap

variable {p : ℕ} [ThePrime p] {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Type*} [CommRing A]
  [Algebra A (PadicAlgCl p)] [Algebra A BdR] [IsScalarTower A (PadicAlgCl p) BdR]

/-- The matrix `W · diag (t ^ k i)` over `B_dR`, where `t` is the period `tUnit`. -/
noncomputable def hodgeMatrix (W : Matrix ι ι BdRPlus) (k : ι → ℤ) : Matrix ι ι BdR :=
  W.map (↑) * diagonal fun i ↦ ((tUnit ^ k i : BdRˣ) : BdR)

/-- The columns of `P` are Hodge–Tate vectors of weights `k` for the semilinear map
`v ↦ N (g • v)` of `ℂ_p ^ ι`: it multiplies the column `j` by `χ(g) ^ (-k j)`, where `χ` is the
cyclotomic character. -/
def IsHodgeTateFrame (N P : Matrix ι ι ℂ_[p]) (k : ι → ℤ) (g : Gp p) : Prop :=
  ∀ j : ι, N *ᵥ (g • P.col j) = ((cyclotomicGp g ^ (-k j) : ℤ_[p]ˣ) : ℤ_[p]) • P.col j

omit [DecidableEq ι] in
/-- In the coordinates given by a Hodge–Tate frame `P`, the map `v ↦ N (g • v)` acts on the
coordinate `j` by `x ↦ χ(g) ^ (-k j) • g • x`. -/
lemma IsHodgeTateFrame.mulVec_twist {N P : Matrix ι ι ℂ_[p]} {k : ι → ℤ} {g : Gp p}
    (h_frame : IsHodgeTateFrame N P k g) (w : ι → ℂ_[p]) :
    P *ᵥ (fun j : ι ↦ ((cyclotomicGp g ^ (-k j) : ℤ_[p]ˣ) : ℤ_[p]) • g • w j) =
      N *ᵥ (g • (P *ᵥ w)) := by
  funext i
  have h_entry (j : ι) : ((cyclotomicGp g ^ (-k j) : ℤ_[p]ˣ) : ℤ_[p]) • P i j =
      ∑ m, N i m * g • P m j := (congrFun (h_frame j) i).symm
  calc (P *ᵥ fun j ↦ ((cyclotomicGp g ^ (-k j) : ℤ_[p]ˣ) : ℤ_[p]) • g • w j) i
      = ∑ j, (((cyclotomicGp g ^ (-k j) : ℤ_[p]ˣ) : ℤ_[p]) • P i j) * g • w j := by
        simp only [mulVec, dotProduct, mul_smul_comm, smul_mul_assoc]
    _ = ∑ j, ∑ m, N i m * g • P m j * g • w j := by simp only [h_entry, sum_mul]
    _ = ∑ m, ∑ j, N i m * g • P m j * g • w j := sum_comm
    _ = (N *ᵥ (g • (P *ᵥ w))) i := by simp [mulVec, dotProduct, smul_sum, mul_sum, mul_assoc]

/-- `Y`, `W`, `k` form a Hodge frame for the matrix `U` over `B_dR` and the family `N` along the
filter `F` on `Γ`: the algebraic, integral, fixed change of basis `Y` turns `U` into the invariant
matrix `W · diag (t ^ k i)` with `W` invertible over `B_dR⁺`. -/
structure IsHodgeFrame {Γ : Type*} [Group Γ] [OverGp Γ p] (F : Filter Γ) (N : Γ → Matrix ι ι A)
    (U : Matrix ι ι BdR) (Y : SpecialLinearGroup ι (PadicAlgCl p)) (W : Matrix ι ι BdRPlus)
    (k : ι → ℤ) : Prop where
  /-- The matrix `W` is invertible over `B_dR⁺`. -/
  isUnit : IsUnit W
  /-- The entries of `Y` are fixed by `g`, eventually along `F`. -/
  eventually_map_eq : ∀ᶠ g : Γ in F, (Y : Matrix ι ι (PadicAlgCl p)).map (toGp g) = Y
  /-- The product `U Y` is `W · diag (t ^ k i)`. -/
  mul_map_eq : U * (Y : Matrix ι ι (PadicAlgCl p)).map (↑) = hodgeMatrix W k
  /-- The matrix `W · diag (t ^ k i)` is fixed by `M ↦ N g * g • M`, eventually along `F`. -/
  eventually_mul_smul_eq :
    ∀ᶠ g : Γ in F, (N g).map (↑) * toGp g • hodgeMatrix W k = hodgeMatrix W k
  /-- The entries of `Y` are integral. -/
  norm_le_one : ∀ i l : ι, ‖Y i l‖ ≤ 1

/-- If `W · diag (t ^ k i)` is fixed by `M ↦ N * g • M`, then `θ(W)` is a Hodge–Tate frame of
weights `k` at `g` for `N`, whose entries are read in `ℂ_[p]`. -/
lemma isHodgeTateFrame_of_hodgeMatrix {W : Matrix ι ι BdRPlus} {k : ι → ℤ} {N : Matrix ι ι A}
    {g : Gp p} (h_inv : N.map (↑) * g • hodgeMatrix W k = hodgeMatrix W k) :
    IsHodgeTateFrame (N.map fun a : A ↦ ((a : PadicAlgCl p) : ℂ_[p])) (W.map thetaBdR) k g := by
  intro l
  funext i
  -- Cancel `t ^ k l` in the entry `(i, l)` of `h_inv`, using `g • t ^ k l = χ(g) ^ k l • t ^ k l`.
  have h_entry : (∑ m, (N i m : PadicAlgCl p) • g • W m l) *
      algebraMap ℤ_[p] BdRPlus ((cyclotomicGp g ^ k l : ℤ_[p]ˣ) : ℤ_[p]) = W i l := by
    apply IsFractionRing.injective BdRPlus BdR
    -- Without `-val_zpow_eq_zpow_val`, `simp` splits `↑(tUnit ^ k l)` before `smul_tUnit_zpow`.
    simpa [smul_tUnit_zpow, ← mul_assoc, ← IsScalarTower.algebraMap_apply, ← sum_mul,
      -val_zpow_eq_zpow_val, Algebra.smul_def, hodgeMatrix, diagonal, Matrix.mul_apply] using
      congrFun₂ h_inv i l
  -- Apply `θ` and move the power of `χ(g)` to the other side.
  have h_theta : cyclotomicGp g ^ k l • ∑ m, ((N i m : PadicAlgCl p) : ℂ_[p]) *
      g • thetaBdR (W m l) = thetaBdR (W i l) := by
    simp [← h_entry, Units.smul_def, mul_comm, mul_left_comm, PadicComplex.coe_eq, Algebra.cast,
      smul_sum, Algebra.smul_def, sum_mul]
  rw [_root_.zpow_neg]
  exact eq_inv_smul_iff.2 h_theta

/-- Every matrix `U` over `B_dR` is `W · diag (t ^ k i)` for a matrix `W` over `B_dR⁺`: write a
common denominator of the entries of `U` as `u * t ^ d` with `u` a unit, and take `k i = -d`. -/
lemma exists_eq_hodgeMatrix (U : Matrix ι ι BdR) :
    ∃ (W : Matrix ι ι BdRPlus) (k : ι → ℤ), U = hodgeMatrix W k := by
  obtain ⟨b, h_int⟩ : ∃ b : BdRPlus⁰, ∀ il : ι × ι,
      IsLocalization.IsInteger BdRPlus ((b : BdRPlus) • U.uncurry il) :=
    IsLocalization.exist_integer_multiples_of_finite BdRPlus⁰ U.uncurry
  choose W₀ hW₀ using h_int
  obtain ⟨d, u, hu⟩ : ∃ (d : ℕ) (u : BdRPlusˣ), (b : BdRPlus) = u * tPeriod ^ d :=
    eq_unit_mul_pow_irreducible (coe_ne_zero b) prime_tPeriod.irreducible
  refine ⟨of fun i l ↦ (u⁻¹ : BdRPlusˣ) * W₀ (i, l), fun _ : ι ↦ -(d : ℤ), ?_⟩
  have ht : algebraMap BdRPlus BdR tPeriod ≠ 0 := by simpa using prime_tPeriod.ne_zero
  simp [← ext_iff, hW₀, hu, tUnit, uncurry, field, hodgeMatrix, diagonal, Matrix.mul_apply,
    Algebra.smul_def]

/-- Cramer's rule for one column: if `W *ᵥ a = c • V` and `a i = 1`, then `det W = c * det W'`,
where `W'` is `W` with the column `i` replaced by `V`. -/
lemma _root_.Matrix.det_eq_mul_det_updateCol_of_mulVec_eq_smul_of_apply_eq_one {n R : Type*}
    [Fintype n] [DecidableEq n] [CommRing R] {W : Matrix n n R} {a V : n → R} {c : R} {i : n}
    (h_mulVec : W *ᵥ a = c • V) (h_one : a i = 1) :
    W.det = c * (W.updateCol i V).det := by
  have h_cramer : cramer W (W *ᵥ a) = W.det • a := by
    rw [cramer_eq_adjugate_mulVec, mulVec_mulVec, adjugate_mul, smul_mulVec, one_mulVec]
  calc W.det = cramer W (W *ᵥ a) i := by
        rw [h_cramer, Pi.smul_apply, h_one, _root_.smul_eq_mul, mul_one]
    _ = c * (W.updateCol i V).det := by
      rw [h_mulVec, map_smul, Pi.smul_apply, cramer_apply, _root_.smul_eq_mul]

/-- The column step of the Hodge frame: let `a` be supported where the weight is `k i`, with
`W a = t V`. Then replacing the column `i` of the identity by `a` turns `W · diag (t ^ k)` into
`W' · diag (t ^ k')`, where `W'` is `W` with the column `i` replaced by `V` and `k'` is `k`
with `k i` raised by one. -/
lemma hodgeMatrix_mul_map_updateCol {W : Matrix ι ι BdRPlus} {k : ι → ℤ} {i : ι}
    {a : ι → PadicAlgCl p} {V : ι → BdRPlus} (h_supp : ∀ x : ι, k x = k i ∨ a x = 0)
    (hV : ∀ m : ι, (W *ᵥ (↑) ∘ a) m = tPeriod * V m) :
    hodgeMatrix W k * (updateCol 1 i a).map (↑) =
      hodgeMatrix (W.updateCol i V) (k + Pi.single i 1) := by
  ext m l
  by_cases hl : l = i
  · -- `a` is supported where `k x = k i`, so `t ^ k i` factors out of the sum.
    calc (hodgeMatrix W k * (updateCol 1 i a).map ((↑) : PadicAlgCl p → BdR)) m l
        = ∑ x, (W m x : BdR) * ((tUnit ^ k x : BdRˣ) : BdR) * a x := by
          simp [hl, hodgeMatrix, diagonal, Matrix.mul_apply]
      _ = ∑ x, ((tUnit ^ k i : BdRˣ) : BdR) * (W m x * a x) := by
          refine sum_congr rfl fun x _ ↦ ?_
          obtain h_weight | h_zero := h_supp x
          · rw [h_weight, mul_comm (W m x : BdR), mul_assoc]
          · simp [h_zero]
      _ = ((tUnit ^ k i : BdRˣ) : BdR) * ((tPeriod * V m : BdRPlus) : BdR) := by
          simp [← hV, ← IsScalarTower.algebraMap_apply, mulVec, dotProduct, mul_sum]
      _ = hodgeMatrix (W.updateCol i V) (k + Pi.single i 1) m l := by
          simp [hl, tUnit, zpow_add_one₀, prime_tPeriod.ne_zero, field, hodgeMatrix, diagonal,
            Matrix.mul_apply]
  · simp [hl, one_apply, hodgeMatrix, diagonal, Matrix.mul_apply]

/-- Let `Γ` map to `Gp p` by `j` with open image, let `F` be a filter on `Γ` with `nearOne Γ ≤ F`
(`nearOne Γ` is the pull-back along `j` of the neighbourhoods of `1`), and let `N g` be matrices
over a ring `A` that maps compatibly to ℚ̄_p and `B_dR`. An invertible matrix `U` over `B_dR` with
`N g * j(g) • U = U` for `F`-almost all `g` (with `j(g)` acting entrywise) has a Hodge frame
`IsHodgeFrame F N U Y W k`: a change of basis `Y` of determinant one over ℚ̄_p, integral and fixed
as `IsHodgeFrame` requires, turns `U` into `W · diag (t ^ k i)` with `W` invertible over `B_dR⁺` and
`k : ι → ℤ`.

A variant of the existence of bases of B_dR^+⊗T adapted to the Hodge filtration, for de Rham T. -/
lemma exists_isHodgeFrame (Γ : Type*) [Group Γ] [OverGp Γ p] {F : Filter Γ} (hF : nearOne Γ ≤ F)
    {U : Matrix ι ι BdR} {N : Γ → Matrix ι ι A} (hU : IsUnit U)
    (hU_inv : ∀ᶠ g : Γ in F, (N g).map ((↑) : A → BdR) * U.map (fun x : BdR ↦ toGp g • x) = U) :
    ∃ (Y : SpecialLinearGroup ι (PadicAlgCl p)) (W : Matrix ι ι BdRPlus) (k : ι → ℤ),
      IsHodgeFrame F N U Y W k := by
  -- Among all factorisations `U * Y = hodgeMatrix W k` with `Y` fixed, integral and of determinant
  -- `1`, take one with `det W` minimal for divisibility. If `θ(W)` were singular, its kernel would
  -- contain a fixed vector, and a column operation would divide `det W` by `t`.
  let S : Set (Matrix ι ι BdRPlus) :=
    {W | ∃ (Y : SpecialLinearGroup ι (PadicAlgCl p)) (k : ι → ℤ),
      (Y : Matrix ι ι (PadicAlgCl p)) ∈ (intQpBar p).matrix ∧
      (∀ᶠ g : Γ in F, (Y : Matrix ι ι (PadicAlgCl p)).map (toGp g) = Y) ∧
      U * (Y : Matrix ι ι (PadicAlgCl p)).map (↑) = hodgeMatrix W k}
  -- There is one with `Y = 1`.
  have h_ne : S.Nonempty := by
    obtain ⟨W₀, k₀, hU_eq⟩ := exists_eq_hodgeMatrix U
    exact ⟨W₀, 1, k₀, by simp, by simp, by simp [hU_eq]⟩
  obtain ⟨W, ⟨Y, k, Y_int, Y_fix, hUY⟩, h_min⟩ :
      ∃ W ∈ S, ∀ W' ∈ S, ¬DvdNotUnit W'.det W.det :=
    (InvImage.wf det wellFounded_dvdNotUnit).has_min S h_ne
  have h_inv : ∀ᶠ g : Γ in F, (N g).map (↑) * toGp g • hodgeMatrix W k = hodgeMatrix W k := by
    rw [← hUY]
    filter_upwards [hU_inv, Y_fix] with g hg hY
    -- `g` acts entrywise, and fixes the entries of `Y`.
    have h_smul : toGp g • (U * (Y : Matrix ι ι (PadicAlgCl p)).map ((↑) : PadicAlgCl p → BdR)) =
        U.map (fun x : BdR ↦ toGp g • x) *
          ((Y : Matrix ι ι (PadicAlgCl p)).map (toGp g)).map ((↑) : PadicAlgCl p → BdR) := by
      simp [← ext_iff, Matrix.mul_apply, smul_sum]
    rw [h_smul, hY, ← mul_assoc, hg]
  have det_ne : W.det ≠ 0 := by
    intro h_zero
    apply (hU.map detMonoidHom).ne_zero
    simpa [← map_det, ← mapMatrix_apply, h_zero, hodgeMatrix] using congrArg det hUY
  refine ⟨Y, W, k, ?_, Y_fix, hUY, h_inv, Y_int⟩
  -- `W` is a unit iff `θ(det W) ≠ 0`, that is, iff `θ(W)` has zero kernel.
  suffices h_ker : LinearMap.ker (toLin' (W.map thetaBdR)) ≤ ⊥ by
    have h_det : LinearMap.det (toLin' (W.map thetaBdR)) ≠ 0 :=
      fun h_zero ↦ (LinearMap.bot_lt_ker_of_det_eq_zero h_zero).not_ge h_ker
    rw [LinearMap.det_toLin'] at h_det
    rw [isUnit_iff_isUnit_det, BdRPlus.isUnit_iff, AlgHom.map_det]
    exact h_det
  -- The kernel is stable under the twisted action (`isHodgeTateFrame_of_hodgeMatrix`), so by
  -- `le_of_hodgeTate_stable` it is zero unless it contains an algebraic, integral, fixed vector
  -- `a` with `a i = 1` for some `i` and supported where the weight is `k i`.
  have hF_nhds : nhds 1 ≤ map toGp F := (nhds_one_le_map_nearOne Γ).trans (map_mono hF)
  refine le_of_hodgeTate_stable hF_nhds (fun i : ι ↦ -k i) (LinearMap.ker (toLin' (W.map thetaBdR)))
    ⊥ (fun v (hv : W.map thetaBdR *ᵥ v = 0) ↦ ?_) ?_
  · refine h_inv.mono fun g hg ↦ ((isHodgeTateFrame_of_hodgeMatrix hg).mulVec_twist v).trans ?_
    rw [hv, smul_zero, mulVec_zero]
  intro a i a_ker (a_int : ∀ x : ι, a x ∈ intQpBar p) a_supp a_one a_fix
  -- `θ(W a) = 0` means `W a = t V` (`ker θ` is generated by `xi`, an associate of `t`); Cramer's
  -- rule gives `det W = t * det W'`, where `W'` is `W` with the column `i` replaced by `V`.
  have h_t_dvd (m : ι) : ∃ x : BdRPlus, (W *ᵥ (↑) ∘ a) m = tPeriod * x :=
    associated_xi_tPeriod.dvd'.trans <| thetaBdR_eq_zero_iff.1 <| by
      simpa [mulVec, dotProduct, toLin'_apply] using congrFun (LinearMap.mem_ker.1 a_ker) m
  choose V hV using h_t_dvd
  have h_mulVec : W *ᵥ ((↑) ∘ a) = tPeriod • V := funext hV
  have h_det : W.det = tPeriod * (W.updateCol i V).det :=
    det_eq_mul_det_updateCol_of_mulVec_eq_smul_of_apply_eq_one h_mulVec (i := i) (by simp [a_one])
  -- `W'` occurs in a factorisation: replace the column `i` of `Y` by `Y a` and `k i` by `k i + 1`.
  have h_supp (x : ι) : k x = k i ∨ a x = 0 := (a_supp x).imp_left fun h_neg ↦ neg_injective h_neg
  have h_mem : W.updateCol i V ∈ S := by
    refine ⟨⟨Y * updateCol 1 i a, by simp [← cramer_apply, a_one]⟩, k + Pi.single i 1,
      mul_mem Y_int fun x ↦ ?_, ?_, ?_⟩
    · simp [updateCol_apply, one_apply, ite_mem, a_int]
    · filter_upwards [Y_fix, eventually_all.2 a_fix] with g hY (ha : ∀ l : ι, toGp g (a l) = a l)
      simp [Matrix.map_mul, map_updateCol, hY, ha, comp_def]
    · rw [Matrix.map_mul, ← mul_assoc, hUY]
      exact hodgeMatrix_mul_map_updateCol h_supp hV
  -- This contradicts the minimality of `det W`.
  have h_dvd : DvdNotUnit (W.updateCol i V).det W.det :=
    ⟨right_ne_zero_of_mul (h_det.symm.trans_ne det_ne), tPeriod, prime_tPeriod.not_isUnit,
      h_det.trans (mul_comm _ _)⟩
  exact absurd h_dvd (h_min _ h_mem)

end HodgeFrame

/-!
## Hodge–Tate frames and jumps of potentially crystalline modules

For `ρ` potentially crystalline (`New.Period.IsPotentiallyCrystalline`) on a free `R`-module with
basis `e`, with `R` algebraic over `ℤ_[p]` and `toGp` of open image, the Hodge–Tate decomposition is
written in matrices.

The frame is the image under θ (`New.Period.thetaBdR`) of a basis adapted to the Hodge filtration
(`New.Period.exists_isHodgeFrame`).
-/

section HodgeTateFrame

open Filter Finset Matrix Module Submodule LinearMap

variable {p : ℕ} [ThePrime p]
  {Γ R T : Type*} [Group Γ] [CommRing R] [AddCommGroup T] [Module R T] [Algebra ℤ_[p] R]
  [Algebra.IsAlgebraic ℤ_[p] R] [OverGp Γ p] {ρ : Representation R Γ T}
  {ι : Type*} [Fintype ι] [DecidableEq ι] (e : Basis ι R T)

/-- The rows of the inverse of an invertible Hodge–Tate frame `P` satisfy
`P⁻¹ N = diag (χ(g) ^ (-k i)) · g(P⁻¹)`. -/
lemma inv_mul_apply_of_isHodgeTateFrame {N : Matrix ι ι ℂ_[p]} {k : ι → ℤ} {g : Gp p}
    {P : GL ι ℂ_[p]} (h_frame : IsHodgeTateFrame N P k g) (i l : ι) :
    ((P⁻¹ : GL ι ℂ_[p]) * N : Matrix ι ι ℂ_[p]) i l =
      ((cyclotomicGp g ^ (-k i) : ℤ_[p]ˣ) : ℤ_[p]) • g • P⁻¹ i l := by
  -- Apply `mulVec_twist` to the column `l` of `P⁻¹` and multiply by `P⁻¹`.
  set Pinv : Matrix ι ι ℂ_[p] := ((P⁻¹ : GL ι ℂ_[p]) : Matrix ι ι ℂ_[p]) with hPinv
  have h_entry : (Pinv *ᵥ (P *ᵥ fun j : ι ↦
      ((cyclotomicGp g ^ (-k j) : ℤ_[p]ˣ) : ℤ_[p]) • g • (Pinv *ᵥ col 1 l) j)) i =
      (Pinv *ᵥ (N *ᵥ (g • (P *ᵥ (Pinv *ᵥ col 1 l))))) i := by rw [h_frame.mulVec_twist]
  -- Cancel `P⁻¹ P` on the left and `P P⁻¹` on the right.
  simp only [mulVec_mulVec, hPinv, Units.inv_mul, Units.mul_inv, one_mulVec] at h_entry
  simpa [hPinv, one_apply, mulVec_apply_eq_sum] using h_entry.symm

/-- Let `R` be algebraic over `ℤ_[p]` and `e` a finite basis of `T`. Let `Q` be invertible over
`ℂ_[p]` with `Q · γ(ρ g) = diag (χ(g) ^ (-k i)) · g(Q)` for `g` near `1`, where `ρ g` is written
as a matrix in the basis `e`. Then the `k i` are the jumps of `ρ` at `γ`, and the `γ`-semilinear
forms whose values on `e` are the rows of `Q` form a basis, the `i`-th in
`New.Period.hodgeTateMaps` for the weight `k i`. -/
lemma hasJumps_of_rows {γ : R →ₐ[ℤ_[p]] ℂ_[p]} (Q : GL ι ℂ_[p]) (k : ι → ℤ)
    (h_rows : ∀ᶠ g : Γ in nearOne Γ, ∀ i l : ι,
      ((Q : Matrix ι ι ℂ_[p]) * ((ρ g).toMatrix e e).map γ) i l =
        ((χ g ^ (-k i) : ℤ_[p]ˣ) : ℤ_[p]) • toGp g • Q i l) :
    HasJumps ρ γ (univ.val.map k) ∧
    ∃ b : Basis ι ℂ_[p] (T →ₛₗ[(γ : R →+* ℂ_[p])] ℂ_[p]),
      (∀ i : ι, b i ∈ hodgeTateMaps ρ γ (k i)) ∧ ∀ i l : ι, b i (e l) = Q i l := by
  classical
  -- `b i` is the semilinear form whose values on the basis `e` are the `i`-th row of `Q`.
  let b : Basis ι ℂ_[p] (T →ₛₗ[(γ : R →+* ℂ_[p])] ℂ_[p]) :=
    (basisOfPiSpaceOfLinearIndependent (linearIndependent_row_iff_isUnit.2 Q.isUnit)).map
      (evalOnBasis (γ := γ) e).symm
  have h_val (i l : ι) : b i (e l) = Q i l := by
    change evalOnBasis e (b i) l = Q i l
    simp [b]
  -- The Hodge–Tate condition may be checked on `e`, where it is the hypothesis `h_rows`.
  have h_mem (i : ι) : b i ∈ hodgeTateMaps ρ γ (k i) := by
    refine mem_hodgeTateMaps_of_span e.span_eq fun l ↦ h_rows.mono fun g hg ↦ ?_
    have h_expand : ρ g (e l) = ∑ j : ι, (ρ g).toMatrix e e j l • e j := by
      simp only [LinearMap.toMatrix_apply, e.sum_repr]
    rw [h_expand]
    simpa [h_val, mul_apply, mul_comm] using hg i l
  exact ⟨hasJumps_of_basis (F := .of_basis e) h_mem, b, h_mem, h_val⟩

variable [Module ℤ_[p] T] [IsScalarTower ℤ_[p] R T]

omit [Algebra.IsAlgebraic ℤ_[p] R] in
/-- Let `ρ` be potentially crystalline and `δ : R → ℚ̄_p` a `ℤ_[p]`-algebra map. Then the vectors
`v : ι → B_dR` with `δ(ρ g) · (toGp g • v) = v` for `g` near `1` span `B_dR ^ ι`; here `ρ g` is
written as a matrix in the basis `e`. This is the implication 'potentially crystalline ⇒
potentially de Rham', in coordinates. -/
lemma IsPotentiallyCrystalline.top_le_span_fixed (h : IsPotentiallyCrystalline ρ)
    (δ : R →ₐ[ℤ_[p]] PadicAlgCl p) :
    ⊤ ≤ span BdR {v : ι → BdR | ∀ᶠ g : Γ in nearOne Γ,
      (((ρ g).toMatrix e e).map δ).map (algebraMap (PadicAlgCl p) BdR) *ᵥ toGp g • v = v} := by
  -- Let `L : Bmax ⊗ T → (ι → BdR)` send `b ⊗ x` to `b` times the coordinates of `x`, read in
  -- `BdR` through `δ`. It is equivariant near `1`, so it maps the fixed vectors, which span
  -- `Bmax ⊗ T` by `h`, to fixed vectors; and its image contains the standard basis.
  let coords : T →ₗ[ℤ_[p]] ι → BdR :=
    ((IsScalarTower.toAlgHom ℤ_[p] (PadicAlgCl p) BdR).comp δ).toLinearMap.compLeft ι ∘ₗ
      e.equivFun.toLinearMap
  let L : TensorProduct ℤ_[p] Bmax T →ₗ[Bmax] ι → BdR := liftBaseChange Bmax coords
  have h_equivariant (y : TensorProduct ℤ_[p] Bmax T) : ∀ᶠ g : Γ in nearOne Γ,
      (((ρ g).toMatrix e e).map δ).map (algebraMap (PadicAlgCl p) BdR) *ᵥ toGp g • L y =
        L (tensorAction Bmax (toGp g) (ρ g) y) := by
    induction y using TensorProduct.inductionOn with
    | tmul b x =>
      -- Near `1`, `toGp g` fixes the finitely many coordinates `δ (e.repr x i)`.
      filter_upwards [eventually_all.2 fun i ↦ eventually_nearOne_apply_eq Γ (δ (e.repr x i))]
        with g hg
      -- Written out in coordinates, the two sides are sums with equal terms.
      simp [L, coords, funext_iff, tensorAction, ← toMatrix_mulVec_repr e, mulVec_eq_sum,
        Algebra.smul_def, mul_sum, hg, Algebra.cast, mul_assoc, mul_comm, mul_left_comm]
    | add y z hy hz =>
      filter_upwards [hy, hz] with g hgy hgz
      simp only [map_add, smul_add, mulVec_add, hgy, hgz]
  have h_basis (i : ι) : L (1 ⊗ₜ e i) = Pi.basisFun BdR ι i := by
    simp [L, coords, funext_iff, Finsupp.single_apply, Pi.single_apply, eq_comm]
  refine ((eq_top_iff_forall_basis_mem (Pi.basisFun BdR ι)).2 fun i ↦ ?_).ge
  have h_mem : L (1 ⊗ₜ e i) ∈ (span Bmax (fixedPeriods ρ Bmax (nearOne Γ))).map L :=
    mem_map_of_mem (h.ge mem_top)
  rw [← h_basis, ← restrictScalars_mem Bmax]
  -- It suffices that `L` maps each fixed vector `y` to a fixed vector.
  refine (L.map_span_le _ _).2 (fun y hy ↦ subset_span (R := BdR) ?_) h_mem
  have hy_fix : ∀ᶠ g : Γ in nearOne Γ, tensorAction Bmax (toGp g) (ρ g) y = y := hy
  filter_upwards [h_equivariant y, hy_fix] with g hg hfix
  rw [hg, hfix]

/-- For `toGp` with open image and `R` algebraic over ℤ_p, the Hodge–Tate frame of a potentially
crystalline `ρ` along `γ`: an invertible matrix `P` over `ℂ_[p]` and integers `k i` such that (a)
near `1` the columns of `P` are Hodge–Tate vectors of weights `k` for the matrix of `ρ g` in the
basis `e`; (b) the `k i` are the jumps of `ρ` at `γ`; (c) the semilinear maps whose values on `e`
are the rows of `P⁻¹` form a basis, the `i`-th of weight `k i`. -/
lemma IsPotentiallyCrystalline.exists_isHodgeTateFrame (h : IsPotentiallyCrystalline ρ)
    (γ : R →ₐ[ℤ_[p]] ℂ_[p]) :
    ∃ P : GL ι ℂ_[p], ∃ k : ι → ℤ,
      -- (a)
      (∀ᶠ g : Γ in nearOne Γ,
        IsHodgeTateFrame (((ρ g).toMatrix e e).map γ) (P : Matrix ι ι ℂ_[p]) k (toGp g)) ∧
      -- (b)
      HasJumps ρ γ (univ.val.map k) ∧
      -- (c)
      ∃ b : Basis ι ℂ_[p] (T →ₛₗ[(γ : R →+* ℂ_[p])] ℂ_[p]),
        (∀ i : ι, b i ∈ hodgeTateMaps ρ γ (k i)) ∧ ∀ i l : ι, b i (e l) = P⁻¹ i l := by
  -- Lift `γ` to `δ` with algebraic values, and take a basis `U` of invariant vectors over `BdR`.
  obtain ⟨δ, hδ⟩ : ∃ δ : R →ₐ[ℤ_[p]] PadicAlgCl p, ∀ r, γ r = δ r := exists_algHom_lift γ
  obtain ⟨U, hU⟩ : ∃ U : GL ι BdR, ∀ i : ι, ∀ᶠ g : Γ in nearOne Γ,
      (((ρ g).toMatrix e e).map δ).map (algebraMap (PadicAlgCl p) BdR) *ᵥ
        toGp g • (U : Matrix ι ι BdR).col i = (U : Matrix ι ι BdR).col i :=
    exists_GL_col_mem_of_span _ (h.top_le_span_fixed e δ)
  -- The Hodge frame `hodgeMatrix W k` is still invariant, with `W` invertible over `BdRPlus`.
  obtain ⟨Y, W, k, h_hodge⟩ : ∃ (Y : SpecialLinearGroup ι (PadicAlgCl p))
      (W : Matrix ι ι BdRPlus) (k : ι → ℤ),
      IsHodgeFrame (nearOne Γ) (fun g : Γ ↦ ((ρ g).toMatrix e e).map δ) (U : Matrix ι ι BdR)
        Y W k :=
    exists_isHodgeFrame Γ le_rfl U.isUnit ((eventually_all.2 hU).mono fun _ ↦ ext_col)
  -- The image of `W` under `thetaBdR` is the required matrix.
  let P : GL ι ℂ_[p] := .map thetaBdR h_hodge.isUnit.unit
  have h_frame : ∀ᶠ g : Γ in nearOne Γ,
      IsHodgeTateFrame (((ρ g).toMatrix e e).map γ) (P : Matrix ι ι ℂ_[p]) k (toGp g) := by
    rw [funext hδ]
    exact h_hodge.eventually_mul_smul_eq.mono fun _ ↦ isHodgeTateFrame_of_hodgeMatrix
  exact ⟨P, k, h_frame, hasJumps_of_rows e P⁻¹ k
    (h_frame.mono fun _ ↦ inv_mul_apply_of_isHodgeTateFrame)⟩

/-- Let `toGp` have open image, R be algebraic over Z_p, and T be finite free over R and potentially
crystalline. Then at each γ: R → C_p the jumps of T, with multiplicity, form a multiset of
cardinality the rank of T.

This is the equality between the number of Hodge–Tate weights of a potentially crystalline
representation and its rank (Brinon–Conrad), for R algebraic over Z_p, with weights counted as jumps
at each embedding γ: R → C_p of the coefficients. -/
lemma IsPotentiallyCrystalline.exists_hasJumps (h : IsPotentiallyCrystalline ρ) [Free R T]
    [Module.Finite R T] (γ : R →ₐ[ℤ_[p]] ℂ_[p]) :
    ∃ J : Multiset ℤ, J.card = finrank R T ∧ HasJumps ρ γ J := by
  have : Nontrivial R := γ.domain_nontrivial
  -- The weights `k` of a Hodge–Tate frame in a basis of `T` are the jumps; there are `finrank R T`.
  obtain ⟨-, k, -, h_jumps, -⟩ := h.exists_isHodgeTateFrame (finBasis R T) γ
  exact ⟨univ.val.map k, by simp, h_jumps⟩

end HodgeTateFrame

/-!
## Hodge–Tate jumps under operations on representations

Here Γ maps to G_p by `toGp`, with open image, and acts on an R-module T; γ : R → ℂ_p is a
ℤ_p-algebra map. `New.Period.hodgeTateMaps ρ γ u` is the Q̄_p-space of γ-semilinear forms f on T
with f(g x) = χ(g)^(−u) · g f(x) for g near 1 (`New.Period.nearOne`), and `New.Period.jump ρ γ u`,
its dimension, is the multiplicity of the jump u; so χ^c has the jump −c.

* `New.Period.jump_baseChange`, `New.Period.jump_twist_of_period`: extension of scalars, twists.
* `New.Period.exists_jump_bound`: the jumps at γ are bounded.
* `New.Period.jump_eq_of_pairing`: duals.
-/

section Jumps

open LinearEquiv Filter Module Submodule LinearMap Finset hodgeTateMaps Algebra
  RingHomClass Fintype Finite IsAlgebraic Matrix

section

variable {p : ℕ} [ThePrime p]
  {Γ R T T' R' ι κ : Type*} [Group Γ] [CommRing R] [AddCommGroup T] [Module R T] [Algebra ℤ_[p] R]
  [AddCommGroup T'] [OverGp Γ p]
  {ρ ρ' : Representation R Γ T} [CommRing R'] [Module R' T'] [Algebra ℤ_[p] R']
  {σ : Representation R' Γ T'} {γ' : R' →ₐ[ℤ_[p]] ℂ_[p]} {φ : R' →+* R} {u : ℤ}
  {γ : R →ₐ[ℤ_[p]] ℂ_[p]}

/-! ### Pull-back of forms, base change and twists -/

/-- For a φ-semilinear map i: T' → T equivariant near 1, the Q̄_p-linear map f ↦ f∘i between the
spaces `New.Period.hodgeTateMaps` for u, of T at γ and T' at γ' = γ∘φ. -/
def hodgeTateMaps.pull [RingHomCompTriple φ (toRingHom γ) γ'] (i : T' →ₛₗ[φ] T)
    (hi : ∀ᶠ g : Γ in nearOne Γ, ∀ x : T', i (σ g x) = ρ g (i x)) :
    hodgeTateMaps ρ γ u →ₗ[PadicAlgCl p] hodgeTateMaps σ γ' u where
  toFun f :=
    ⟨f.val ∘ₛₗ i, fun x ↦ by
      filter_upwards [hi, f.property (i x)] with g h_equiv h_weight
      simpa [h_equiv] using h_weight⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Extension of scalars. Let R' be algebraic over Z_p, and let f: T → T' be semilinear along φ:
R → R', map a basis to a basis, and be equivariant near 1. Then the jump u has the same multiplicity
for T' at γ' as for T at γ'∘φ; T need not be potentially crystalline. This is the invariance of
Hodge–Tate weights under extension of coefficients. -/
lemma jump_baseChange {φ : R →ₐ[ℤ_[p]] R'} (f : T →ₛₗ[toRingHom φ] T') (b : Basis ι R T)
    (b' : Basis ι R' T') (hb : ∀ i : ι, f (b i) = b' i)
    (hf : ∀ᶠ g : Γ in nearOne Γ, ∀ x : T, f (ρ g x) = σ g (f x)) [Algebra.IsAlgebraic ℤ_[p] R'] :
    jump σ γ' u = jump ρ (γ'.comp φ) u := by
  -- Composition with `f` identifies the semilinear maps on `T'` and on `T`, as both are determined
  -- freely by their values on the bases; it respects the weight in both directions.
  have : RingHomCompTriple (toRingHom φ) (toRingHom γ') (toRingHom (γ'.comp φ)) :=
    ⟨(γ'.comp_toRingHom φ).symm⟩
  -- The values of `F.comp f` on `b` are the values of `F` on `b'`.
  have h_eval_comp : (fun F : T' →ₛₗ[toRingHom γ'] ℂ_[p] ↦
      evalOnBasis b (F.comp f : T →ₛₗ[toRingHom (γ'.comp φ)] ℂ_[p])) = evalOnBasis b' :=
    funext fun F ↦ funext fun i ↦ congrArg F (hb i)
  have h_bij : Function.Bijective fun F : T' →ₛₗ[toRingHom γ'] ℂ_[p] ↦
      (F.comp f : T →ₛₗ[toRingHom (γ'.comp φ)] ℂ_[p]) :=
    .of_comp_left (by rw [Function.comp_def, h_eval_comp]; exact (evalOnBasis b').bijective)
      (evalOnBasis b).injective
  have h_iff (F : T' →ₛₗ[toRingHom γ'] ℂ_[p]) :
      F ∈ hodgeTateMaps σ γ' u ↔ F.comp f ∈ hodgeTateMaps ρ (γ'.comp φ) u := by
    refine ⟨fun hF ↦ (pull f hf ⟨F, hF⟩).property, fun hF ↦ ?_⟩
    -- The condition at `b' i = f (b i)` is the condition for `F.comp f` at `b i`.
    refine mem_hodgeTateMaps_of_span b'.span_eq fun i ↦ ?_
    filter_upwards [hf, hF (b i)] with g h_equiv hg
    simpa [h_equiv, hb] using hg
  let e_forms : hodgeTateMaps σ γ' u ≃ₗ[PadicAlgCl p] hodgeTateMaps ρ (γ'.comp φ) u :=
    { pull f hf, (Equiv.ofBijective _ h_bij).subtypeEquiv h_iff with }
  exact finrank_eq e_forms

/-- If ρ'(g) = a(g)ρ(g) with scalars a(g) in R, and some nonzero y in C_p has γ(a(g))y = χ(g)^(−v)·g
y near 1, then the multiplicity of the jump u+v of ρ' at γ equals that of u for ρ. -/
lemma jump_twist_of_period (a : Γ → R) {v : ℤ} {y : ℂ_[p]} (hy : y ≠ 0)
    (h_period : ∀ᶠ g : Γ in nearOne Γ, γ (a g) * y = (χ g ^ (-v)).val • toGp g • y)
    (h_twist : ∀ (g : Γ) (x : T), ρ' g x = a g • ρ g x) :
    jump ρ' γ (u + v) = jump ρ γ u := by
  -- `F ↦ y • F` maps the forms of weight `u` for `ρ` onto those of weight `u + v` for `ρ'`.
  let mul_y : (T →ₛₗ[toRingHom γ] ℂ_[p]) ≃ₗ[PadicAlgCl p] (T →ₛₗ[toRingHom γ] ℂ_[p]) :=
    (smulOfNeZero ℂ_[p] (T →ₛₗ[toRingHom γ] ℂ_[p]) y hy).restrictScalars (PadicAlgCl p)
  have h_iff (F : T →ₛₗ[toRingHom γ] ℂ_[p]) :
      y • F ∈ hodgeTateMaps ρ' γ (u + v) ↔ F ∈ hodgeTateMaps ρ γ u := by
    refine forall_congr' fun x ↦ eventually_congr (h_period.mono fun g hg ↦ ?_)
    show (y • F) (ρ' g x) = (χ g ^ (-(u + v))).val • toGp g • (y • F) x ↔
      F (ρ g x) = (χ g ^ (-u)).val • toGp g • F x
    -- With `c = χ(g) ^ (-v) • g • y ≠ 0`, the condition for `y • F` is `c` times the one for `F`.
    set c : ℂ_[p] := (χ g ^ (-v)).val • toGp g • y with hc
    have hc_ne : c ≠ 0 := by simp [hc, hy, smul_eq_zero_iff_eq]
    have h_lhs : (y • F) (ρ' g x) = c * F (ρ g x) := by
      simp [← hg, h_twist, mul_comm, mul_left_comm, mul_assoc]
    have h_rhs : (χ g ^ (-(u + v))).val • toGp g • (y • F) x =
        c * ((χ g ^ (-u)).val • toGp g • F x) :=
      calc _ = ((χ g ^ (-v)).val * (χ g ^ (-u)).val) • (toGp g • y * toGp g • F x) := by
            simp [_root_.zpow_add, smul_mul', mul_comm]
        _ = _ := (smul_mul_smul_comm _ _ _ _).symm
    rw [h_lhs, h_rhs, mul_right_inj' hc_ne]
  have h_comap : (hodgeTateMaps ρ' γ (u + v)).comap mul_y.toLinearMap = hodgeTateMaps ρ γ u :=
    ext h_iff
  exact finrank_eq ((mul_y.ofSubmodule' _).symm ≪≫ₗ ofEq _ _ h_comap)

variable [Module.Finite R T]

/-! ### Bounds, duals and cyclotomic twists -/

/-- For `toGp` with open image and T finite over R, the jump u has multiplicity zero at γ exactly
when there is no non-zero form of weight u. -/
lemma jump_eq_zero_iff : jump ρ γ u = 0 ↔ ∀ f ∈ hodgeTateMaps ρ γ u, f = 0 :=
  finrank_eq_zero.trans eq_bot_iff

/-- For `toGp` with open image and T finitely generated over R, there is a natural number a such
that every jump k of T at γ (nonzero multiplicity) satisfies −a ≤ k ≤ a. -/
lemma exists_jump_bound : ∃ a : ℕ, ∀ k : ℤ, jump ρ γ k ≠ 0 → -a ≤ k ∧ k ≤ a := by
  -- Finitely many forms `f i`, of weights `w i`, span over `ℂ_[p]` all forms that have a weight.
  obtain ⟨f, hf, h_span, -⟩ :=
    exists_fun_fin_finrank_span_eq ℂ_[p] {F | ∃ u, F ∈ hodgeTateMaps ρ γ u}
  choose w hw using hf
  obtain ⟨a, ha⟩ : ∃ a : ℕ, ∀ i, (w i).natAbs ≤ a := exists_le fun i ↦ (w i).natAbs
  refine ⟨a, fun k h_ne ↦ ?_⟩
  by_contra hk
  refine h_ne (jump_eq_zero_iff.2 fun F hF ↦ ?_)
  -- A form of weight `k` is spanned by the `f i` with `w i = k`; outside `[-a, a]` there are none.
  have h_mem : F ∈ span (PadicAlgCl p) (f '' {i | w i = k}) :=
    mem_span_same_weight hw hF (h_span.ge (subset_span ⟨k, hF⟩))
  have h_ne_weight (i) : w i ≠ k := by grind [ha i]
  simpa [h_ne_weight] using h_mem

variable [Algebra.IsAlgebraic ℤ_[p] R] [Module ℤ_[p] T] [IsScalarTower ℤ_[p] R T] [Free R T]

/-- Let R be algebraic over Z_p, `toGp` have open image, and T be finite free and potentially
crystalline (`hρ`). Let b: T' → Hom_R(T,R) be bijective with b(gx,gy) = χ(g)^c b(x,y). Then the
jump u of T' at γ has the multiplicity of the jump −u−c of T. This is the rule for Hodge–Tate
weights under a perfect pairing into a cyclotomic twist. -/
lemma jump_eq_of_pairing [Module R T'] {σ : Representation R Γ T'} (hρ : IsPotentiallyCrystalline ρ)
    (b : T' ≃ₗ[R] T →ₗ[R] R) (c : ℤ)
    (h_equiv : ∀ (g : Γ) (x : T') (y : T), b (σ g x) (ρ g y) = (χ g ^ c).val • b x y) :
    jump σ γ u = jump ρ γ (-u - c) := by
  let v : Basis (Free.ChooseBasisIndex R T) R T := Free.chooseBasis R T
  let w : Basis (Free.ChooseBasisIndex R T) R T' := v.dualBasis.map b.symm
  -- An invertible `P` whose columns are Hodge–Tate vectors of weights `k i`, the jumps of `T`.
  obtain ⟨P, k, h_frame, h_jumps, -⟩ := hρ.exists_isHodgeTateFrame v γ
  -- In the basis `w` of `T'` dual to `v`, the rows of `Pᵀ` are forms of weights `-c - k i`.
  have h_rows : ∀ᶠ g : Γ in nearOne Γ, ∀ i l : Free.ChooseBasisIndex R T,
      (P.valᵀ * ((σ g).toMatrix w w).map γ) i l =
        (χ g ^ (-(-c - k i))).val • toGp g • P.valᵀ i l := by
    filter_upwards [h_frame] with g hg i l
    -- `M` is the transpose of the matrix of `σ g`, and inverts that of `ρ g` up to `χ(g) ^ c`.
    set M := toMatrix₂ w v (b.toLinearMap ∘ₗ σ g) with hM
    have h_transpose : (σ g).toMatrix w w = Mᵀ := by
      ext m j
      simp [hM, w, toMatrix_apply]
    have h_mul : M * (ρ g).toMatrix v v = (χ g ^ c).val • 1 := by
      ext m j
      simp [hM, ← toMatrix₂_compl₂, h_equiv, w, one_apply, Finsupp.single_apply, eq_comm]
    -- Apply `M` to the frame relation for the column `i` of `P`.
    have h_paired : ((cyclotomicGp (toGp g) ^ (-k i) : ℤ_[p]ˣ) : ℤ_[p]) •
          (M.map γ *ᵥ P.val.col i) l =
        (χ g ^ c).val • toGp g • P.val l i := by
      rw [← Pi.smul_apply, ← Matrix.mulVec_smul, ← hg i, mulVec_mulVec, ← Matrix.map_mul, h_mul]
      simp [mulVec_apply_eq_sum, one_apply, apply_ite]
    have h_entry : (P.valᵀ * ((σ g).toMatrix w w).map γ) i l = (M.map γ *ᵥ P.val.col i) l := by
      rw [h_transpose, transpose_map, ← transpose_mul]
      rfl
    calc (P.valᵀ * ((σ g).toMatrix w w).map γ) i l
        = (χ g ^ k i).val • (χ g ^ (-k i)).val • (M.map γ *ᵥ P.val.col i) l := by
          simp [h_entry, smul_smul]
      _ = (χ g ^ k i).val • (χ g ^ c).val • toGp g • P.val l i :=
          congrArg ((χ g ^ k i).val • ·) h_paired
      _ = (χ g ^ (-(-c - k i))).val • toGp g • P.valᵀ i l := by
          simp [smul_smul, sub_eq_add_neg, _root_.zpow_add, mul_comm]
  have h_dual : HasJumps σ γ (univ.val.map fun i ↦ -c - k i) :=
    (hasJumps_of_rows w (unitOfInvertible P.valᵀ) _ h_rows).left
  -- Count the `i` with `u = -c - k i`, that is `-u - c = k i`.
  rw [h_jumps, h_dual, Multiset.count_map, Multiset.count_map]
  exact congrArg _ (Multiset.filter_congr fun i _ ↦ by omega)

/-- For R algebraic over Z_p, `toGp` with open image and T finite free over R, if ρ(g)x = χ(g)^c x
for all g and x, then the only jump at γ is −c, with multiplicity the rank of T. -/
lemma hasJumps_of_cyclotomicGp_zpow (c : ℤ) (h : ∀ (g : Γ) (x : T), ρ g x = (χ g ^ c).val • x) :
    HasJumps ρ γ (Multiset.replicate (finrank R T) (-c)) := by
  -- The coordinate forms of a basis, the rows of the identity matrix, all have weight `-c`.
  have : Nontrivial R := γ.domain_nontrivial
  let e : Basis (Fin (finrank R T)) R T := finBasis R T
  have h_rows (g : Γ) (i l : Fin (finrank R T)) :
      ((1 : GL (Fin (finrank R T)) ℂ_[p]).val * ((ρ g).toMatrix e e).map γ) i l =
        (χ g ^ (-(-c))).val • toGp g • (1 : GL (Fin (finrank R T)) ℂ_[p]) i l := by
    simp +contextual [h, LinearMapClass.map_smul_of_tower (S := R), one_apply, toMatrix_apply,
      apply_ite]
  obtain ⟨h_jumps, -⟩ := hasJumps_of_rows e 1 (fun _ ↦ -c) (.of_forall h_rows)
  simpa using h_jumps

omit [Module.Finite R T] [Algebra.IsAlgebraic ℤ_[p] R] [Free R T] in
/-- Let Γ be a group with an open-image map to Gal(Q̄_p/Q_p), and let ρ, ρ' be representations of Γ
on an R-module T, where R is a ℤ_p-algebra. Suppose ρ' is the twist of ρ by
the c-th power of the p-adic cyclotomic character χ pulled back to Γ, that is, ρ' g x = χ(g)^c • ρ g
x. Then for every ℤ_p-algebra map γ : R → ℂ_p, the multiplicity `jump ρ' γ (u - c)` of the
Hodge–Tate jump u − c of ρ' at γ equals the multiplicity `jump ρ γ u` of the jump u of ρ. -/
lemma jump_twist_cyclotomicGp (c : ℤ)
    (h_twist : ∀ (g : Γ) (x : T), ρ' g x = (χ g ^ c).val • ρ g x) :
    jump ρ' γ (u - c) = jump ρ γ u := by
  -- The case `y = 1`, `a g = χ(g) ^ c` of `jump_twist_of_period`: the cyclotomic character needs no
  -- period.
  rw [sub_eq_add_neg]
  exact jump_twist_of_period (fun g ↦ (χ g ^ c).val • (1 : R)) one_ne_zero
    (.of_forall fun g ↦ by simp) fun g x ↦ by rw [smul_one_smul, h_twist g x]

end

section

variable {p : ℕ} [ThePrime p]
  {Γ R T T' R' ι κ : Type*} [Group Γ] [CommRing R] [AddCommGroup T] [Module R T] [Algebra ℤ_[p] R]
  [AddCommGroup T'] [OverGp Γ p]
  {ρ ρ' : Representation R Γ T} [CommRing R'] [Module R' T'] [Algebra ℤ_[p] R']
  {σ : Representation R' Γ T'} {γ' : R' →ₐ[ℤ_[p]] ℂ_[p]} {φ : R' →+* R} {u : ℤ}
  {γ : R →ₐ[ℤ_[p]] ℂ_[p]} [Module.Finite R T]
  [Algebra.IsAlgebraic ℤ_[p] R] [Free R T] [IsDomain R] [Fintype κ]
  {S : ι → Type _} [∀ i, AddCommGroup (S i)] [∀ i, Module R (S i)] [∀ i, Module ℤ_[p] (S i)]
  [∀ i, IsScalarTower ℤ_[p] R (S i)] [∀ i, Free R (S i)] [∀ i, Module.Finite R (S i)]
  {τ : ∀ i : ι, Representation R Γ (S i)} (h_potCrys : ∀ i : ι, IsPotentiallyCrystalline (τ i))
  (e : Basis κ R' T') {δ : ι → R →ₐ[ℤ_[p]] ℂ_[p]} [∀ i, RingHomCompTriple φ (toRingHom (δ i)) γ']
  (f : ∀ i : ι, T' →ₛₗ[φ] S i)
  (h_equiv : ∀ i : ι, ∀ᶠ g : Γ in nearOne Γ, ∀ x : T', f i (σ g x) = τ i g (f i x))
  (h_indep :
    LinearIndependent ℂ_[p] fun (a : κ) (l : Σ i : ι, Fin (finrank R (S i))) ↦
      δ l.fst ((finBasis R (S l.fst)).coord l.snd (f l.fst (e a))))

/-! ### Modules that map to a family S_i -/

include h_indep in
omit [Algebra.IsAlgebraic ℤ_[p] R] [∀ i, Module ℤ_[p] (S i)] [∀ i, IsScalarTower ℤ_[p] R (S i)] in
/-- Under the independence hypothesis `h_indep`, for any bases b_i of the δ_i-semilinear forms on
S_i, the pull-backs b_{i,y} ∘ f_i span over ℂ_p all γ'-semilinear forms on T'. -/
lemma top_le_span_pullback {m : ι → Type _}
    (b : ∀ i : ι, Basis (m i) ℂ_[p] (S i →ₛₗ[toRingHom (δ i)] ℂ_[p])) :
    ⊤ ≤ span ℂ_[p] (Set.range fun y : Sigma m ↦ b y.fst y.snd ∘ₛₗ f y.fst) := by
  set W : Submodule ℂ_[p] (T' →ₛₗ[(γ' : R' →+* ℂ_[p])] ℂ_[p]) :=
    span ℂ_[p] (Set.range fun y : Sigma m ↦ b y.fst y.snd ∘ₛₗ f y.fst)
  -- Every form on `S i` is a combination of the `b i y`, so its pull-back lies in `W`.
  have h_pull (i : ι) (F : S i →ₛₗ[toRingHom (δ i)] ℂ_[p]) : F ∘ₛₗ f i ∈ W :=
    mapsTo_span (f := id.compl₂ (f i)) (by aesop) ((b i).mem_span F)
  -- Read forms on `T'` as vectors of values on `e`. By `h_indep` the pull-backs of the coordinate
  -- forms give vectors that span `κ → ℂ_[p]`.
  have h_top : ⊤ ≤ W.map (evalOnBasis e).toLinearMap := by
    rw [← span_flip_eq_top_iff_linearIndependent.2 h_indep, span_le, Set.range_subset_iff]
    rintro ⟨i, l⟩
    -- The pull-back of the coordinate form `l` of `S i`, read in `ℂ_[p]` through `δ i`.
    exact ⟨_, h_pull i ((δ i).toSemilinearMap.comp ((finBasis R (S i)).coord l)), rfl⟩
  exact (map_le_map_iff_of_injective (evalOnBasis e).injective ⊤ W).1 (le_top.trans h_top)

include h_indep h_potCrys h_equiv in
/-- Let `toGp` have open image, R be a domain algebraic over Z_p, and each S_i be finite free and
potentially crystalline over R (`h_potCrys`). Let f_i: T' → S_i be φ-semilinear and equivariant
near 1 (`h_equiv`), with δ_i∘φ = γ'. Let e be a finite basis of T'. Suppose (`h_indep`) that the
vectors (δ_i(l(f_i e_a)))_{i,l}, indexed by a, are ℂ_p-independent, where l runs over the
coordinates of S_i. Then every jump of T' at γ' is a jump of some S_i at δ_i. -/
lemma exists_jump_of_linearIndependent : jump σ γ' u ≠ 0 → ∃ i : ι, jump (τ i) (δ i) u ≠ 0 := by
  -- Bases `b i` of the `δ i`-semilinear forms on `S i`, with `b i y` of weight `k i y`.
  choose _ k _ _ b hb _ using fun i : ι ↦
    (h_potCrys i).exists_isHodgeTateFrame (finBasis R (S i)) (δ i)
  have : Module.Finite R' T' := of_basis e
  intro h_ne
  by_contra! h_zero
  refine h_ne (jump_eq_zero_iff.2 fun F hF ↦ ?_)
  -- The pull-backs of the `b i y` span all forms on `T'`, so `F` is spanned by those of weight
  -- `u`; these vanish, as no `S i` has a non-zero form of weight `u`.
  have h_weight (y : Σ i : ι, Fin (finrank R (S i))) :
      b y.fst y.snd ∘ₛₗ f y.fst ∈ hodgeTateMaps σ γ' (k y.fst y.snd) :=
    (pull (f y.fst) (h_equiv y.fst) ⟨b y.fst y.snd, hb y.fst y.snd⟩).property
  have h_mem : F ∈ span (PadicAlgCl p)
      ((fun y : Σ i : ι, Fin (finrank R (S i)) ↦ b y.fst y.snd ∘ₛₗ f y.fst) ''
        {y | k y.fst y.snd = u}) :=
    mem_span_same_weight h_weight hF (top_le_span_pullback e f h_indep b trivial)
  -- It suffices that each of these pull-backs is zero.
  refine (mem_bot (PadicAlgCl p)).1 (span_le.2 ?_ h_mem)
  rintro _ ⟨⟨i, l⟩, rfl, rfl⟩
  have h_b_zero : b i l = 0 := jump_eq_zero_iff.1 (h_zero i) (b i l) (hb i l)
  simp [h_b_zero]

include h_potCrys in
/-- Let R be a domain algebraic over Z_p, `toGp` of open image, and T finite free with jointly
injective (`h_inj`) equivariant (`hf`) R-linear maps f_i to finitely many finite free potentially
crystalline S_i (`h_potCrys`). Then every jump of T at γ is a jump of some S_i at γ.

This is a weak form, without multiplicities, of the additivity of Hodge–Tate weights in exact
sequences. -/
lemma exists_jump_of_jointly_injective [Fintype ι] (f : ∀ i : ι, T →ₗ[R] S i)
    (hf : ∀ (i : ι) (g : Γ) (x : T), f i (ρ g x) = τ i g (f i x))
    (h_inj : ∀ x : T, (∀ i : ι, f i x = 0) → x = 0) :
    jump ρ γ u ≠ 0 → ∃ i : ι, jump (τ i) γ u ≠ 0 := by
  let := γ.toAlgebra
  have : FaithfulSMul R ℂ_[p] := faithfulSMul_tower_top ℤ_[p] R ℂ_[p]
  -- The coordinates of the `f i` on a basis of `T` are independent over `R`, so over `ℂ_[p]`.
  let coords : T →ₗ[R] (Σ i : ι, Fin (finrank R (S i))) → R :=
    (Pi.basis fun i ↦ finBasis R (S i)).equivFun.toLinearMap ∘ₗ pi f
  have h_ker : ker coords = ⊥ := by simpa [coords, ker_eq_bot', funext_iff]
  exact exists_jump_of_linearIndependent h_potCrys (finBasis R T) f (fun i ↦ .of_forall (hf i))
    (linearIndependent_algebraMap_comp_iff.2 ((finBasis R T).linearIndependent.map' coords h_ker))

variable [Module ℤ_[p] T] [IsScalarTower ℤ_[p] R T] [Module ℤ_[p] T'] [FaithfulSMul ℤ_[p] R]
  (f : ∀ i : ι, T' →ₗ[ℤ_[p]] S i) (e : Basis κ ℤ_[p] T')

/-! ### Restriction of scalars from R to ℤ_p -/

/-- Let R ⊃ Z_p be an algebraic domain and each S_i finite free over R. Let the f_i: T' → S_i be
Z_p-linear and jointly injective, and let (e_a) be a finite Z_p-basis of T'. Then the vectors
v_a = (γ(l-th coordinate of f_i e_a))_{i,γ,l} are C_p-linearly independent, where γ runs over the
Z_p-algebra maps R → C_p. -/
lemma linearIndependent_algHom_coord (h_inj : ∀ x : T', (∀ i : ι, f i x = 0) → x = 0) :
    LinearIndependent ℂ_[p]
      fun (a : κ) (l : Σ i : ι × (R →ₐ[ℤ_[p]] ℂ_[p]), Fin (finrank R (S i.fst))) ↦
        l.fst.snd ((finBasis R (S l.fst.fst)).coord l.snd (f l.fst.fst (e a))) := by
  classical
  -- The claim: the space of linear relations `a : κ → ℂ_[p]` among the vectors is zero. It is
  -- stable under the Galois group, so by `le_of_hodgeTate_stable` it suffices to kill the fixed
  -- algebraic relations of norm at most one. These have coefficients in `ℤ_[p]`.
  rw [Fintype.linearIndependent_iff', ← le_bot_iff]
  refine le_of_hodgeTate_stable le_top 0 _ ⊥ (fun a ha g ↦ ?_) ?_
  · -- Apply `g` to the relation at the embedding `g⁻¹ ∘ γ`.
    ext ⟨⟨i, γ⟩, l⟩
    simpa [smul_sum] using congrArg (fun y : ℂ_[p] ↦ g • y)
      (congrFun ha ⟨(i, (MulSemiringAction.toAlgHom _ _ g⁻¹).comp γ), l⟩)
  intro a _ h_rel h_norm _ _ h_fix
  obtain ⟨b, rfl⟩ : ∃ b : κ → ℚ_[p], (fun k ↦ algebraMap ℚ_[p] (PadicAlgCl p) (b k)) = a := by
    choose b hb using fun k ↦ (InfiniteGalois.mem_bot_iff_fixed (a k)).2 (h_fix k)
    exact ⟨b, funext hb⟩
  let c (k : κ) : ℤ_[p] := ⟨b k, by simpa using h_norm k⟩
  -- One embedding `γ` is enough: it is injective, as `R` is an algebraic domain.
  have γ : R →ₐ[ℤ_[p]] ℂ_[p] := IsAlgClosed.lift
  algebraize [γ.toRingHom]
  have hγ : Function.Injective γ := (faithfulSMul_tower_top ℤ_[p] R _).algebraMap_injective
  have h_coord (i : ι) (l : Fin (finrank R (S i))) :
      (finBasis R (S i)).coord l (f i (∑ k, c k • e k)) = 0 :=
    -- the relation `h_rel` at the embedding `γ`
    (map_eq_zero_iff γ hγ).1 (by simpa [smul_def'] using! congrFun h_rel ⟨(i, γ), l⟩)
  have h_sum : ∑ k, c k • e k = 0 :=
    h_inj _ fun i ↦ (finBasis R (S i)).forall_coord_eq_zero_iff.1 (h_coord i)
  have hc (k : κ) : c k = 0 := linearIndependent_iff.1 e.linearIndependent c h_sum k
  simpa [c, funext_iff] using fun k ↦ congrArg Subtype.val (hc k)

/-- For Z_p-linear maps f_i: T' → S_i and a pair (i, k) in ι × κ, the map f_i regarded as semilinear
along the structure map Z_p → R; it does not depend on k. -/
def asSemilinear (i : ι × κ) : T' →ₛₗ[algebraMap ℤ_[p] R] S i.fst := ⟨f i.fst, by simp⟩

/-- Composing the structure map ℤ_p → R with γ gives the structure map ℤ_p → ℂ_p. -/
instance : RingHomCompTriple (algebraMap (ℤ_[p]) R) (toRingHom γ) (toRingHom (ofId ℤ_[p] ℂ_[p])) :=
  ⟨by simp⟩

variable [Module.Finite ℤ_[p] R]

/-- The ℤ_p-algebra maps R → ℂ_p, finitely many as R is finite over ℤ_p, form a `Fintype`. -/
instance : Fintype (R →ₐ[ℤ_[p]] ℂ_[p]) := ofFinite _

/-- A domain R that is finite free over ℤ_p has rank_{ℤ_p} R embeddings into ℂ_p over ℤ_p. -/
@[simp]
lemma card_algHom_eq_finrank : Fintype.card (R →ₐ[ℤ_[p]] ℂ_[p]) = finrank ℤ_[p] R := by
  refine le_antisymm (card_eq_nat_card.trans_le (card_algHom_le_finrank ℤ_[p] R ℂ_[p])) ?_
  -- The values of the embeddings on a basis of `R` give `finrank ℤ_[p] R` independent vectors
  -- with one coordinate for each embedding.
  simpa using (linearIndependent_algHom_coord (R := R) (![.id] : Fin 1 → R →ₗ[ℤ_[p]] R)
    (finBasis ℤ_[p] R) (by simp)).fintype_card_le_finrank

open scoped Classical in
/-- Let `toGp` have open image, R be a domain finite free over ℤ_p, and T be finite free over R and
potentially crystalline. With γ running over the ℤ_p-algebra maps R → ℂ_p: (a) the multiplicity of
the jump u of T as a ℤ_p-module is ∑_γ jump_γ(u); (b) for ζ ∈ R and w ∈ ℂ_p, a set F of ℤ_p-linear
forms f of weight u with f(ζt) = w·f(t) spans over ℂ_p a space of dimension at most the sum of
jump_γ(u) over the γ with γ(ζ) = w. Part (a) is the formula for the graded dimensions of D_dR as a
sum over the embeddings of the coefficients. -/
lemma IsPotentiallyCrystalline.sum_jump_eq_jump_overZp (h : IsPotentiallyCrystalline ρ) :
    -- (a)
    (∀ u : ℤ, ∑ γ : R →ₐ[ℤ_[p]] ℂ_[p], jump ρ γ u = jump (overZp ρ) (ofId ℤ_[p] ℂ_[p]) u) ∧
    -- (b)
    ∀ (ζ : R) (w : ℂ_[p]) (u : ℤ) (F : Set (T →ₛₗ[toRingHom (ofId ℤ_[p] ℂ_[p])] ℂ_[p])),
      (∀ f ∈ F,
        f ∈ hodgeTateMaps (overZp ρ) (ofId ℤ_[p] ℂ_[p]) u ∧
        ∀ t : T, f (ζ • t) = w * f t) →
      finrank ℂ_[p] (span ℂ_[p] F) ≤ ∑ γ : R →ₐ[ℤ_[p]] ℂ_[p] with γ ζ = w, jump ρ γ u := by
  -- The Hodge–Tate bases `b γ` of the `γ`-semilinear maps, over all embeddings `γ`, together form a
  -- basis `B` of the `ℤ_[p]`-linear maps: they span by `top_le_span_pullback`, and their number is
  -- right.
  have e : Basis (Fin (finrank ℤ_[p] R) × Fin (finrank R T)) ℤ_[p] T :=
    (finBasis ℤ_[p] R).smulTower (finBasis R T)
  have : Module.Finite ℤ_[p] T := of_basis e
  -- For each embedding `γ`: weights `k γ` and a basis `b γ` of forms of these weights.
  choose P k h_frame h_jumps b hb h_val using h.exists_isHodgeTateFrame (finBasis R T)
  have h_inj : ∀ x : T, (∀ i : Fin 1, (![LinearMap.id] : Fin 1 → T →ₗ[ℤ_[p]] T) i x = 0) →
      x = 0 := by
    simp
  -- The coordinates of `e` at all embeddings are independent over `ℂ_[p]`.
  have h_indep : LinearIndependent ℂ_[p]
      fun (a : Fin (finrank ℤ_[p] R) × Fin (finrank R T))
        (l : Σ i : Fin 1 × (R →ₐ[ℤ_[p]] ℂ_[p]), Fin (finrank R T)) ↦
        l.fst.snd ((finBasis R T).coord l.snd
          ((![LinearMap.id] : Fin 1 → T →ₗ[ℤ_[p]] T) l.fst.fst (e a))) :=
    linearIndependent_algHom_coord (R := R) ![LinearMap.id] e h_inj
  let B := basisOfTopLeSpanOfCardEqFinrank _
    (top_le_span_pullback e (asSemilinear ![LinearMap.id]) h_indep fun i ↦ b i.snd)
    (by simp [finrank_eq (evalOnBasis e), -toRingHom_ofId])
  have hB (y : Σ i : Fin 1 × (R →ₐ[ℤ_[p]] ℂ_[p]), Fin (finrank R T)) :
      B y ∈ hodgeTateMaps (overZp ρ) (ofId ℤ_[p] ℂ_[p]) (k y.fst.snd y.snd) := by
    -- `using!`: the membership for `ρ` at `γ` is the one for `overZp ρ` only up to unfolding.
    simpa [B, asSemilinear, -toRingHom_ofId] using! hb y.fst.snd y.snd
  have h_count (γ : R →ₐ[ℤ_[p]] ℂ_[p]) (u : ℤ) : jump ρ γ u = ∑ i, if k γ i = u then 1 else 0 := by
    simp [h_jumps γ u, ↓Multiset.count_map, ← filter_val, eq_comm, card_filter, -sum_boole]
  refine ⟨fun u ↦ ?_, fun ζ w u F hF ↦ ?_⟩
  · -- Both sides count the pairs `(γ, i)` with `k γ i = u`.
    simp [h_count, hasJumps_of_basis hB u, ↓Multiset.count_map, ← filter_val, eq_comm,
      card_filter, Fintype.sum_sigma, sum_prod_type, -sum_boole]
  -- Each `f ∈ F` involves only basis vectors with `γ ζ = w` and weight `u`.
  have h_span : F ⊆ span ℂ_[p] (B '' {y | y.fst.snd ζ = w ∧ k y.fst.snd y.snd = u}) := by
    refine fun f hf ↦ B.mem_span_image.2 fun y hy ↦ ⟨?_, ?_⟩
    · -- Multiplication by `ζ` scales `f` by `w` and `B z` by `γ ζ`; compare coordinates at `y`.
      have h_scale : ∑ z, B.repr f z • z.fst.snd ζ • B z = w • f := by
        ext t
        simpa [B, asSemilinear, (hF f hf).2, -toRingHom_ofId] using
          DFunLike.congr_fun (B.sum_repr f) (ζ • t)
      simpa [mul_comm w, Finsupp.mem_support_iff.1 hy, Finsupp.single_apply, -toRingHom_ofId]
        using B.ext_elem_iff.1 h_scale y
    · -- A form of weight `u` is spanned by the basis vectors of weight `u`.
      exact B.mem_span_image.1
        (span_subset_span _ _ _
          (mem_span_same_weight hB (hF f hf).1 (by simp [-toRingHom_ofId]))) hy
  calc
    finrank ℂ_[p] (span ℂ_[p] F) ≤ #(B '' {y | y.fst.snd ζ = w ∧ k y.fst.snd y.snd = u}).toFinset :=
      (finrank_mono (span_le.2 h_span)).trans (finrank_span_le_card _)
    _ = ∑ γ with γ ζ = w, jump ρ γ u := by
      simp [h_count, B.injective, card_image_of_injective, card_filter, Fintype.sum_sigma,
        sum_prod_type, sum_filter, ite_and, -sum_boole, -toRingHom_ofId]

end

end Jumps

end New.Period

end
