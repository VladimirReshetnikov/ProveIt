import Lib.GaloisRep.Main.LocalConditions
import Lib.General.LinearAlgebra.TensorChains
import Lib.PadicHodge.Limit.CrystallineLimit

/-!
# Hodge–Tate jumps with bounded denominators and local conditions at limits of traces

The multiplicities of Hodge–Tate jumps can be read from traces with uniformly bounded denominators,
which lets jumps pass to `p`-adic limits of representations. These bounded denominators are used to
prove `New.GaloisRep.local_clauses_of_trace_limit`.

## Overview of this theory

One period ring `B = New.Period.Bmax` defines crystalline and potentially crystalline
representations `T` of a group `Γ` mapping to `G_p = Gal(ℚ̄_p/ℚ_p)`, such as `G_K` with `K/ℚ_p`
finite. This ring is Colmez's `B_max`, not Fontaine's `B_cris`, and their comparison is not
formalised. `B` also gives a linear Frobenius and the crystalline cocycles `Z_f(T)`. The Hodge–Tate
jumps of `T` form a multiset of integers, defined via `ℂ_p ⊗ T`.

* `New.Period.ax_mem_closure_fixedField`, `New.Period.tate_eq_zero_of_cyclotomicGp_twist`: for a
  subgroup `J` of `G_p`, `ℂ_p^J` lies in the closure of `ℚ̄_p^J`. An element of `ℂ_p(i)`, `i ≠ 0`,
  fixed by an open subgroup is `0`.
* `New.Period.IsAdmissible.of_jointly_injective`: being crystalline, or potentially crystalline,
  passes to subrepresentations of finite direct sums.
* `New.Period.crysCocycles.finrank_eq`: let `T` be a potentially crystalline `ℤ_p`-lattice with
  jumps `J`. Then `Z_f(T)` is finitely generated of rank `rk T + n · #(negative jumps)`, where `n`
  is the index of the image of `Γ` in `G_p`.
* `New.GaloisRep.local_clauses_of_trace_limit`: let `r` be a continuous Galois representation with
  non-degenerate trace form. Let its trace be a uniform limit of linear combinations of traces of
  continuous representations unramified or crystalline at a place `A`. Require finitely many
  approximations, or the same jumps for all terms. Then `r` is unramified or crystalline at `A`. Its
  jumps follow if their multiplicities are compatible with the limit. A polynomial killing an
  element `s` at `A` passes to `r`, given bounded degrees and convergence weighted by each
  coefficient.

The development proves only the parts of the standard theory that it uses: of the Ax–Sen–Tate
theorem only Ax's weaker form, and of Tate's theorem only the statement on `H⁰`. The notions below
take the place of Fontaine's admissible representations, of the Weil–Deligne representation and of
the Bloch–Kato rank formula. For local–global compatibility of automorphic Galois representations,
only the passage to limits is proved, with `r` given. Crystalline means that the invariants span
`B ⊗ T`.

In place of the Weil–Deligne representation stands `New.Period.linearFrob`. For `s ∈ Γ` and `m ∈ ℕ`,
it is a chosen `B`-linear endomorphism of `B ⊗ T`. It agrees with `φ^m s ⊗ s` on `D_pcris(T)` when
one exists, where `φ` is the Frobenius of `B`. In place of `H¹_f` stands the rank of `Z_f(T)`.

Organisation of `Lib.PadicHodge`. (1) `PeriodRings`: Ax's theorem, `A_inf`, Fontaine's map `θ`,
`B`, the period `t` of `ℤ_p(1)`, `B_dR`. (2) `TateSen`: Tate's theorem, invariants of `B_dR`.
(3) `Crystalline`: `Basic` (definitions, twists), `HodgeTateJumps`, `Regularity` (regularity of
`B`, using `Kisin`). (4) `BlochKato`: the rank, by the fundamental exact sequence; duality is in
`Lib.ClassField.LocalDuality.CrystallineDuality`. (5) `Limit`: the trace-limit theorem.

## Main definitions and results

* `New.Period.exists_uniform_trace_sum_eq_jump`: the multiplicity of one jump is `t` times a sum of
  traces with coefficients of norm at most `1`, where `t` is the same for every crystalline lattice
  with jumps in `[0, n]` and depends only on `Γ`, `n` and the jump.

Notions from other files:
* `New.GaloisRep.HasJumpsAt`: For each local datum at `A` with embedding `e` and each `g` in
  `Gal(ℚ̄_ℓ/ℚ_ℓ)`, the Hodge–Tate jumps of `r` at `g`, with multiplicity, are `J` at the embedding
  `ι_ℓ⁻¹ ∘ g⁻¹ ∘ e` of `E` in `ℂ`.
* `New.Period.IsKilledBy`: the form of `PolyKillsAt` above ℓ. For a Weil pair (s, k), with s acting
  on residues as x ↦ x^(1/ℓ^k), it says that the representation T is potentially crystalline. It
  also says that P kills the operator β = `linearFrob` on `Bmax ℓ` ⊗ T, which acts as φ^k s on the
  elements fixed by all g near 1.
* `New.Period.IsPotentiallyCrystalline`: the elements of B⊗T fixed by all g with j(g) near 1 span
  B⊗T over B.

## Relation to the literature

Known result: Limits of crystalline representations with bounded weights are crystalline. Here the
hypothesis is a uniform limit of traces with unbounded coefficients and ranks, and crystallinity is
Liu's theorem applied to the image of the group ring. The file also proves limit formulas for the
multiplicities of jumps and for killing polynomials. Source: T. Liu, Torsion p-adic Galois
representations and a conjecture of Fontaine, Ann. Sci. ENS 40 (2007) 633–674; L. Berger, Limites de
représentations cristallines, Compositio Math. 140 (2004) 1473–1498; for the passage from traces to
the image of the group ring, P. Wake, C. Wang-Erickson, Deformation conditions for
pseudorepresentations, Forum Math. Sigma 7 (2019).
-/

/-!
## Bounded denominators of Hodge–Tate projectors for jumps in [0, n]

Here the instance `𝒥 : OverGp Γ p` gives a map from `Γ` to the absolute Galois group of `ℚ_p`.
`New.Period.IsCrystallineUpTo n ρ` says that `ρ` is crystalline with all jumps in `[0, n]`.
`New.Period.jump` is the multiplicity of a jump.
-/

section HodgeTateProjectors

open Module Matrix IsScalarTower RingHom Function Algebra Submodule.Quotient New.Period.BdRPlus
  algebraMap

/-- Bounded denominators in `BdRPlus`. Let `R` be a coefficient ring (the integers of a finite
Galois extension of `ℚ_p` in `ℚ̄_p`) and let `e ∈ Amax` be nonzero in `BdR`. Then some
`κ ∈ BdRPlus` with `θ κ ≠ 0`, where `θ = thetaBdR : BdRPlus → ℂ_p`, has `‖θ (κ * z)‖ ≤ 1` for
every `z` such that `e • z` is the image of some `y` under the map `Amax ⊗ R → BdRPlus`. -/
lemma New.Period.exists_norm_thetaBdR_mul_le {p : ℕ} [ThePrime p] (R : CoeffRing p) {e : Amax}
    (he_ne_zero : algebraMap Amax BdR e ≠ 0) :
    ∃ κ : BdRPlus,
      thetaBdR κ ≠ 0 ∧
      ∀ {z : BdRPlus} {y : TensorProduct ℤ_[p] Amax R},
        (toAlgHom ℤ_[p] R BdRPlus).liftEquiv ℤ_[p] Amax R BdRPlus y = e • z →
          ‖thetaBdR (κ * z)‖ ≤ 1 := by
  -- Write `e = ξ ^ m * δ` with `δ` a unit of `BdRPlus` and `ξ = xi`.
  obtain ⟨m, δ, hδ⟩ : ∃ m : ℕ, Associated ((xi : BdRPlus) ^ m) (algebraMap Amax BdRPlus e) :=
    exists_associated_xi_pow
      (ne_zero_of_map ((algebraMap_apply Amax BdRPlus BdR e).symm.trans_ne he_ne_zero))
  set O : TensorProduct ℤ_[p] Amax R →ₐ[Amax] BdRPlus :=
    (toAlgHom ℤ_[p] R BdRPlus).liftEquiv ℤ_[p] Amax R BdRPlus
  -- `N` is `A + ξ ^ (m + 1) B`, for `A` the image of `Amax` in `B = BdRPlus`.
  let N : Submodule Amax BdRPlus :=
    (((toAlgHom Amax BPlus BdRPlus).toLinearMap ∘ₗ Algebra.linearMap Amax BPlus).coprod
      (.mulLeft Amax (xi ^ (m + 1) • 1))).range
  -- A power of `p` moves each `O y` into `N`; by finite generation one power `p ^ c` serves all.
  obtain ⟨c, hc⟩ :
      IsNilpotent (p : End Amax (TensorProduct ℤ_[p] Amax R ⧸ N.comap O.toLinearMap)) := by
    refine End.isNilpotent_iff_of_finite.mpr (Quot.ind fun y ↦ ?_)
    obtain ⟨l, a, v, h⟩ := exists_Ainf_approx (O y) (m + 1)
    exact ⟨l, mod_cast (mk_eq_zero _).mpr ⟨(a, v), by simp [← h, smul_def, ← algebraMap_apply]⟩⟩
  have hκ : thetaBdR ((p : BdRPlus) ^ (2 * m) * ((δ : BdRPlus) * (p : BdRPlus) ^ c)) ≠ 0 := by
    simp [← isUnit_iff, NeZero.ne]
  refine ⟨(p : BdRPlus) ^ (2 * m) * ((δ : BdRPlus) * (p : BdRPlus) ^ c), hκ, fun {z y} h ↦ ?_⟩
  -- So `p ^ c * e * z = a + ξ ^ (m + 1) * v`, and `ξ ^ m` divides `a` since `e = ξ ^ m * δ`.
  -- `p ^ c` kills the class of `y` modulo the preimage of `N`.
  have h_pow_y : ((p ^ c : ℕ) : End Amax (_ ⧸ N.comap O.toLinearMap)) ⟦y⟧ = 0 := by
    rw [p.cast_pow c, hc, LinearMap.zero_apply]
  obtain ⟨a, v, ha⟩ : ∃ (a : Amax) (v : BdRPlus),
      ((a : BPlus) : BdRPlus) = (xi : BdRPlus) ^ m * (δ * (p ^ c * z) - xi * v) := by
    simpa [N, h, smul_def, ← hδ, pow_succ, mul_assoc, mul_left_comm (_ ^ c), ← mul_sub,
      ← eq_sub_iff_add_eq] using (mk_eq_zero _).mp h_pow_y
  obtain ⟨a', ha'⟩ : (xi : BPlus) ^ m ∣ (a : BPlus) := xi_pow_dvd_iff.mp ⟨_, ha⟩
  -- The quotient `a'` lies in `BPlus`, and `p ^ (2 * m) * a'` comes from some `a'' ∈ Amax`, because
  -- `ξ` divides `mu` (`amaxImage.p_pow_mul_mem_of_dvd_mu`).
  obtain ⟨a'', ha''⟩ : p ^ (2 * m) * a' ∈ amaxImage :=
    amaxImage.p_pow_mul_mem_of_dvd_mu ⟨_, xi_mul_tau.symm⟩ ⟨a, by simpa [smul_def]⟩
  -- Cancel `ξ ^ m` and apply `θ`, which kills `ξ`: the element in question is `θ a''`.
  have h_theta : thetaBdR ((p : BdRPlus) ^ (2 * m) * ((δ : BdRPlus) * (p : BdRPlus) ^ c) * z) =
      (thetaAmax a'' : ℂ_[p]) := by
    clear he_ne_zero hc hκ
    simp_all [← thetaBPlus_algebraMap_Amax, ← thetaBdR_algebraMap_BPlus, ← algebraMap_apply,
      prime_xi.ne_zero, mul_assoc]
  rw [h_theta, ← mem_valRingCp]
  exact (thetaAmax a'').prop

/-- The diagonal matrix with entry `1` at the indices `i` with `k i = w` and `0` elsewhere: the
projector onto the coordinates of Hodge–Tate weight `w`. -/
private def New.Period.jumpProjector {α A : Type*} [DecidableEq α] [Ring A] (w : ℤ) (k : α → ℤ) :
    Matrix α α A :=
  diagonal fun i ↦ if w = k i then 1 else 0
/-- Trace formula for the multiplicity of a jump. Let `W · diag (t ^ k)` be a Hodge frame of `T`,
basis `ε` (`IsHodgeFrame` for `⊤`: fixed by the twisted action of `Γ`, `W` a unit over `BdRPlus`),
and `z = W · P · W⁻¹ · x`, where `P = jumpProjector w k` keeps the coordinates of weight `w`. For
`r` potentially crystalline and `ℤ_p`-linear `u` with `u (g y) = r g * u y`, `u x = 1`, the sum over
`s` of `thetaBdR (z s) * γ (trace (u (ε s)))` is the multiplicity of the jump `w` of `r` at `γ`. -/
private lemma New.Period.sum_thetaBdR_mul_trace_eq_jump_of_isHodgeFrame {p : ℕ} [ThePrime p]
    {Γ : Type} [Group Γ] [OverGp Γ p] {T ι : Type} [AddCommGroup T] [Module ℤ_[p] T] [Fintype ι]
    [DecidableEq ι] (ε : Basis ι ℤ_[p] T) {ρ : Representation ℤ_[p] Γ T} (x : T) (w : ℤ)
    {U : Matrix ι ι BdR} {Y : SpecialLinearGroup ι (PadicAlgCl p)} {W : (Matrix ι ι BdRPlus)ˣ}
    {k : ι → ℤ} (hF : IsHodgeFrame (⊤ : Filter Γ) (fun g : Γ ↦ (ρ g).toMatrix ε ε) U Y W k)
    {z : ι → BdRPlus} (hz : z = ↑W *ᵥ jumpProjector w k *ᵥ ↑W⁻¹ *ᵥ (↑) ∘ ε.repr x)
    (γ : PadicAlgCl p →ₐ[ℤ_[p]] ℂ_[p]) (r : PadicRep Γ p)
    (u : T →ₗ[ℤ_[p]] Matrix r.Index r.Index (PadicAlgCl p))
    (hu : ∀ (g : Γ) (y : T), u (ρ g y) = (r.rep g).val * u y) (hx : u x = 1)
    (h_pcr : IsPotentiallyCrystalline (matrixRep r.rep)) :
    ∑ s : ι, thetaBdR (z s) * γ (u (ε s)).trace = jump (matrixRep r.rep) γ w := by
  -- Hodge–Tate bases: `b` from a frame `P` of `r`, and `β` from the rows of `(θ W)⁻¹` for `T`.
  -- The matrix `F y = P⁻¹ (γ (u y))` satisfies `∑ s, θ (z s) • F (ε s) = jumpProjector w k₁ * F x`,
  -- a projector onto the jump `w` of `r`; taking traces gives the multiplicity.
  have : Module.Finite ℤ_[p] T := Finite.of_basis ε
  obtain ⟨P, k₁, -, h_jumps, b, hb, hbP⟩ :=
    h_pcr.exists_isHodgeTateFrame (Pi.basisFun (PadicAlgCl p) r.Index) γ
  -- `β l` has weight `k l`, and its values on `ε` are the row `l` of `(θ W)⁻¹`.
  obtain ⟨β, hβ, hβW⟩ := (hasJumps_of_rows (ρ := ρ) (γ := ofId ℤ_[p] ℂ_[p]) ε
    (W.map thetaBdR.toRingHom.mapMatrix.toMonoidHom)⁻¹ k
    -- (`by exact` waits for the expected type; elaborated at once this times out)
    (by exact .of_forall fun g ↦ inv_mul_apply_of_isHodgeTateFrame
          (isHodgeTateFrame_of_hodgeMatrix (hF.eventually_mul_smul_eq g)))).right
  let F (y : T) : Matrix r.Index r.Index ℂ_[p] :=
    (↑P⁻¹ : Matrix r.Index r.Index ℂ_[p]) * (u y).map γ
  suffices h_proj : ∑ s, thetaBdR (z s) • F (ε s) = jumpProjector w k₁ * F x by
    -- Multiply by `P` and take traces; `u x = 1` leaves the trace of the projector.
    have h_trace : ((P : Matrix r.Index r.Index ℂ_[p]) * ∑ s, thetaBdR (z s) • F (ε s)).trace =
        ((P : Matrix r.Index r.Index ℂ_[p]) * (jumpProjector w k₁ * F x)).trace := by
      rw [h_proj]
    simpa [F, Finset.mul_sum, mul_assoc, Matrix.trace_mul_comm (P : Matrix r.Index r.Index ℂ_[p]),
      jumpProjector, hx, h_jumps w, Multiset.count_map, AddMonoidHom.map_trace, ← Finset.filter_val,
      Finset.card_val] using h_trace
  ext i c
  -- The entry `(i, c)` of `F` is a map `φ` of weight `k₁ i` on `T`, hence a combination of the
  -- `β l` with `k l = k₁ i` with algebraic coefficients (`hodgeTateMaps.mem_span_same_weight`).
  have h_entry (y : T) : F y i c = b i (u y *ᵥ Pi.single c 1) := by
    simp [pi_eq_sum_univ' (col _ c), F, ← hbP, ↓mul_apply, mul_comm]
  -- `φ` pulls `b i` back along the equivariant map `y ↦ u y *ᵥ Pi.single c 1`.
  let φ : hodgeTateMaps ρ (ofId ℤ_[p] ℂ_[p]) (k₁ i) :=
    hodgeTateMaps.pull (φ := algebraMap ℤ_[p] (PadicAlgCl p)) ⟨applyVec u (Pi.single c 1), by simp⟩
      (by simp [hu, -mulVec_single]) ⟨b i, hb i⟩
  -- The coordinates of `W⁻¹ z` are those of `W⁻¹ x` of weight `w`.
  have h_coord : (↑W⁻¹ : Matrix ι ι BdRPlus) *ᵥ z =
      jumpProjector w k *ᵥ (↑W⁻¹ : Matrix ι ι BdRPlus) *ᵥ (↑) ∘ ε.repr x :=
    (congrArg _ hz).trans (inv_smul_smul W _)
  -- Both sides of the claim are linear in the map, so it passes from these `β l` to their span.
  have h_span (ψ : T →ₛₗ[(ofId ℤ_[p] ℂ_[p] : ℤ_[p] →+* ℂ_[p])] ℂ_[p])
      (hψ : ψ ∈ Submodule.span (PadicAlgCl p) (β '' {l | k l = k₁ i})) :
      ∑ s, thetaBdR (z s) * ψ (ε s) = (if w = k₁ i then 1 else 0) * ψ x := by
    induction hψ using Submodule.span_induction with
    | mem _ h =>
      -- For `β l` the claim is `θ` of coordinate `l` of `h_coord`.
      obtain ⟨l, hl : k l = k₁ i, rfl⟩ := h
      have h_coord_l : thetaBdR (((↑W⁻¹ : Matrix ι ι BdRPlus) *ᵥ z) l) =
          thetaBdR ((jumpProjector w k *ᵥ (↑W⁻¹ : Matrix ι ι BdRPlus) *ᵥ (↑) ∘ ε.repr x) l) := by
        rw [h_coord]
      rw [← ε.sum_repr x, map_sum]
      simpa [-toRingHom_ofId, hβW, hl, jumpProjector, mulVec, dotProduct, smul_def, diagonal,
        apply_ite, ite_apply, mul_comm] using h_coord_l
    | zero => simp only [LinearMap.zero_apply, mul_zero, Finset.sum_const_zero]
    | add ψ₁ ψ₂ _ _ h₁ h₂ =>
      simp only [LinearMap.add_apply, mul_add, Finset.sum_add_distrib, h₁, h₂]
    | smul a ψ' _ h =>
      simp only [LinearMap.smul_apply, mul_smul_comm, ← Finset.smul_sum, h]
  simp only [Matrix.sum_apply, Matrix.smul_apply, h_entry, smul_eq_mul, diagonal_mul, jumpProjector]
  exact h_span φ (hodgeTateMaps.mem_span_same_weight hβ φ.prop (β.mem_span _))

/-- Integrality of the projection onto one jump. Let `U * Y = W · diag (t ^ k)` be a Hodge frame
(`IsHodgeFrame`) with `det Y = 1` and `U * U' = e • 1`, and let `y` over `Amax ⊗ R` map to `Y`
under `O`. Then `e` times the projection `W · P · W⁻¹ · x` onto the coordinates of weight `w`
(`P = jumpProjector w k`) is the image under `O` of `M x`, with `M = U · y · P · adj y · U'`. -/
private lemma New.Period.map_mulVec_apply_eq_smul_of_isHodgeFrame {p : ℕ} [ThePrime p] {Γ : Type}
    [Group Γ] [OverGp Γ p] {T ι : Type} [AddCommGroup T] [Module ℤ_[p] T] [Fintype ι]
    [DecidableEq ι] (ε : Basis ι ℤ_[p] T) {ρ : Representation ℤ_[p] Γ T} (x : T) (w : ℤ)
    {R : CoeffRing p} (O : TensorProduct ℤ_[p] Amax R →ₐ[Amax] BdRPlus) {e : Amax}
    {U U' : Matrix ι ι Amax} (hUU' : U * U' = e • 1) {Y : Matrix ι ι (PadicAlgCl p)}
    (hY_det : Y.det = 1) {W : (Matrix ι ι BdRPlus)ˣ} {k : ι → ℤ}
    (hF : IsHodgeFrame (⊤ : Filter Γ) (fun g : Γ ↦ (ρ g).toMatrix ε ε)
      ((algebraMap Amax BdR).mapMatrix U) ⟨Y, hY_det⟩ W k)
    {y : Matrix ι ι (TensorProduct ℤ_[p] Amax R)}
    (hy : O.mapMatrix y = (algebraMap (PadicAlgCl p) BdRPlus).mapMatrix Y) (s : ι) :
    O (((U.map (↑) * y * jumpProjector w k * y.adjugate * U'.map (↑)) *ᵥ (↑) ∘ ε.repr x) s) =
      e • (↑W *ᵥ jumpProjector w k *ᵥ ↑W⁻¹ *ᵥ (↑) ∘ ε.repr x) s := by
  set M : Matrix ι ι (TensorProduct ℤ_[p] Amax R) :=
    U.map (↑) * y * jumpProjector w k * y.adjugate * U'.map (↑)
  -- Diagonal matrices commute, so `U * Y` conjugates the projector as `W` does.
  have h_conj : SemiconjBy (U.map (↑) * (algebraMap (PadicAlgCl p) BdRPlus).mapMatrix Y)
      ((jumpProjector w k).map O)
      ((W : Matrix ι ι BdRPlus) * jumpProjector w k * (↑W⁻¹ : Matrix ι ι BdRPlus)) := by
    refine map_injective (IsFractionRing.injective _ BdR) ?_
    -- The frame equation `U * Y = W * diag (t ^ k)`, written with the maps that appear below.
    have hUY : U.map (algebraMap BdRPlus BdR ∘ ((↑) : Amax → BdRPlus)) *
        Y.map (algebraMap BdRPlus BdR ∘ algebraMap (PadicAlgCl p) BdRPlus) = hodgeMatrix W k :=
      hF.mul_map_eq
    -- `simp` distributes the map over the products, which leaves `U * Y` in the form of `hUY`.
    simp
    rw [hUY, hodgeMatrix, ← mul_assoc]
    simp [jumpProjector, mul_assoc]
  -- `O` commutes with the product `M *ᵥ x`.
  rw [show O _ = (O.mapMatrix M *ᵥ O ∘ (↑) ∘ ε.repr x) s from O.toRingHom.map_mulVec M _ s]
  -- Hence `O M = e • W P W⁻¹`, because `Y.det = 1` and `U * U' = e • 1`. The flags
  -- `-mapMatrix_apply` and `-TensorProduct.algebraMap_apply` keep `O.mapMatrix` and `algebraMap`
  -- folded so that `hy` and `h_conj` apply; without them `simp` unfolds both first.
  simp [↓map_mul, O.map_adjugate, comp_def, ← map_det, hy, hY_det, hUU', M, h_conj.eq,
    mul_assoc, mul_adjugate, -mapMatrix_apply, ← U.map_mul, map_smul',
    -TensorProduct.algebraMap_apply, smul_mulVec]
/-- Hodge–Tate projectors of lattices with jumps in `[0, n]` have bounded denominators (`𝒥` maps `Γ`
to `Gp p` with open image). Some `t ∈ ℂ_p`, depending on `Γ`, `n`, `w` only, serves each crystalline
`T` with jumps in `[0, n]`, basis `ε`, `x ∈ T`. Some `z` has (a) `‖z s‖ ≤ 1` and (b) for potentially
crystalline `r` and `ℤ_p`-linear `u` with `u (g y) = r g * u y`, `u x = 1`,
`t * ∑ s, z s * γ (trace (u (ε s)))` is the multiplicity of the jump `w` of `r` at `γ`. -/
lemma New.Period.exists_uniform_trace_sum_eq_jump {p : ℕ} [ThePrime p] (Γ : Type) [Group Γ]
    [𝒥 : OverGp Γ p] (n : ℕ) (w : ℤ) :
    ∃ t : ℂ_[p],
      ∀ {T ι : Type} [AddCommGroup T] [Module ℤ_[p] T] [Fintype ι] (ε : Basis ι ℤ_[p] T)
        {ρ : Representation ℤ_[p] Γ T} (x : T),
      IsCrystallineUpTo (R := ℤ_[p]) n ρ →
      ∃ z : ι → ℂ_[p],
        (∀ s : ι, ‖z s‖ ≤ 1) ∧
        ∀ (γ : PadicAlgCl p →ₐ[ℤ_[p]] ℂ_[p]) (r : PadicRep Γ p)
          (u : T →ₗ[ℤ_[p]] Matrix r.Index r.Index (PadicAlgCl p)),
          (∀ (g : Γ) (y : T), u (ρ g y) = (r.rep g).val * u y) →
          u x = 1 →
          IsPotentiallyCrystalline (matrixRep r.rep) →
          t * ∑ s : ι, z s * γ (u (ε s)).trace = jump (matrixRep r.rep) γ w := by
  classical
  -- In a Hodge frame `W` of `T` take the projector `W * jumpProjector w k * W⁻¹` onto the jump
  -- `w`. The vector `z` it makes of `x` has denominators bounded by one `κ`, and `u` takes `θ z`
  -- to the projector onto the jump `w` of `r`, whose trace is the multiplicity.
  -- `e` is a uniform denominator: every such `T` has a period matrix `U` over `Amax`, with
  -- invariant columns, and `U'` with `U * U' = e • 1`.
  obtain ⟨e, he_unit, h_unif⟩ := Lift.uniform_period_bound Γ n
  -- `R` contains the integers of `localFieldOf Γ`, a finite extension of `ℚ_p`.
  obtain ⟨R, hR⟩ : ∃ R : CoeffRing p,
      ∀ x ∈ localFieldOf Γ, ‖x‖ ≤ 1 → x ∈ (R : Subalgebra ℤ_[p] (PadicAlgCl p)) := by
    obtain ⟨s, hs⟩ := (localFieldOf Γ).essFiniteType_iff.mp inferInstance
    rw [← hs]
    exact CoeffRing.exists_mem_of_mem_adjoin s
  have he_ne_zero : algebraMap Amax BdR e ≠ 0 :=
    (algebraMap_apply _ Bmax BdR e).trans_ne (he_unit.map _).ne_zero
  -- `O` is the map `Amax ⊗ R → BdRPlus`; `κ` bounds the denominators of preimages under `O`.
  set O : TensorProduct ℤ_[p] Amax R →ₐ[Amax] BdRPlus :=
    (toAlgHom ℤ_[p] R BdRPlus).liftEquiv ℤ_[p] Amax R BdRPlus
  obtain ⟨κ, hκ, h_bound⟩ := exists_norm_thetaBdR_mul_le R he_ne_zero
  refine ⟨(thetaBdR κ)⁻¹, fun {T ι} _ _ _ ε ρ x h_crys ↦ ?_⟩
  obtain ⟨U, U', hUU', hU⟩ := (h_unif ε h_crys).right
  -- The invariant matrix `U` becomes a Hodge frame: `U * Y = hodgeMatrix W k = W * diag (t ^ k)`,
  -- with `W` invertible over `BdRPlus` and `Y` algebraic, fixed, integral, of determinant `1`.
  have hU_unit : IsUnit ((algebraMap Amax BdR).mapMatrix U) :=
    isUnit_of_mul_isUnit_left (y := (algebraMap Amax BdR).mapMatrix U')
      (by simp [← Matrix.map_mul, hUU', smul_eq_diagonal_mul, he_ne_zero, Pi.isUnit_iff])
  -- `U` is invariant over `BdR` too, being invariant over `Amax` (`hU`).
  obtain ⟨⟨Y, hY_det⟩, W, k, hF⟩ := exists_isHodgeFrame Γ le_top hU_unit fun g ↦ by
    simpa [comp_def, ← algebraMap_apply] using congrArg (algebraMap Amax BdR).mapMatrix (hU g)
  obtain ⟨W, rfl⟩ := hF.isUnit
  -- `Y` is fixed and integral, so its entries lie in `R`.
  have hY_mem (i l : ι) : Y i l ∈ (R : Subalgebra ℤ_[p] (PadicAlgCl p)) :=
    hR _ (by simpa using fun g ↦ congrFun₂ (hF.eventually_map_eq g) i l) (hF.norm_le_one i l)
  obtain ⟨y, hy⟩ : ∃ y : Matrix ι ι (TensorProduct ℤ_[p] Amax R),
      O.mapMatrix y = (algebraMap (PadicAlgCl p) BdRPlus).mapMatrix Y :=
    ⟨of fun i l ↦ 1 ⊗ₜ ⟨Y i l, hY_mem i l⟩, by ext; simp [O]⟩
  -- `jumpProjector w k` keeps the coordinates of weight `w`; `z` is the projection of `x`.
  let z : ι → BdRPlus := ↑W *ᵥ jumpProjector w k *ᵥ ↑W⁻¹ *ᵥ (↑) ∘ ε.repr x
  refine ⟨fun s ↦ thetaBdR (κ * z s), fun s ↦ ?_, fun γ r u hu hx h_pcr ↦ ?_⟩
  · -- (a) `e • z s` is the image under `O` of an element of `Amax ⊗ R`, so `κ` bounds it.
    exact h_bound (map_mulVec_apply_eq_smul_of_isHodgeFrame ε x w O hUU' hY_det hF hy s)
  · -- (b) Cancel `κ`; the remaining sum is the multiplicity.
    simp only [map_mul, mul_assoc, ← Finset.mul_sum, inv_mul_cancel_left₀ hκ]
    exact sum_thetaBdR_mul_trace_eq_jump_of_isHodgeFrame ε x w hF rfl γ r u hu hx h_pcr

end HodgeTateProjectors

/-!
## Goodness, jumps and killing polynomials at limits of traces

The conditions are `New.GaloisRep.IsGoodAt` (unramified off ℓ, crystalline above ℓ),
`New.GaloisRep.JumpsRelAt` (a relation on the multiplicities of the Hodge–Tate jumps) and
`New.GaloisRep.PolyKillsAt` (a polynomial kills a given element). Off ℓ these are linear relations
in the group ring, which pass to the limit because the trace form is non-degenerate
(`New.IsTraceNondeg`). Above ℓ one first bounds all jumps, so that the periods have bounded
denominators, and then reduces to such relations.
-/

section LocalLimit

open Matrix Polynomial MonoidAlgebra Finset Module Metric IsUltrametricDist Submodule Set New.Period
  hodgeTateMaps TensorProduct Function LinearMap Amax Filter

/-- If the combinations of the traces of the `ρ η x` with coefficients `a η x` tend uniformly on `G`
to `b` times the trace of `r`, they do so uniformly on the group ring `ℤ_ℓ[G]`: for each `ε > 0`,
eventually along `F` the error is at most `ε` at every `y`. Representations act on the group ring
by `groupRingHom`, their linear extension; `⟨r⟩` is `r` as a `PadicRep`. -/
lemma New.GaloisRep.eventually_trace_sub_sum_mem_closedBall {ℓ : ℕ} [ThePrime ℓ] {G m I : Type}
    [Group G] [Fintype m] [DecidableEq m] {r : G →* GL m (PadicAlgCl ℓ)} {ι : I → Type}
    [∀ η : I, Fintype (ι η)] {F : Filter I} {a : (η : I) → ι η → PadicAlgCl ℓ}
    {ρ : (η : I) → ι η → PadicRep G ℓ} {b : PadicAlgCl ℓ}
    (h_conv : TendstoUniformly
      (fun (η : I) (g : G) ↦ ∑ x : ι η, a η x * ((ρ η x).rep g).val.trace)
      (fun g : G ↦ b * (r g).val.trace) F)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ η : I in F, ∀ y : ℤ_[ℓ][G],
      b * (groupRingHom ⟨r⟩ y).trace - ∑ x : ι η, a η x * (groupRingHom (ρ η x) y).trace ∈
        closedBall 0 ε := by
  -- The coefficients of y have norm at most 1, and the norm is ultrametric. (`using!`: the
  -- coefficients act through their coercion to `ℚ̄_ℓ`, which plain `using` does not match.)
  filter_upwards [tendstoUniformly_iff.mp h_conv ε hε] with η hη y
  simpa [lift_apply, Finsupp.sum, mul_sum, univ.sum_comm, smul_sub, smul_sum] using!
    norm_sum_le_of_forall_le_of_nonneg hε.le fun g _ ↦ (norm_smul ..).trans_le
      ((mul_le_of_le_one_left (by simp) (y.coeff g).prop).trans (mem_ball_iff_norm.mp (hη g)).le)

/-- Linear relations pass to the limit. Let `r` have non-degenerate trace form, `F` be a proper
filter, `S` a finite set of indices `l`, and let the traces of the `ρ η x` weighted by `a * c l`
tend uniformly to `b l` times the trace of `r`. If the group ring elements `y θ l` satisfy the
relation with coefficients `c l θ x` in each `ρ θ x`, and their combination with coefficients `b l`
has a value `M` in `r` that does not depend on `θ`, then `M = 0`. -/
lemma New.GaloisRep.matrix_eq_zero_of_relation_of_limit {ℓ : ℕ} [ThePrime ℓ] {G m I : Type}
    [Group G] [Fintype m] [DecidableEq m] {r : G →* GL m (PadicAlgCl ℓ)} {ι : I → Type}
    [∀ η : I, Fintype (ι η)] (F : Filter I) [NeBot F] (hr_nondeg : IsTraceNondeg r)
    (a : (η : I) → ι η → PadicAlgCl ℓ) (ρ : (η : I) → ι η → PadicRep G ℓ) (S : Finset ℕ)
    {b : ℕ → PadicAlgCl ℓ} {c : ℕ → (η : I) → ι η → PadicAlgCl ℓ}
    (h_conv : ∀ l : ℕ, TendstoUniformly
      (fun (η : I) (g : G) ↦ ∑ x : ι η, (a * c l) η x * ((ρ η x).rep g).val.trace)
      (fun g : G ↦ b l * (r g).val.trace) F)
    (y : I → ℕ → ℤ_[ℓ][G])
    (hy_rel : ∀ (θ : I) (x : ι θ), ∑ l ∈ S, c l θ x • groupRingHom (ρ θ x) (y θ l) = 0)
    {M : Matrix m m (PadicAlgCl ℓ)}
    (hM_eq : ∀ θ : I, (∑ l ∈ S, b l • groupRingHom ⟨r⟩ (y θ l) : Matrix m m (PadicAlgCl ℓ)) = M) :
    M = 0 := by
  obtain ⟨t₀⟩ : Nonempty I := F.nonempty_of_neBot
  refine hr_nondeg _ ?_ fun g ↦ ?_
  · simp (maxDischargeDepth := 9) [← hM_eq t₀, lift_apply, Finsupp.sum, sum_mem, smul_of_tower_mem,
      mem_span_of_mem]
  -- The trace of M r g is a sum of errors that tend to 0.
  let err (θ : I) (l : ℕ) : PadicAlgCl ℓ := b l * (groupRingHom ⟨r⟩ (y θ l * .single g 1)).trace -
    ∑ x, (a * c l) θ x * (groupRingHom (ρ θ x) (y θ l * .single g 1)).trace
  have h_lim : Tendsto (fun θ ↦ ∑ l ∈ S, err θ l) F (nhds (∑ l ∈ S, 0)) :=
    tendsto_finsetSum S fun l _ ↦ nhds_basis_closedBall.tendsto_right_iff.mpr fun ε hε ↦
      (eventually_trace_sub_sum_mem_closedBall (h_conv l) hε).mono fun θ h ↦ h _
  have h_const (θ : I) : ∑ l ∈ S, err θ l = (M * r g).trace := by
    -- Each `ρ θ x` satisfies the relation, so the sum of its error terms vanishes.
    have h_rel : ∑ x : ι θ, a θ x *
        ((∑ l ∈ S, c l θ x • groupRingHom (ρ θ x) (y θ l)) * ((ρ θ x).rep g).val).trace = 0 := by
      simp [hy_rel]
    simpa [err, ← hM_eq θ, sum_mul, mul_sum, mul_assoc, S.sum_comm] using h_rel
  exact (tendsto_const_nhds_iff.mp (h_lim.congr h_const)).trans sum_const_zero

/-- Let the maps `x ↦ u o x *ᵥ v` intertwine a lattice `lat` with potentially crystalline `σ o`,
let `(toGp s, k)` be a Weil pair (`s` acts on residues as `x ↦ x ^ (1 / ℓ ^ k)`), and let `y` lie in
the `Amax`-span of the invariant periods of `lat` (elements of `Amax ⊗ T` fixed by `Γ`). Then one
`y' ∈ Amax ⊗ T` represents `linearFrob` of `s` on the image of `y` in every `σ o`; here
`periodTensorMap Amax Bmax f` is the map `a ⊗ x ↦ a ⊗ f x` into `Bmax ⊗ _`. -/
lemma New.GaloisRep.exists_periodTensorMap_eq_linearFrob {ℓ : ℕ} [ThePrime ℓ] {Γ T κ : Type}
    [Group Γ] [OverGp Γ ℓ] [AddCommGroup T] [Module ℤ_[ℓ] T] {n : κ → Type} [∀ o : κ, Fintype (n o)]
    {lat : Representation ℤ_[ℓ] Γ T}
    {σ : (o : κ) → Representation (PadicAlgCl ℓ) Γ (n o → PadicAlgCl ℓ)}
    (hσ : ∀ o : κ, IsPotentiallyCrystalline (σ o))
    {u : (o : κ) → T →ₗ[ℤ_[ℓ]] Matrix (n o) (n o) (PadicAlgCl ℓ)}
    (h_equiv : ∀ (o : κ) (v : n o → PadicAlgCl ℓ) (g : Γ) (x : T),
      applyVec (u o) v (lat g x) = σ o g (applyVec (u o) v x))
    {s : Γ} {k : ℕ} (hs : IsWeilPair (toGp s) k) {y : Amax ⊗[ℤ_[ℓ]] T}
    (hy : y ∈ span Amax (fixedPeriods lat Amax ⊤)) :
    ∃ y' : Amax ⊗[ℤ_[ℓ]] T, ∀ (o : κ) (v : n o → PadicAlgCl ℓ),
      periodTensorMap Amax Bmax (applyVec (u o) v) y' =
        linearFrob (σ o) s k (periodTensorMap Amax Bmax (applyVec (u o) v) y) := by
  -- On invariant elements `linearFrob` acts by φ ^ k s on periods and by s on `T`, which keeps
  -- `Amax ⊗ T`; extend by linearity.
  induction hy using span_induction with
  | mem y hy =>
    exact ⟨_, fun o v ↦ .symm <| (linearFrob_apply (hσ o) hs
      (fixedPeriods.periodTensorMap_mem (.of_forall (h_equiv o v))
        ((nearOne _).univ_mem' hy))).trans
      (tensorAction_periodTensorMap (h_equiv o v _) ..)⟩
  | zero => exact ⟨0, by simp⟩
  | add y₁ y₂ _ _ h₁ h₂ =>
    obtain ⟨⟨y₁', h₁'⟩, ⟨y₂', h₂'⟩⟩ := And.intro h₁ h₂
    exact ⟨y₁' + y₂', fun o v ↦ by simp [h₁', h₂']⟩
  | smul t y₀ _ h =>
    obtain ⟨y₀', h'⟩ := h
    exact ⟨t • y₀', fun o v ↦ by simp [h', map_smul_of_tower]⟩

namespace New.GaloisRep

variable {ℓ : ℕ} [ThePrime ℓ] {E m I : Type} [Field E] [EmbeddedNumberField E] [Fintype m]
  [DecidableEq m] {ι : I → Type} [∀ η : I, Fintype (ι η)]

section Chart

/-- The map `g ↦ χ(g) ^ (-d) · [g]` from the decomposition group at `A` to the group ring, where `χ`
is the cyclotomic character. A representation read along it is its Tate twist by `χ ^ (-d)`. -/
noncomputable def tateTwistHom (A : ClosurePlace) [PadicPlaceEmbedding E A ℓ] (d : ℕ) :
    decompGroup Gal(Ω/E) A →* ℤ_[ℓ][Gal(Ω/E)] :=
  singleHom.comp (((Units.coeHom ℤ_[ℓ]).comp (χ⁻¹ ^ d)).prod (decompGroup Gal(Ω/E) A).subtype)

variable {A : ClosurePlace} [PadicPlaceEmbedding E A ℓ]

/-- Read along `tateTwistHom A d`, an element `g` acts as `χ(g) ^ (-d)` times its action in `σ`. -/
lemma viaGroupRing_tateTwistHom {d : ℕ} {σ : PadicRep Gal(Ω/E) ℓ} (g : decompGroup Gal(Ω/E) A)
    (x : σ.Index → PadicAlgCl ℓ) :
    viaGroupRing (tateTwistHom A d) σ g x = (χ g ^ (-d : ℤ)).val • decompRep σ.rep A g x := by
  simp [tateTwistHom]

/-- A continuous representation `σ` has finitely many Hodge–Tate jumps at `A`: the integers `k`
of nonzero multiplicity at some `γ : ℚ̄_ℓ → ℂ_ℓ`, for the restriction of `σ` to the decomposition
group at `A`, form a finite set. -/
lemma finite_setOf_jump_ne_zero {σ : PadicRep Gal(Ω/E) ℓ} (hσ : Continuous σ.rep) :
    {k : ℤ | ∃ γ : PadicAlgCl ℓ →ₐ[ℤ_[ℓ]] ℂ_[ℓ], jump (decompRep σ.rep A) γ k ≠ 0}.Finite := by
  -- The image `L` of the group ring is a lattice, so its jumps are bounded. A jump of `σ` is a jump
  -- of `L`, by pulling back along y ↦ y v.
  let Δ : Subgroup Gal(Ω/E) := decompGroup Gal(Ω/E) A
  obtain ⟨L, q, u, _, _, -, hu, -⟩ :=
    exists_finite_groupRing_quotient Δ (τ := fun _ : Unit ↦ σ) fun _ ↦ hσ
  obtain ⟨n, h_bound⟩ := exists_jump_bound (γ := Algebra.ofId ℤ_[ℓ] ℂ_[ℓ])
    (ρ := actionRep _ L (q.toMonoidHom.comp (.comp (of ℤ_[ℓ] Gal(Ω/E)) Δ.subtype)))
  refine (finite_Icc (-(n : ℤ)) n).subset fun k ⟨γ, hk⟩ ↦
    h_bound k fun h_jump_zero ↦ hk <| jump_eq_zero_iff.mpr fun f hf ↦ f.ext fun v ↦ ?_
  -- A form `f` of weight `k` for `σ` gives, for each vector `v`, the form `y ↦ f (y v)` of
  -- weight `k` for `L`; that one is zero, so `f v = 0`.
  have h_pull := jump_eq_zero_iff.mp h_jump_zero _ (pull (asSemilinear (applyVec (u ())) (v, γ))
    (by simp [hu, asSemilinear]) ⟨_, hf⟩).prop
  -- At `y = 1` the pulled-back form is `f v`; `simp` does not unfold `pull`.
  exact (congrArg f (by simp [asSemilinear])).trans (LinearMap.congr_fun h_pull 1)

/-- If the twist of `σ` by `χ ^ (-d)` is crystalline and every jump of `σ` at `A` has absolute
value at most `d`, then the twist is crystalline with jumps in `[0, 2 d]`: the twist adds `d` to
every jump. -/
lemma isCrystallineUpTo_tateTwistHom {d : ℕ} {σ : PadicRep Gal(Ω/E) ℓ}
    (h_twist : IsCrystalline (viaGroupRing (tateTwistHom A d) σ))
    (h_bound : ∀ (γ : PadicAlgCl ℓ →ₐ[ℤ_[ℓ]] ℂ_[ℓ]) (k : ℤ),
      jump (decompRep σ.rep A) γ k ≠ 0 → k.natAbs ≤ d) :
    IsCrystallineUpTo (2 * d) (viaGroupRing (tateTwistHom A d) σ) := by
  refine ⟨h_twist, fun γ k hk ↦ ?_⟩
  have h_shift : (k - d).natAbs ≤ d := h_bound γ _ <| by
    rw [← jump_twist_cyclotomicGp _ (viaGroupRing_tateTwistHom (d := d))]
    simpa using hk
  omega

end Chart

/-- The trace of `r` is the uniform limit along `F` of the sums ∑ᵢ a η i · tr ρ η i, where the
`ρ η i` are unramified or crystalline at `A`, and are finitely many or share their jumps. -/
structure IsTraceLimit [PadicIso ℓ] (r : GalRep ℓ E m) (A : ClosurePlace) (F : Filter I)
    (a : (η : I) → ι η → PadicAlgCl ℓ) (ρ : (η : I) → ι η → PadicRep Gal(Ω/E) ℓ) : Prop where
  /-- The limit is continuous. -/
  continuous_limit : Continuous r
  /-- The trace form of the limit is non-degenerate. -/
  isTraceNondeg : IsTraceNondeg r
  /-- Each `ρ η i` is continuous. -/
  continuous_approx (η : I) (i : ι η) : Continuous (ρ η i).rep
  /-- Each `ρ η i` is unramified or crystalline at `A`. -/
  isGoodAt_approx (η : I) (i : ι η) : IsGoodAt (ρ η i).rep A
  /-- There are finitely many `η`, or all `ρ η i` have the same jumps. -/
  finite_or_hasJumpsAt : Finite I ∨
    ∃ J : (E →+* ℂ) → Multiset ℤ, ∀ (η : I) (i : ι η), HasJumpsAt (ρ η i).rep A J
  /-- The combinations of traces converge uniformly along `F` to the trace of `r`. -/
  tendstoUniformly_trace :
    TendstoUniformly (fun (η : I) (g : Gal(Ω/E)) ↦ ∑ i : ι η, a η i * ((ρ η i).rep g).val.trace)
      (fun g : Gal(Ω/E) ↦ (r g).val.trace) F

namespace IsTraceLimit

variable [PadicIso ℓ] {r : GalRep ℓ E m} {A : ClosurePlace} {F : Filter I}
  {a : (η : I) → ι η → PadicAlgCl ℓ} {ρ : (η : I) → ι η → PadicRep Gal(Ω/E) ℓ}

/-- `Amax` has a `p`-adic basis, for the ideal of `ℤ_p` generated by `p`. -/
lemma _root_.New.Period.nonempty_adicBasis_span_natCast (p : ℕ) [ThePrime p] :
    Nonempty (Lift.AdicBasis (Ideal.span {(p : ℤ_[p])}) Amax) := by
  rw [← PadicInt.maximalIdeal_eq_span_p]
  exact nonempty_adicBasis _ PadicInt.maximalIdeal_eq_span_p

/-- The convergence of traces is uniform on the group ring: for every `ε > 0`, eventually along
`F`, the trace of every `y ∈ ℤ_ℓ[Gal(Ω/E)]` on `r` differs by at most `ε` from the combination
∑ᵢ a η i · (trace of `y` on `ρ η i`). -/
lemma eventually_norm_trace_sub_le (h : IsTraceLimit r A F a ρ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ η : I in F, ∀ y : ℤ_[ℓ][Gal(Ω/E)],
      ‖(groupRingHom ⟨r⟩ y).trace - ∑ i : ι η, a η i * (groupRingHom (ρ η i) y).trace‖ ≤ ε := by
  simpa using eventually_trace_sub_sum_mem_closedBall (b := 1) (r := r) (ρ := ρ)
    (by simpa using h.tendstoUniformly_trace) hε

/-- In a chart at `A` (an embedding `PadicPlaceEmbedding E A ℓ`), the integers that occur as jumps
of some `ρ η i` at some `γ : ℚ̄_ℓ → ℂ_ℓ` form a finite set. -/
lemma finite_setOf_jump_approx_ne_zero (h : IsTraceLimit r A F a ρ) [PadicPlaceEmbedding E A ℓ] :
    {k : ℤ | ∃ (η : I) (i : ι η) (γ : PadicAlgCl ℓ →ₐ[ℤ_[ℓ]] ℂ_[ℓ]),
      jump (decompRep (ρ η i).rep A) γ k ≠ 0}.Finite := by
  rcases h.finite_or_hasJumpsAt with h_fin | ⟨J, h_same⟩
  · simpa only [ofPred_exists] using finite_iUnion fun η ↦
      finite_iUnion fun i ↦ finite_setOf_jump_ne_zero (h.continuous_approx η i)
  · -- Every `γ : Q̄_ℓ → ℂ_ℓ` is an element `g γ` of `Gp ℓ` followed by the inclusion.
    choose g hg using exists_gp_eq_algHom (p := ℓ)
    refine (finite_iUnion fun τ ↦ (J τ).finite_toSet).subset ?_
    rintro k ⟨η, i, γ, hk⟩
    exact mem_iUnion.mpr ⟨_, Multiset.count_ne_zero.mp ((h_same η i (hg γ) k).trans_ne hk)⟩

variable [NeBot F]

/-- In a chart at `A`, one Tate twist, by `χ ^ (-d)` (`tateTwistHom A d`), makes `r` and all
`ρ η i` crystalline with jumps in `[0, 2 d]` (`IsCrystallineUpTo (2 * d)`). -/
lemma exists_isCrystallineUpTo_tateTwistHom (h : IsTraceLimit r A F a ρ)
    [PadicPlaceEmbedding E A ℓ] :
    ∃ d : ℕ, IsCrystallineUpTo (2 * d) (viaGroupRing (tateTwistHom A d) ⟨r⟩) ∧
      ∀ (η : I) (i : ι η), IsCrystallineUpTo (2 * d) (viaGroupRing (tateTwistHom A d) (ρ η i)) := by
  -- Take `d` above all jumps. The twist of `r` is crystalline as a limit.
  have h_fin : ({k : ℤ | ∃ γ : PadicAlgCl ℓ →ₐ[ℤ_[ℓ]] ℂ_[ℓ], jump (decompRep r A) γ k ≠ 0} ∪
      {k : ℤ | ∃ (η : I) (i : ι η) (γ : PadicAlgCl ℓ →ₐ[ℤ_[ℓ]] ℂ_[ℓ]),
        jump (decompRep (ρ η i).rep A) γ k ≠ 0}).Finite :=
    (finite_setOf_jump_ne_zero (A := A) (σ := ⟨r⟩) h.continuous_limit).union
      h.finite_setOf_jump_approx_ne_zero
  obtain ⟨d, hd_bound⟩ := (h_fin.image Int.natAbs).bddAbove
  have h_approx (η : I) (i : ι η) :
      IsCrystallineUpTo (2 * d) (viaGroupRing (tateTwistHom A d) (ρ η i)) := by
    obtain ⟨-, h_crys⟩ := h.isGoodAt_approx η i
    exact isCrystallineUpTo_tateTwistHom (h_crys.tate_twist _ viaGroupRing_tateTwistHom)
      fun γ k hk ↦ hd_bound ⟨k, .inr ⟨η, i, γ, hk⟩, rfl⟩
  -- for each `ε > 0` there is an `η` such that the trace on `r` of every `y` killed by all `ρ η i`
  -- has norm at most `ε`
  have h_close : ∀ ε > (0 : ℝ), ∃ η : I, ∀ y : ℤ_[ℓ][Gal(Ω/E)],
      (∀ i : ι η, groupRingHom (ρ η i) y = 0) → ‖(groupRingHom ⟨r⟩ y).trace‖ ≤ ε := fun ε hε ↦
    (h.eventually_norm_trace_sub_le hε).exists.imp fun η hη y hy ↦ by simpa [hy] using hη y
  have h_limit : IsCrystalline (viaGroupRing (tateTwistHom A d) ⟨r⟩) :=
    isCrystalline_of_trace_limit _ h.continuous_limit h.isTraceNondeg h_approx h.continuous_approx
      h_close
  exact ⟨d, isCrystallineUpTo_tateTwistHom h_limit fun γ k hk ↦ hd_bound ⟨k, .inl ⟨γ, hk⟩, rfl⟩,
    h_approx⟩

/-- In a chart at `A` (an embedding `PadicPlaceEmbedding E A ℓ`), the restriction of `r` to the
decomposition group at `A` is crystalline. -/
lemma isCrystalline (h : IsTraceLimit r A F a ρ) [PadicPlaceEmbedding E A ℓ] :
    IsCrystalline (decompRep r A) := by
  obtain ⟨d, ⟨h_twist_crys, -⟩, -⟩ := h.exists_isCrystallineUpTo_tateTwistHom
  -- the twist by `χ ^ d` undoes `tateTwistHom A d`
  have h_untwist (g : decompGroup Gal(Ω/E) A) (x : m → PadicAlgCl ℓ) :
      decompRep r A g x = (χ g ^ (d : ℤ)).val • viaGroupRing (tateTwistHom A d) ⟨r⟩ g x := by
    rw [viaGroupRing_tateTwistHom]
    simp [smul_smul, ← mul_pow]
  exact h_twist_crys.tate_twist d h_untwist

/-- A limit of traces of representations that are unramified or crystalline at `A` is unramified or
crystalline at `A`. -/
theorem isGoodAt (h : IsTraceLimit r A F a ρ) : IsGoodAt r A := by
  refine ⟨fun hA s hs ↦ ?_, h.isCrystalline⟩
  -- Off ℓ, the relation s - 1 = 0 on inertia passes to the limit.
  have h_unram (θ : I) (x : ι θ) : (ρ θ x).rep s = 1 := (h.isGoodAt_approx θ x).left hA s hs
  have h_rel : (r s).val - 1 = 0 :=
    matrix_eq_zero_of_relation_of_limit F h.isTraceNondeg a ρ {0} (b := fun _ ↦ 1)
      (c := fun _ ↦ 1) (fun _ ↦ by simpa using h.tendstoUniformly_trace)
      (fun _ _ ↦ .single s 1 - 1) (by simp [h_unram]) (by simp)
  exact Units.ext (sub_eq_zero.mp h_rel)

/-- Suppose the trace of `r` is the uniform limit along the nontrivial filter `F` of the sums
∑ᵢ a η i · tr (ρ η i), where the `ρ η i` are unramified or crystalline at the place `A` and are
either finitely many or share their jumps (`IsTraceLimit r A F a ρ`). Suppose also that we fix an
embedding of Ω into ℚ̄_ℓ inducing `A`, with a compatible map from the decomposition group to
Gal(ℚ̄_ℓ/ℚ_ℓ) (`PadicPlaceEmbedding E A ℓ`). Then for every `γ` and `w`, the multiplicity of the
Hodge–Tate jump `w` at `γ` of `r` restricted to the decomposition group at `A` is the limit along
`F` of ∑ᵢ a η i · (the multiplicity of `w` at `γ` for the corresponding restriction of `ρ η i`). -/
theorem tendsto_jump (h : IsTraceLimit r A F a ρ) [PadicPlaceEmbedding E A ℓ]
    (γ : PadicAlgCl ℓ →ₐ[ℤ_[ℓ]] ℂ_[ℓ]) (w : ℤ) :
    Tendsto (fun η : I ↦ ∑ i : ι η, a η i * jump (decompRep (ρ η i).rep A) γ w) F
      (nhds (jump (decompRep r A) γ w)) := by
  -- After a common twist the image `L θ` of the group ring in r and the `ρ θ x`, listed as `X θ o`,
  -- is a crystalline lattice. `exists_uniform_trace_sum_eq_jump` reads the multiplicity of w in
  -- `X θ o` as `t * ∑ s, z θ s * γ (trace at y θ s)`, with `t` independent of θ and `‖z θ s‖ ≤ 1`.
  let Δ : Subgroup Gal(Ω/E) := decompGroup Gal(Ω/E) A
  let X (η : I) : Option (ι η) → PadicRep Gal(Ω/E) ℓ := Option.elim' ⟨r⟩ (ρ η)
  obtain ⟨d, h_limit, h_approx⟩ := h.exists_isCrystallineUpTo_tateTwistHom
  have h_in (θ : I) : ∀ o : Option (ι θ),
      IsCrystallineUpTo (2 * d) (viaGroupRing (tateTwistHom A d) (X θ o))
    | none => h_limit
    | some x => h_approx θ x
  have h_cont (η : I) : ∀ o : Option (ι η), Continuous (X η o).rep
    | none => h.continuous_limit
    | some x => h.continuous_approx η x
  choose L q u hL using fun η ↦ exists_finite_groupRing_quotient Δ (τ := X η) (h_cont η)
  have hL_free (η : I) : Free ℤ_[ℓ] (L η) := (hL η).free
  have hL_finite (η : I) : Module.Finite ℤ_[ℓ] (L η) := (hL η).finite
  have hq (η : I) : (⇑(q η)).Surjective := (hL η).surjective
  have hu (η : I) (o : Option (ι η)) (y : ℤ_[ℓ][Gal(Ω/E)]) :
      u η o (q η y) = groupRingHom (X η o) y :=
    (hL η).factors o y
  have h_iso {x : PadicAlgCl ℓ} : ‖γ x‖ = ‖x‖ := by
    obtain ⟨g, hg⟩ := exists_gp_eq_algHom γ
    simp [hg, ← smul_coe_Cp]
  -- In the twist the jump w is w - (-d).
  obtain ⟨t, ht⟩ := exists_uniform_trace_sum_eq_jump Δ (2 * d) (w - -d)
  choose z hz h_proj using fun θ ↦ ht (finBasis ℤ_[ℓ] (L θ)) 1 ((hL θ).isCrystallineUpTo (h_in θ))
  choose y hy using fun θ s ↦ hq θ (finBasis ℤ_[ℓ] _ s)
  let err (θ : I) (s : Fin (finrank ℤ_[ℓ] (L θ))) : PadicAlgCl ℓ :=
    (groupRingHom ⟨r⟩ (y θ s)).trace - ∑ x, a θ x * (groupRingHom (ρ θ x) (y θ s)).trace
  have h_dist (θ : I) : dist (∑ x, a θ x * jump (decompRep (ρ θ x).rep A) γ w)
      (jump (decompRep r A) γ w) = ‖t * ∑ s, z θ s * γ (err θ s)‖ := by
    have h_read (o : Option (ι θ)) :=
      h_proj θ γ ⟨.toHomUnits _⟩ (u θ o) (by simp [hu]) (by simp)
        (h_in θ o).left.isPotentiallyCrystalline
    -- `using!`: `h_read` is stated for `X θ o`, which is `r` or `ρ θ x` only up to unfolding of
    -- instances
    simpa [err, ← hy, hu, mul_sub, mul_sum, sum_comm (γ := ι _), mul_left_comm (γ _),
      dist_eq_norm', ← h_iso, ↓jump_twist_cyclotomicGp _ viaGroupRing_tateTwistHom] using!
      congr(‖$(h_read none) - ∑ x, γ (a θ x) * $(h_read x)‖).symm
  refine Metric.tendsto_nhds.mpr fun ε hε ↦ ?_
  obtain ⟨δ, hδ, hδε⟩ : ∃ δ : ℝ, 0 < δ ∧ ‖t‖ * δ < ε := exists_pos_mul_lt hε ‖t‖
  filter_upwards [h.eventually_norm_trace_sub_le hδ] with θ hθ
  have h_term (s : Fin (finrank ℤ_[ℓ] (L θ))) : ‖z θ s * γ (err θ s)‖ ≤ δ := by
    have h_err : ‖err θ s‖ ≤ δ := hθ (y θ s)
    exact (norm_mul_le_of_le (hz θ s) (h_iso.trans_le h_err)).trans_eq (one_mul δ)
  calc dist (∑ x, a θ x * jump (decompRep (ρ θ x).rep A) γ w) (jump (decompRep r A) γ w)
      = ‖t * ∑ s, z θ s * γ (err θ s)‖ := h_dist θ
    _ ≤ ‖t‖ * δ :=
      norm_mul_le_of_le le_rfl (norm_sum_le_of_forall_le_of_nonneg hδ.le fun s _ ↦ h_term s)
    _ < ε := hδε

/-- Let the jump multiplicities of `ρ η i` be `R'`-related to `J' η i`. Suppose that `n` is
`R`-related to the multiplicity in `J` whenever numbers `x η i` are `R'`-related to the
multiplicities in `J' η i` and ∑ᵢ a η i · x η i tends to `n`. Then the jump multiplicities of `r`
are `R`-related to `J`. -/
theorem jumpsRelAt (h : IsTraceLimit r A F a ρ) {R R' : ℕ → ℕ → Prop} {J : (E →+* ℂ) → Multiset ℤ}
    {J' : (η : I) → ι η → (E →+* ℂ) → Multiset ℤ}
    (h_jump : ∀ (η : I) (i : ι η), JumpsRelAt (ρ η i).rep A R' (J' η i))
    (h_rel : ∀ (τ : E →+* ℂ) (u : ℤ) (x : (η : I) → ι η → ℕ) (n : ℕ),
      (∀ (η : I) (i : ι η), R' ((J' η i τ).count u) (x η i)) →
      Tendsto (fun η : I ↦ ∑ i : ι η, a η i * x η i) F (nhds n) →
      R ((J τ).count u) n) :
    JumpsRelAt r A R J :=
  fun _ γ _ hg u ↦ h_rel _ u _ _ (fun η i ↦ h_jump η i hg u) (h.tendsto_jump γ u)

/-- Relations in the group ring pass to the limit. Let the traces weighted by the coefficients of
the `Q η i` and of `P` converge (`h_coeff`). If the group ring elements `y θ l` satisfy, in each
`ρ θ x`, the relation with the coefficients of `Q θ x`, and their combination with the
coefficients of `P` has in `r` a value `M` that does not depend on `θ`, then `M = 0`. -/
lemma eq_zero_of_relation (h : IsTraceLimit r A F a ρ) {n : ℕ} {P : (PadicAlgCl ℓ)[X]}
    {Q : (η : I) → ι η → (PadicAlgCl ℓ)[X]}
    (h_coeff : ∀ l : ℕ, TendstoUniformly
        (fun (η : I) (g : Gal(Ω/E)) ↦
          ∑ i : ι η, a η i * (Q η i).coeff l * ((ρ η i).rep g).val.trace)
        (fun g : Gal(Ω/E) ↦ P.coeff l * (r g).val.trace) F)
    (y : I → ℕ → ℤ_[ℓ][Gal(Ω/E)])
    (hy_rel : ∀ (θ : I) (x : ι θ),
      ∑ l ∈ range n, (Q θ x).coeff l • groupRingHom (ρ θ x) (y θ l) = 0)
    {M : Matrix m m (PadicAlgCl ℓ)}
    (hM_eq : ∀ θ : I,
      (∑ l ∈ range n, P.coeff l • groupRingHom ⟨r⟩ (y θ l) : Matrix m m (PadicAlgCl ℓ)) = M) :
    M = 0 :=
  matrix_eq_zero_of_relation_of_limit F h.isTraceNondeg a ρ (range n)
    (c := fun l η x ↦ (Q η x).coeff l) h_coeff y hy_rel hM_eq

omit [PadicIso ℓ] in
/-- Untwisting the powers of a Weil element. Let the twist of `σ` by `χ ^ (-d)` be crystalline with
jumps in `[0, 2 d]`, `σ` crystalline at `A`, `(s, k)` a Weil pair, and `Y N ∈ Amax ⊗ T` represent
(`hY`) the linear Frobenius of `s ^ N` (degree `N k`) of the twist on `ℓ ^ (k d (n - N)) δ ⊗ 1`. For
`deg Q < n`, `periodTensorMap` sends `∑ N, lTensor Amax (Q.coeff N • applyVec u v) (Y N)` to
`(δ • (ℓ ^ (k d)) ^ n) • Q(β) (1 ⊗ v)`, `β = linearFrob (decompRep σ.rep A) ⟨s, hs⟩ k`. -/
private lemma periodTensorMap_sum_lTensor_eq [L : PadicPlaceEmbedding E A ℓ] {s : Gal(Ω/E)}
    (hs : s ∈ decompGroup Gal(Ω/E) A) {k d n : ℕ} (hw : IsWeilPair (L.toGp ⟨s, hs⟩) k)
    {σ : PadicRep Gal(Ω/E) ℓ}
    (h_twist : IsCrystallineUpTo (2 * d) (viaGroupRing (tateTwistHom A d) σ))
    (h_crys : IsCrystalline (decompRep σ.rep A)) {T : Type} [Ring T] [Algebra ℤ_[ℓ] T]
    (u : T →ₐ[ℤ_[ℓ]] Matrix σ.Index σ.Index (PadicAlgCl ℓ)) (δ : Amax)
    (Y : ℕ → Amax ⊗[ℤ_[ℓ]] T) (v : σ.Index → PadicAlgCl ℓ)
    (hY : ∀ N : ℕ, periodTensorMap Amax Bmax (applyVec u.toLinearMap v) (Y N) =
      linearFrob (viaGroupRing (tateTwistHom A d) σ) (⟨s, hs⟩ ^ N) (N * k)
        (periodTensorMap Amax Bmax (applyVec u.toLinearMap v)
          ((ℓ ^ (k * d)) ^ (n - N) • δ ⊗ₜ[ℤ_[ℓ]] 1)))
    {Q : (PadicAlgCl ℓ)[X]} (hQ : Q.natDegree < n) :
    periodTensorMap Amax Bmax id (∑ N ∈ range n, lTensor Amax (Q.coeff N • applyVec u v) (Y N)) =
      (δ • (ℓ ^ (k * d) : Bmax) ^ n) • Q.eval₂ (coeffEnd (PadicAlgCl ℓ) (σ.Index → PadicAlgCl ℓ))
        (linearFrob (decompRep σ.rep A) ⟨s, hs⟩ k) (1 ⊗ₜ v) := by
  -- Untwisting gives a factor ℓ ^ (k d N), which completes the exponent n - N to n.
  have h_pow (N : ℕ) : linearFrob (viaGroupRing (tateTwistHom A d) σ) (⟨s, hs⟩ ^ N) (N * k) =
      ((ℓ ^ (k * d) : Bmax) • linearFrob (decompRep σ.rep A) ⟨s, hs⟩ k) ^ N := by
    rw [linearFrob_pow h_twist.left.isPotentiallyCrystalline hw,
      linearFrob_twist_cyclotomicGp h_crys.isPotentiallyCrystalline hw d viaGroupRing_tateTwistHom]
  choose G hG using fun N ↦ (Y N).exists_finset
  -- apply `Q.coeff N` to `hY N`, untwist by `h_pow`, and sum over `N < n`
  have h_sum : ∑ N ∈ range n, coeffEnd (PadicAlgCl ℓ) (σ.Index → PadicAlgCl ℓ) (Q.coeff N)
        (periodTensorMap Amax Bmax (applyVec u.toLinearMap v) (Y N)) =
      ∑ N ∈ range n, coeffEnd (PadicAlgCl ℓ) (σ.Index → PadicAlgCl ℓ) (Q.coeff N)
        ((((ℓ ^ (k * d) : Bmax) • linearFrob (decompRep σ.rep A) ⟨s, hs⟩ k) ^ N)
          ((ℓ ^ (k * d)) ^ (n - N) •
            periodTensorMap Amax Bmax (applyVec u.toLinearMap v) (δ ⊗ₜ[ℤ_[ℓ]] 1))) :=
    Finset.sum_congr rfl fun N _ ↦ by rw [hY N, h_pow N, map_nsmul]
  -- `pow_add` with `mem_range_le` (`N ≤ n`) merges `ℓ ^ (k d N)` and `ℓ ^ (k d (n - N))`
  simpa +contextual [eval₂_eq_sum_range' _ hQ, smul_sum, periodTensorMap, hG, smul_comm _ δ,
    tmul_eq_smul_one_tmul δ, ← Nat.cast_smul_eq_nsmul Bmax, smul_smul, ← pow_add,
    mem_range_le, _root_.smul_pow] using h_sum

omit [PadicIso ℓ] in
/-- Integral representatives. In the setting of `periodTensorMap_sum_lTensor_eq`, let `u ∘ q` be the
action of the group ring on `σ` (`hu`), and let `q (y f N)` be the element that the linear form `f`
reads off `Y N` (`hy`). Write `V` for the space `σ.Index → ℚ̄_ℓ` of `σ`. Then one `M ∈ Amax ⊗ V`
has image `(δ • (ℓ ^ (k d)) ^ n) • Q(β) (1 ⊗ v)` in `Bmax ⊗ V`, and every `f` reads `M` as
`(∑ N < n, Q.coeff N • y f N) *ᵥ v` on `σ`. -/
private lemma exists_periodTensorMap_eq_and_lift_eq [L : PadicPlaceEmbedding E A ℓ] {s : Gal(Ω/E)}
    (hs : s ∈ decompGroup Gal(Ω/E) A) {k d n : ℕ} (hw : IsWeilPair (L.toGp ⟨s, hs⟩) k)
    {σ : PadicRep Gal(Ω/E) ℓ}
    (h_twist : IsCrystallineUpTo (2 * d) (viaGroupRing (tateTwistHom A d) σ))
    (h_crys : IsCrystalline (decompRep σ.rep A)) {T : Type} [Ring T] [Algebra ℤ_[ℓ] T]
    (q : ℤ_[ℓ][Gal(Ω/E)] →ₐ[ℤ_[ℓ]] T) (u : T →ₐ[ℤ_[ℓ]] Matrix σ.Index σ.Index (PadicAlgCl ℓ))
    (hu : ∀ z : ℤ_[ℓ][Gal(Ω/E)], u (q z) = groupRingHom σ z) (δ : Amax) (Y : ℕ → Amax ⊗[ℤ_[ℓ]] T)
    (hY : ∀ (N : ℕ) (v : σ.Index → PadicAlgCl ℓ),
      periodTensorMap Amax Bmax (applyVec u.toLinearMap v) (Y N) =
        linearFrob (viaGroupRing (tateTwistHom A d) σ) (⟨s, hs⟩ ^ N) (N * k)
          (periodTensorMap Amax Bmax (applyVec u.toLinearMap v)
            ((ℓ ^ (k * d)) ^ (n - N) • δ ⊗ₜ[ℤ_[ℓ]] 1)))
    (y : (Amax →ₗ[ℤ_[ℓ]] ℤ_[ℓ]) → ℕ → ℤ_[ℓ][Gal(Ω/E)])
    (hy : ∀ (f : Amax →ₗ[ℤ_[ℓ]] ℤ_[ℓ]) (N : ℕ), q (y f N) = lift (lsmul ℤ_[ℓ] T ∘ₗ f) (Y N))
    {Q : (PadicAlgCl ℓ)[X]} (hQ : Q.natDegree < n) (v : σ.Index → PadicAlgCl ℓ) :
    ∃ M : Amax ⊗[ℤ_[ℓ]] (σ.Index → PadicAlgCl ℓ),
      periodTensorMap Amax Bmax id M =
        (δ • (ℓ ^ (k * d) : Bmax) ^ n) • Q.eval₂ (coeffEnd (PadicAlgCl ℓ) (σ.Index → PadicAlgCl ℓ))
          (linearFrob (decompRep σ.rep A) ⟨s, hs⟩ k) (1 ⊗ₜ v) ∧
      ∀ f : Amax →ₗ[ℤ_[ℓ]] ℤ_[ℓ], lift (lsmul ℤ_[ℓ] (σ.Index → PadicAlgCl ℓ) ∘ₗ f) M =
        (∑ N ∈ range n, Q.coeff N • groupRingHom σ (y f N)) *ᵥ v := by
  refine ⟨∑ N ∈ range n, lTensor Amax (Q.coeff N • applyVec u v) (Y N), ?_, fun f ↦ ?_⟩
  · exact periodTensorMap_sum_lTensor_eq hs hw h_twist h_crys u δ Y v (fun N ↦ hY N v) hQ
  · choose G hG using fun N ↦ (Y N).exists_finset
    simp [← hu, hy, hG, sum_mulVec, smul_mulVec, smul_sum, smul_comm (Q.coeff _)]

/-- The case of `polyKillsAt` at a place `A` above `ℓ`, given by an embedding `L` of Ω in ℚ̄_ℓ.
Assume the trace of `r` is the uniform limit along `F` of ∑ᵢ `a η i`·tr `ρ η i` (`h`). Let `Q η i`
kill `s` on `ρ η i`, let all degrees be below `n`, and let the traces also converge when weighted by
each coefficient of `Q η i` and of `P` (`h_coeff`). If `(s, k)` is a Weil pair through `L` (`s⁻¹` is
a Frobenius for `ℓ ^ k`), then the restriction of `r` to the decomposition group is potentially
crystalline and `P` kills its linearized Frobenius in degree `k` (`IsKilledBy`). -/
theorem isKilledBy (h : IsTraceLimit r A F a ρ) [L : PadicPlaceEmbedding E A ℓ] {s : Gal(Ω/E)}
    (hs : s ∈ decompGroup Gal(Ω/E) A) {k n : ℕ} {P : (PadicAlgCl ℓ)[X]}
    {Q : (η : I) → ι η → (PadicAlgCl ℓ)[X]} (hP : P.natDegree < n)
    (hQ : ∀ (η : I) (i : ι η), (Q η i).natDegree < n)
    (h_kill : ∀ (η : I) (i : ι η), PolyKillsAt (ρ η i).rep A s (Q η i))
    (h_coeff : ∀ l : ℕ, TendstoUniformly
        (fun (η : I) (g : Gal(Ω/E)) ↦
          ∑ i : ι η, a η i * (Q η i).coeff l * ((ρ η i).rep g).val.trace)
        (fun g : Gal(Ω/E) ↦ P.coeff l * (r g).val.trace) F)
    (hw : IsWeilPair (L.toGp ⟨s, hs⟩) k) :
    IsKilledBy (decompRep r A) ⟨s, hs⟩ k P := by
  -- The powers of the Weil element have bounded denominators on the twisted lattices `T θ`, and
  -- linear forms on `Amax` turn relations between them into group ring relations.
  refine ⟨h.isCrystalline.isPotentiallyCrystalline, (isBaseChange ..).algHom_ext _ _ fun v ↦ ?_⟩
  obtain ⟨t₀⟩ : Nonempty I := F.nonempty_of_neBot
  let Δ : Subgroup Gal(Ω/E) := decompGroup Gal(Ω/E) A
  let X (η : I) : Option (ι η) → PadicRep Gal(Ω/E) ℓ := Option.elim' ⟨r⟩ (ρ η)
  obtain ⟨d, h_limit, h_approx⟩ := h.exists_isCrystallineUpTo_tateTwistHom
  let α : decompGroup Gal(Ω/E) A →* ℤ_[ℓ][Gal(Ω/E)] := tateTwistHom A d
  have h_in (θ : I) (o : Option (ι θ)) : IsCrystallineUpTo (2 * d) (viaGroupRing α (X θ o)) :=
    o.rec h_limit (h_approx θ)
  have h_crys (θ : I) (o : Option (ι θ)) : IsCrystalline (decompRep (X θ o).rep A) :=
    o.rec h.isCrystalline fun x ↦ (h.isGoodAt_approx θ x).right
  have h_cont (η : I) (o : Option (ι η)) : Continuous (X η o).rep :=
    o.rec h.continuous_limit (h.continuous_approx η)
  -- The lattice `T θ` is the image of the group ring in r and the `ρ θ x`, listed as `X θ o`.
  choose T q u hT using fun η ↦ exists_finite_groupRing_quotient Δ (τ := X η) (h_cont η)
  have hT_free (η : I) : Free ℤ_[ℓ] (T η) := (hT η).free
  have hT_finite (η : I) : Module.Finite ℤ_[ℓ] (T η) := (hT η).finite
  have hq (η : I) : (⇑(q η)).Surjective := (hT η).surjective
  have hu (η : I) (o : Option (ι η)) (z : ℤ_[ℓ][Gal(Ω/E)]) :
      u η o (q η z) = groupRingHom (X η o) z :=
    (hT η).factors o z
  -- `δ : Amax` is a unit in `Bmax`, and `δ ⊗ t` lies in the span of the invariants for every
  -- crystalline lattice with jumps in [0, 2 d]; `c` is an ℓ-adic basis of `Amax`.
  obtain ⟨δ, hδ, h_unif⟩ := Lift.uniform_period_bound Δ (2 * d)
  obtain ⟨c⟩ := nonempty_adicBasis_span_natCast ℓ
  have h_span (θ : I) (N : ℕ) : (ℓ ^ (k * d)) ^ (n - N) • δ ⊗ₜ[ℤ_[ℓ]] (1 : T θ) ∈
      span Amax (fixedPeriods (actionRep ℤ_[ℓ] (T θ) ((q θ).toMonoidHom.comp α)) Amax ⊤) :=
    nsmul_mem ((h_unif (finBasis ℤ_[ℓ] (T θ)) ((hT θ).isCrystallineUpTo (h_in θ))).left 1) _
  -- `frobPow θ N` represents `linearFrob` of s ^ N on the element of `h_span`.
  choose frobPow h_frobPow using fun θ N ↦ exists_periodTensorMap_eq_linearFrob
    (fun o ↦ (h_in θ o).left.isPotentiallyCrystalline) (u := fun o ↦ (u θ o).toLinearMap)
    (by simp [hu]) (hw.pow N) (h_span θ N)
  -- The group ring elements that a linear form f reads off `frobPow θ N`.
  let relElt (f : Amax →ₗ[ℤ_[ℓ]] ℤ_[ℓ]) (θ : I) (N : ℕ) : ℤ_[ℓ][Gal(Ω/E)] :=
    surjInv (hq θ) (lift (lsmul ℤ_[ℓ] (T θ) ∘ₗ f) (frobPow θ N))
  -- δ ℓ ^ (k d n) Q' (β) (1 ⊗ v) is the image of some `M θ o hQ' v ∈ Amax ⊗ _` (`hM`), and
  -- `h_read` says how each f reads that element as a relation in the `relElt f θ N`.
  have h_int (θ : I) (o : Option (ι θ)) {Q' : (PadicAlgCl ℓ)[X]} (hQ' : Q'.natDegree < n)
      (v : (X θ o).Index → PadicAlgCl ℓ) :=
    exists_periodTensorMap_eq_and_lift_eq hs hw (h_in θ o) (h_crys θ o) (q θ) (u θ o) (hu θ o) δ
      (frobPow θ) (fun N v ↦ h_frobPow θ N o v) (fun f N ↦ relElt f θ N)
      (fun f N ↦ surjInv_eq (hq θ) _) hQ' v
  choose M hM h_read using h_int
  have h_zero (f : Amax →ₗ[ℤ_[ℓ]] ℤ_[ℓ]) :
      ∑ N ∈ range n, P.coeff N • groupRingHom ⟨r⟩ (relElt f t₀ N) = 0 := by
    refine h.eq_zero_of_relation (n := n) h_coeff (relElt f)
      (fun θ x ↦ ext_iff_mulVec.mpr fun v ↦ ?_) fun θ ↦ ext_iff_mulVec.mpr fun v ↦ ?_
    · -- `Q θ x` kills s on `ρ θ x`.
      have hMx : M θ x (hQ θ x) v = 0 := by
        obtain ⟨-, h_Q_zero⟩ := (h_kill θ x).right hw
        have h_Q : (δ • (ℓ ^ (k * d) : Bmax) ^ n) • (Q θ x).eval₂
            (coeffEnd (PadicAlgCl ℓ) ((ρ θ x).Index → PadicAlgCl ℓ))
            (linearFrob (decompRep (ρ θ x).rep A) ⟨s, hs⟩ k) (1 ⊗ₜ v) = 0 := by
          rw [h_Q_zero, LinearMap.zero_apply, smul_zero]
        refine periodTensorMap_injective ((hM θ x (hQ θ x) v).trans ?_)
        rw [map_zero]
        exact h_Q
      -- `M θ x = 0`, so the value read off it is `0`
      have h_read_x := h_read θ x (hQ θ x) v f
      rw [hMx, map_zero] at h_read_x
      rw [zero_mulVec]
      exact h_read_x.symm
    · -- For r the element M does not depend on θ.
      have h_indep : M θ none hP v = M t₀ none hP v :=
        periodTensorMap_injective ((hM θ none hP v).trans (hM t₀ none hP v).symm)
      exact (h_read θ none hP v f).symm.trans
        ((congrArg _ h_indep).trans (h_read t₀ none hP v f))
  -- The coordinates of `Amax` separate points, so M vanishes; δ and ℓ are cancelled.
  have hMr : M t₀ none hP v = 0 := by
    refine tensor_eq_zero_of_separating c.eq_zero_of_coord _ fun i ↦ ?_
    -- each coordinate reads `M` as the relation `h_zero` applied to `v`
    exact (h_read t₀ none hP v _).trans
      ((congrArg (· *ᵥ v) (h_zero _)).trans (zero_mulVec v))
  -- `hM` at `t₀` for `r` (`X t₀ none` unfolds to `r`): the scaled value is `0`
  have h_scaled : (δ • (ℓ ^ (k * d) : Bmax) ^ n) •
      P.eval₂ (coeffEnd (PadicAlgCl ℓ) (m → PadicAlgCl ℓ)) (linearFrob (decompRep r A) ⟨s, hs⟩ k)
        (1 ⊗ₜ v) = 0 := by
    have h_t₀ := hM t₀ none hP v
    rw [hMr, map_zero] at h_t₀
    exact h_t₀.symm
  simpa [hδ.ne_zero, Algebra.smul_def δ, (NeZero.of_faithfulSMul ℚ_[ℓ] _ ℓ).out,
    -map_eq_zero, -isUnit_map_iff] using h_scaled

/-- If `Q η i` kills `s` on `ρ η i`, all degrees are below `n`, and the traces also converge when
weighted by each coefficient of `Q η i` and of `P`, then `P` kills `s` on `r`. -/
theorem polyKillsAt (h : IsTraceLimit r A F a ρ) {s : Gal(Ω/E)} {n : ℕ} {P : (PadicAlgCl ℓ)[X]}
    {Q : (η : I) → ι η → (PadicAlgCl ℓ)[X]} (hP : P.natDegree < n)
    (hQ : ∀ (η : I) (i : ι η), (Q η i).natDegree < n)
    (h_kill : ∀ (η : I) (i : ι η), PolyKillsAt (ρ η i).rep A s (Q η i))
    (h_coeff : ∀ l : ℕ, TendstoUniformly
        (fun (η : I) (g : Gal(Ω/E)) ↦
          ∑ i : ι η, a η i * (Q η i).coeff l * ((ρ η i).rep g).val.trace)
        (fun g : Gal(Ω/E) ↦ P.coeff l * (r g).val.trace) F) :
    PolyKillsAt r A s P := by
  refine ⟨fun hA ↦ ?_, @fun chart hs k hw ↦ h.isKilledBy hs hP hQ h_kill h_coeff hw⟩
  -- Off ℓ, the relations `Q θ x (s) = 0` in the `ρ θ x` pass to `P (s) = 0` in `r`.
  exact h.eq_zero_of_relation (n := n) h_coeff (fun _ l ↦ .single s 1 ^ l)
    (by simp [← aeval_eq_sum_range', (h_kill _ _).left hA, hQ]) (by simp [aeval_eq_sum_range' hP])

end IsTraceLimit

/-- Limits of traces keep the local clauses: unramified or crystalline, the jumps, and the
polynomials that kill a Weil element (`IsTraceLimit.isGoodAt`, `.jumpsRelAt`, `.polyKillsAt`). -/
lemma local_clauses_of_trace_limit [PadicIso ℓ] {r : GalRep ℓ E m} {A : ClosurePlace}
    {F : Filter I} [NeBot F] {a : (η : I) → ι η → PadicAlgCl ℓ}
    {ρ : (η : I) → ι η → PadicRep Gal(Ω/E) ℓ}
    (h : IsTraceLimit r A F a ρ) {R R' : ℕ → ℕ → Prop} {J : (E →+* ℂ) → Multiset ℤ}
    {J' : (η : I) → ι η → (E →+* ℂ) → Multiset ℤ}
    (h_jump : ∀ (η : I) (i : ι η), JumpsRelAt (ρ η i).rep A R' (J' η i))
    (h_rel : ∀ (τ : E →+* ℂ) (u : ℤ) (x : (η : I) → ι η → ℕ) (n : ℕ),
      (∀ (η : I) (i : ι η), R' ((J' η i τ).count u) (x η i)) →
      Tendsto (fun η : I ↦ ∑ i : ι η, a η i * x η i) F (nhds n) →
      R ((J τ).count u) n) :
    IsGoodAt r A ∧
    JumpsRelAt r A R J ∧
    ∀ ⦃s : Gal(Ω/E)⦄ ⦃n : ℕ⦄ ⦃P : (PadicAlgCl ℓ)[X]⦄ ⦃Q : (η : I) → ι η → (PadicAlgCl ℓ)[X]⦄,
      P.natDegree < n →
      (∀ (η : I) (i : ι η), (Q η i).natDegree < n ∧ PolyKillsAt (ρ η i).rep A s (Q η i)) →
      (∀ l : ℕ, TendstoUniformly
          (fun (η : I) (g : Gal(Ω/E)) ↦
            ∑ i : ι η, a η i * (Q η i).coeff l * ((ρ η i).rep g).val.trace)
          (fun g : Gal(Ω/E) ↦ P.coeff l * (r g).val.trace) F) →
      PolyKillsAt r A s P :=
  ⟨h.isGoodAt, h.jumpsRelAt h_jump h_rel, fun _ _ _ _ hP hQ h_coeff ↦
    h.polyKillsAt hP (fun η i ↦ (hQ η i).left) (fun η i ↦ (hQ η i).right) h_coeff⟩

end New.GaloisRep

end LocalLimit
