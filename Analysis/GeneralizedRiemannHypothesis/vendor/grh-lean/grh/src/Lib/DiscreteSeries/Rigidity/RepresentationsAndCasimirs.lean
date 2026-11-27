import Lib.DiscreteSeries.FlenstedJensen.Defs

/-!
# gl_n-modules, unitary representations of U(J) and a Casimir bound on K-highest vectors

This file treats representations of the unitary group `New.U J` (the matrices g with gᴴJg = J) and
modules over `gl n` (`New.GlModule`), where `E_ab` acts by `New.GlModule.E`. Signs `ε : n → ℤˣ` fix
the compact subgroup `K`. They split `gl n` into 𝔨, spanned by the `E_ab` with `ε_a = ε_b`, and 𝔭,
spanned by the others. An integer vector `l` (a `New.HCParam ε`, read as 2λ) orders the indices, and
`E_ab` raises when `l_b < l_a`. For a symmetric relation r on the indices, `New.twoRho l r` is the
sum of the roots e_a − e_b with r(a, b) that are positive for this order. `New.GlModule.casimirK` is
the sum of `E_ab E_ba` over the pairs with `ε_a = ε_b`. For the constant sign it is the full Casimir
operator of `gl n`. κ_λ = |λ|² − |ρ|² is `New.HCParam.casimirValue l`, where ρ in this formula is
the half sum of the positive roots.

## Main definitions and results

* `New.GlModule`: a module over the Lie algebra of complex matrices; `New.GlModule.E` is the action
  of an elementary matrix, `New.GlModule.casimir` and `New.GlModule.casimirK` are Casimir operators.
* `New.IsUnitaryRep`: a representation on a normed space that is strongly continuous, of polynomial
  growth, and preserves a positive definite hermitian form.
* `New.IsDerivedAction`, `New.GlModule.IsCoeffMap`: the module is the derivative of a
  representation, or of a family of linear maps indexed by the group, along `New.expU` (the matrix
  exponential).
* `New.IsUnitaryCasimirGe`: the inner product is invariant, ⟨E_ab v, w⟩ = ε_a ε_b ⟨v, E_ba w⟩, and
  the full Casimir operator is bounded below by κ_λ.
* `New.HCParam.IsKHighest.casimirK_eq_smul`: if `l.HasGap g`, the Casimir operator of 𝔨 acts on a
  K-highest vector by `New.HCParam.casimirKValue`.
* `New.HCParam.IsKHighest.sum_card_sq_add_mul_nonneg`: if `l.HasGap g`, the inner product is
  invariant and the full Casimir operator is bounded below by κ_λ, a nonzero K-highest vector of
  weight Λ + ν gives Σ_a (n² + ν_a(ν_a + l_a)) ≥ 0, that is, |ν|² + 2⟨ν, λ⟩ ≥ −n³.

## Relation to the literature

Lowest K-type and Casimir value are known to determine a discrete series coefficient, via analytic
vectors. See `Lib.DiscreteSeries.Rigidity.HighestVectorsAndFiltration`.
-/

noncomputable section

/-!
## Modules over gl_n and unitary representations of unitary groups

* `New.HCParam.IsKHighest`, `New.HCParam.rootCone`: `K`-highest vectors and the cone of positive
  roots.
-/

section RepresentationDefs

open Matrix Module Norms.L2Operator

namespace New

/-- A gl_n(ℂ)-module structure on a complex vector space M: a linear map from n×n matrices to
endomorphisms of M that respects commutators. -/
structure GlModule (n M : Type*) [Fintype n] [AddCommGroup M] [Module ℂ M] where
  /-- The action: a linear map from complex `n × n` matrices to endomorphisms of `M`. -/
  ρ : Matrix n n ℂ →ₗ[ℂ] End ℂ M
  /-- The action takes the commutator of two matrices to the commutator of their operators. -/
  map_bracket (X Y : Matrix n n ℂ) : ρ (X * Y - Y * X) = ρ X * ρ Y - ρ Y * ρ X

variable {n : Type} [Fintype.{0} n] [DecidableEq n]
  {X M : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [AddCommGroup M] [Module ℂ M]
variable {J : Matrix n n ℂ} (A : ℕ) (π : U J →* X →L[ℂ] X)
variable {ε : n → ℤˣ} (l : HCParam ε) (ι : M →ₗ[ℂ] X) (ρ : GlModule n M)

/-- The representation π of U(J) on X is strongly continuous with ‖π(g)‖ ≤ c‖g‖^A, and the
bounded form B is hermitian, positive definite and π-invariant. -/
structure IsUnitaryRep (B : X →L⋆[ℂ] X →L[ℂ] ℂ) where
  /-- `π` is strongly continuous: each orbit map `g ↦ π g x` is continuous. -/
  continuous (x : X) : Continuous (π · x)
  /-- The form `B` is invariant under `π`. -/
  invariant (g : U J) (x y : X) : B (π g x) (π g y) = B x y
  /-- The form `B` is hermitian. -/
  conj_symm (x y : X) : starRingEnd ℂ (B x y) = B y x
  /-- The form `B` is positive definite. -/
  pos : ∀ x ≠ (0 : X), 0 < (B x x).re
  /-- Polynomial growth: ‖π(g)‖ ≤ c‖g‖^A for a constant `c`, with the ℓ² operator norm of `g`. -/
  growth : ∃ c : ℝ, ∀ g : U J, ‖π g‖ ≤ c * ‖g.1.1‖ ^ A

-- A module is applied to a matrix: `ρ X` is the action of `X`.
instance : CoeFun (GlModule n M) fun _ : GlModule n M ↦ Matrix n n ℂ → End ℂ M := ⟨(·.ρ)⟩

/-- For a gl_n-module and indices a, b, the endomorphism by which the elementary matrix E_{ab}
acts. -/
abbrev GlModule.E (a b : n) : End ℂ M := ρ (single a b 1)

/-- For a gl_n(ℂ)-module and a subspace stable under all X, the gl_n(ℂ)-module structure on that
subspace obtained by restricting the action. -/
def GlModule.restrictTo (p : Submodule ℂ M) (h : ∀ X : Matrix n n ℂ, p ∈ (ρ X).invtSubmodule) :
    GlModule n p where
  ρ :=
    { toFun X := (ρ X).restrict (h X)
      map_add' := by aesop
      map_smul' := by aesop }
  map_bracket := by aesop (add simp map_bracket)

/-- The gl_n-module ρ on M is the derivative of π along ι: d/dt π(exp tY)ιv at t = 0 equals
ι(ρ(Y)v) for Y in Lie U(J), v in M. -/
def IsDerivedAction : Prop :=
  ∀ (Y : unitaryLie J) (v : M), HasDerivAt (fun t : ℝ ↦ π (expU (t • Y)) (ι v)) (ι (ρ Y v)) 0

/-- The vector x is killed by the compact raising operators for l: E_ab x = 0 whenever ε_a = ε_b
and l_b < l_a. -/
@[simp]
abbrev GlModule.IsCompactPrimitive (x : M) : Prop :=
  ∀ a b : n, ε a = ε b → l b < l a → ρ.E a b x = 0

/-- `x` is a `K`-highest vector of weight `ν`: each `E a a` acts on it by `ν a`, and it is killed by
the compact raising operators, the `E a b` with `ε a = ε b` and `l b < l a`. The vector `0` is
allowed. -/
def HCParam.IsKHighest (ν : n → ℤ) (x : M) : Prop :=
  (∀ a : n, ρ.E a a x = (ν a : ℂ) • x) ∧ ρ.IsCompactPrimitive l x

/-- The cone of the positive roots for the order given by `l`, described by duality: the integer
vectors `β` with `o ⬝ᵥ β ≤ 0` for every integer vector `o` that strictly reverses the order of
`l` (`l j < l i` implies `o i < o j`). A root `e_a - e_b` with `l b < l a` pairs with such an
`o` to `o a - o b < 0`, so sums of these roots lie in the cone. -/
def HCParam.rootCone : Set (n → ℤ) :=
  {β : n → ℤ | ∀ o : n → ℤ, (∀ i j : n, l j < l i → o i < o j) → o ⬝ᵥ β ≤ 0}

/-- The maps c(g) : M → X form a coefficient map for ρ: for Y in Lie U(J), the derivative of
t ↦ c(g exp tY)v is c(g exp tY)(ρ(Y)v). -/
def GlModule.IsCoeffMap (c : U J → M →ₗ[ℂ] X) : Prop :=
  ∀ (g : U J) (Y : unitaryLie J) (v : M) (t : ℝ),
    HasDerivAt (fun s : ℝ ↦ c (g * expU (s • Y)) v) (c (g * expU (t • Y)) (ρ Y v)) t

/-- For a relation r on indices, the endomorphism Σ E_ab E_ba of a gl_n-module, summed over the
pairs (a,b) with r(a,b). -/
def GlModule.casimir (r : n → n → Prop) [DecidableRel r] : End ℂ M :=
  ∑ a : n, ∑ b : n with r a b, ρ.E a b * ρ.E b a

variable (ε) in
/-- The Casimir operator of K: the endomorphism Σ E_ab E_ba of a gl_n-module, summed over the
index pairs with ε_a = ε_b. -/
abbrev GlModule.casimirK : End ℂ M := ρ.casimir fun a b ↦ ε a = ε b

end New

end RepresentationDefs

/-!
## Invariant inner products, twists and the filtration M_s

* `New.HCParam.casimirKValue`: the number |ν + ρ_c|² − |ρ_c|², with 2ρ_c given by `New.twoRho`.
-/

namespace New

variable {n : Type _} [Fintype n] [DecidableEq n]
  {M H : Type*} [AddCommGroup M] [Module ℂ M] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (ρ : GlModule n M) {ε : n → ℤˣ} (l ν : HCParam (n := n) ε) (x : M)

/-- The inner product of the gl_n-module H is invariant under 𝔲(diag ε), and the full Casimir
operator Ω = `ρ.casimirK 1` is bounded below by κ_λ = `l.casimirValue`, which is
|λ|² − |ρ|². -/
structure IsUnitaryCasimirGe (ρ : GlModule n H) : Prop where
  /-- Invariance: ⟨E_ab v, w⟩ = ε_a ε_b ⟨v, E_ba w⟩, so E_ab has the adjoint ε_a ε_b E_ba. -/
  inner_E_left (a b : n) (v w : H) :
    inner ℂ (ρ.E a b v) w = (ε a * ε b).val * inner ℂ v (ρ.E b a w)
  /-- The Casimir bound: κ_λ‖y‖² ≤ Re⟨y, Ωy⟩. -/
  casimirValue_mul_le (y : H) : l.casimirValue * ‖y‖ ^ 2 ≤ (inner ℂ y (ρ.casimirK 1 y)).re

/-- The integer |ν+ρ_c|² − |ρ_c|², where ρ_c is the half sum of the compact roots (ε_a = ε_b)
that are positive for the order of l. -/
def HCParam.casimirKValue : ℤ := ∑ a : n, ν a * (ν a + twoRho l (ε · = ε ·) a)

namespace GlModule

/-- The twist of a gl_n-module by an invertible matrix g: X acts as gXg⁻¹ does in the original
module. -/
def adTwist (g : GL n ℂ) : GlModule n M :=
  mk (ρ.ρ ∘ₗ LinearMap.mulLeftRight ℂ (g, ↑g⁻¹)) (by simp [← map_bracket, mul_assoc, map_sub])

/-- For a list of index pairs (a₁,b₁),…,(a_s,b_s), the endomorphism E_{a₁b₁}⋯E_{a_s b_s} of M,
the product taken in list order. -/
def word (w : List (n × n)) : Module.End ℂ M := (List.map ρ.E.uncurry w).prod

variable (ε)

/-- The filtration M_s generated by x: M_0 = U(𝔨)x, the least subspace containing x stable under
the E_ab with ε_a = ε_b, and M_{s+1} = M_s + Σ E_ab M_s. -/
def filtration : ℕ → Submodule ℂ M
  | 0 => sInf {W : Submodule ℂ M | x ∈ W ∧ ∀ a b : n, ε a = ε b → W ∈ (ρ.E a b).invtSubmodule}
  | s + 1 => filtration s ⊔ ⨆ (a : n) (b : n), (filtration s).map (ρ.E a b)

end GlModule

end New

/-!
## Commutation relations and Casimir operators on the filtration

* `New.GlModule.casimirK_one_adTwist`: the full Casimir operator is unchanged by the twist
  `New.GlModule.adTwist`.
-/

namespace New.GlModule

open Matrix Finset Submodule SetLike Module

variable {n : Type} [Fintype n] [DecidableEq n]
  {M : Type*} [AddCommGroup M] [Module ℂ M]
  {ε : n → ℤˣ} {ρ : GlModule n M} {x y : M} {s : ℕ} {a b : n} {c : ℂ}

theorem map_single_mul_single (c d : n) :
    ρ (single a b 1 * single c d 1) = if b = c then ρ.E a d else 0 := by aesop

theorem apply_eq_sum (X : Matrix n n ℂ) : ρ X = ∑ a : n, ∑ b : n, X a b • ρ.E a b := by
  simp [← map_smul, ← map_sum, ← matrix_eq_sum_single]

omit [DecidableEq n] in
theorem apply_apply_eq_swap_add_bracket (X Y : Matrix n n ℂ) :
    ρ X (ρ Y x) = ρ Y (ρ X x) + ρ (X * Y - Y * X) x := by
  simp [map_bracket]

/-- The commutation relation of the matrix units on a vector: E_ab E_cd v is E_cd E_ab v plus E_ad v
if b = c, minus E_cb v if d = a. -/
theorem E_apply_E_apply (a b c d : n) (v : M) :
    ρ.E a b (ρ.E c d v) = ρ.E c d (ρ.E a b v) +
      ((if b = c then ρ.E a d else 0) v - (if d = a then ρ.E c b else 0) v) := by
  simp [ρ.apply_apply_eq_swap_add_bracket (single a b _), map_single_mul_single]

/-- If ε_a = ε_b and E_ab commutes with D, then E_ab commutes with the sum over all c, d of
f(ε_c, ε_d) E_cd D E_dc, for any coefficients f that depend only on the signs. -/
theorem commute_E_sum_E_mul_mul_E (f : ℤˣ → ℤˣ → ℂ) {D : End ℂ M} (hab : ε a = ε b)
    (hD : Commute (ρ.E a b) D) :
    Commute (ρ.E a b) (∑ c : n, ∑ d : n, f (ε c) (ε d) • (ρ.E c d * D * ρ.E d c)) := by
  -- The commutator with `ρ.E a b` is a derivation that kills `D`. Its values on the matrix units
  -- cancel in the double sum, as the coefficients only see the signs and `ε a = ε b`.
  let δ (c d : n) : End ℂ M := (if b = c then ρ.E a d else 0) - if d = a then ρ.E c b else 0
  have h_bracket (c d : n) : ρ.E a b * ρ.E c d - ρ.E c d * ρ.E a b = δ c d := by
    rw [← ρ.map_bracket, map_sub, map_single_mul_single, map_single_mul_single]
  have h_term (c d : n) : ρ.E a b * (ρ.E c d * D * ρ.E d c) - ρ.E c d * D * ρ.E d c * ρ.E a b =
      δ c d * D * ρ.E d c + ρ.E c d * D * δ d c := by
    simp [← h_bracket, sub_mul, mul_sub, mul_assoc, hD.left_comm]
  have h_cancel :
      ∑ c : n, ∑ d : n, f (ε c) (ε d) • (δ c d * D * ρ.E d c + ρ.E c d * D * δ d c) = 0 := by
    simp [δ, hab, sub_mul, mul_sub, smul_sub, sum_add_distrib]
  rw [commute_iff_eq, ← sub_eq_zero, ← h_cancel]
  simp only [mul_sum, sum_mul, mul_smul_comm, smul_mul_assoc, ← sum_sub_distrib, ← smul_sub, h_term]

theorem commute_E_casimirK (hab : ε a = ε b) : Commute (ρ.E a b) (ρ.casimirK ε) := by
  -- Take `D = 1` and the coefficients that keep the pairs of equal signs.
  simpa [casimir, sum_filter, one_apply] using
    ρ.commute_E_sum_E_mul_mul_E (fun s t ↦ if s = t then (1 : ℂ) else 0) hab (Commute.one_right _)

/-- The Casimir operator of gl_n is unchanged by twisting the module with an invertible matrix. -/
theorem casimirK_one_adTwist (g : GL n ℂ) : (ρ.adTwist g).casimirK 1 = ρ.casimirK 1 := by
  -- Expand each twisted `E a b` in the matrix units; the sums over `a` and `b` then contract
  -- entries of `g` against entries of `g⁻¹` to Kronecker deltas.
  have h_conj (a b : n) :
      (ρ.adTwist g).E a b = ∑ c : n, ∑ d : n, (g.val c a * g⁻¹.val b d) • ρ.E c d := by
    simp [adTwist, E, ρ.apply_eq_sum (_ * _), mul_apply, single, ite_and]
  have h_delta (c d e f : n) : ∑ a : n, ∑ b : n, g.val c a * g⁻¹.val b d * (g.val e b * g⁻¹.val a f)
      = (g.val * g⁻¹.val) c f * (g.val * g⁻¹.val) e d := by
    simp only [mul_apply, sum_mul_sum]
    ac_rfl
  calc (ρ.adTwist g).casimirK 1
    _ = ∑ a : n, ∑ b : n, ∑ c : n, ∑ e : n, ∑ d : n, ∑ f : n,
        (g.val c a * g⁻¹.val b d * (g.val e b * g⁻¹.val a f)) • (ρ.E c d * ρ.E e f) := by
      simp only [casimir, h_conj, sum_mul_sum, smul_mul_smul_comm, Pi.one_apply, filter_true]
    _ = ∑ c : n, ∑ e : n, ∑ d : n, ∑ f : n,
        ((g.val * g⁻¹.val) c f * (g.val * g⁻¹.val) e d) • (ρ.E c d * ρ.E e f) := by
      -- Move the sums over `a` and `b` inside the other four.
      iterate 4 refine sum_comm_cycle.trans (sum_congr rfl fun _ _ ↦ ?_)
      simp only [← sum_smul, h_delta]
    _ = ρ.casimirK 1 := by simp [casimir, one_apply]

/-! ### The filtration generated by a vector -/

theorem filtration_mono : Monotone (ρ.filtration ε x) :=
  monotone_nat_of_le_succ fun _ ↦ le_sup_left

theorem self_mem_filtration : x ∈ ρ.filtration ε x s :=
  filtration_mono s.zero_le (mem_sInf.2 fun _W hW ↦ hW.1)

@[local simp]
theorem E_mem_filtration_succ (hy : y ∈ ρ.filtration ε x s) :
    ρ.E a b y ∈ ρ.filtration ε x (s + 1) :=
  mem_sup_right (mem_iSup_of_mem a (mem_iSup_of_mem b (mem_map_of_mem hy)))

/-- For ε_a = ε_b, every step M_s of the filtration is stable under E_ab. -/
theorem E_mem_filtration (hy : y ∈ ρ.filtration ε x s) (h_sign : ε a = ε b) :
    ρ.E a b y ∈ ρ.filtration ε x s := by
  induction s generalizing y with
  | zero =>
    -- Step zero is an intersection of subspaces that are stable under `ρ.E a b` when `ε a = ε b`.
    exact mem_sInf.2 fun W ⟨hx, h_stable⟩ ↦ h_stable a b h_sign (mem_sInf.1 hy W ⟨hx, h_stable⟩)
  | succ s ih =>
    -- Step `s + 1` is spanned by the vectors `v` and `ρ.E c d v` with `v` in step `s`.
    suffices H : ρ.filtration ε x (s + 1) ≤ (ρ.filtration ε x (s + 1)).comap (ρ.E a b) from H hy
    refine sup_le (fun v hv ↦ E_mem_filtration_succ hv) (iSup₂_le fun c d ↦ ?_)
    rintro _ ⟨v, hv : v ∈ ρ.filtration ε x s, rfl⟩
    -- Commute `ρ.E a b` past `ρ.E c d`; each term of the commutator is a matrix unit or zero.
    rw [mem_comap, E_apply_E_apply]
    refine add_mem (E_mem_filtration_succ (ih hv)) (sub_mem ?_ ?_) <;> split_ifs <;> simp [hv]

/-- If the Casimir operator of 𝔨 acts on x by the scalar c, it acts by c on every y in U(𝔨)x. -/
theorem casimirK_eq_smul_of_mem_filtration (hy : y ∈ ρ.filtration ε x 0)
    (hx : ρ.casimirK ε x = c • x) : ρ.casimirK ε y = c • y := by
  -- The eigenspace of `casimirK` contains `x` and is stable under the `E a b` with `ε a = ε b`.
  let W : Submodule ℂ M := LinearMap.eqLocus (ρ.casimirK ε) (c • 1)
  have h_stable (a b : n) (hab : ε a = ε b) : W ∈ (ρ.E a b).invtSubmodule := by
    intro v (hv : ρ.casimirK ε v = c • v)
    change (ρ.casimirK ε * ρ.E a b) v = c • ρ.E a b v
    rw [← (commute_E_casimirK hab).eq, End.mul_apply, hv, map_smul]
  exact mem_sInf.1 hy W ⟨hx, h_stable⟩

/-- The gl_n-module U(gl_n)x generated by x: the least subspace that contains x and is stable under
all E_ab, with the restricted action. -/
noncomputable def generatedModule (x : M) : GlModule n ↥(ρ.filtration 1 x 0) :=
  ρ.restrictTo (ρ.filtration 1 x 0) fun X ↦
    (End.mem_invtSubmodule_iff_forall_mem_of_mem _).2 fun y hy ↦ by
      simp only [ρ.apply_eq_sum X, LinearMap.sum_apply, LinearMap.smul_apply]
      exact sum_mem fun a _ ↦ sum_mem fun b _ ↦ smul_mem _ _ (E_mem_filtration hy rfl)

/-- If the full Casimir operator acts on x by the scalar c, it acts by c on the whole module
U(gl_n)x generated by x. -/
theorem casimirK_generatedModule (hx : ρ.casimirK 1 x = c • x) (y : ↥(ρ.filtration 1 x 0)) :
    (ρ.generatedModule x).casimirK 1 y = c • y := by
  ext1
  rw [SetLike.val_smul, ← casimirK_eq_smul_of_mem_filtration y.2 hx]
  simp only [casimir, LinearMap.sum_apply, End.mul_apply, Submodule.coe_sum]
  -- A restricted operator is the operator itself on the underlying vector.
  rfl

end New.GlModule

/-!
## Casimir values on K-highest vectors and the bound for weights Λ + ν

The Casimir operators evaluated on K-highest vectors (`New.HCParam.IsKHighest`: E_aa x = ν_a x, and
E_ab x = 0 when ε_a = ε_b and l_b < l_a).
-/

namespace New

open Finset Complex InnerProductSpace GlModule

variable {n : Type} [Fintype n] [DecidableEq n]
  {H M : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [AddCommGroup M] [Module ℂ M]
  {ε : n → ℤˣ} {ν : n → ℤ} {g : ℕ} {l : HCParam ε} {ρ : GlModule n H} {σ : GlModule n M}

/-- A vector x of the gl_n-module σ is K-highest of weight ν if E_ab acts on it by ν_a for a = b,
and by 0 for a ≠ b with ε_a = ε_b and l_b ≤ l_a. -/
theorem HCParam.IsKHighest.of_E_eq_smul {x : M}
    (h_act : ∀ a b : n, ε a = ε b → l b ≤ l a → σ.E a b x = (if a = b then (ν a : ℂ) else 0) • x) :
    l.IsKHighest σ ν x :=
  ⟨fun a ↦ by simp [h_act a a], fun a b h_sign h_lt ↦ by
    simp [h_act a b h_sign h_lt.le, ne_of_apply_ne l h_lt.ne']⟩

/-- For a gl_n-module σ, a symmetric relation r on the indices and an integer vector l with distinct
entries, the Casimir sum `σ.casimir r` = Σ_{r(a,b)} E_ab E_ba equals Σ_{r(a,a)} E_aa² + Σ_a (2ρ_r)_a
E_aa + 2 Σ_{r(a,b), l_a < l_b} E_ab E_ba. Here 2ρ_r = `twoRho l r` has a-th entry #{b : r(a,b),
l_b < l_a} − #{b : r(a,b), l_a < l_b}. -/
theorem GlModule.casimir_eq_diag_add_twoRho_add (σ : GlModule n M) {l : n → ℤ} (hl : l.Injective)
    (r : n → n → Prop) [DecidableRel r] (hr : Std.Symm r) :
    σ.casimir r =
      ∑ a : n with r a a, σ.E a a * σ.E a a + ∑ a : n, (twoRho l r a : ℂ) • σ.E a a +
        2 * σ.casimir fun a b : n ↦ r a b ∧ l a < l b := by
  -- Split the pairs into `a = b`, `l b < l a` and `l a < l b`. For `l b < l a` commute the two
  -- factors: the products give the third part again, and the commutators add up to 2ρ_r.
  have h_split : σ.casimir r =
      ∑ a : n with r a a, σ.E a a * σ.E a a + σ.casimir (fun a b : n ↦ r a b ∧ l b < l a) +
        σ.casimir fun a b : n ↦ r a b ∧ l a < l b := by
    have h_diag :
        ∑ a : n with r a a, σ.E a a * σ.E a a = σ.casimir fun a b ↦ r a b ∧ l a = l b := by
      simp [casimir, sum_filter, hl.eq_iff, and_comm (a := r _ _), ite_and]
    simp only [h_diag, casimir, sum_filter, ← sum_add_distrib]
    exact sum_congr rfl fun a _ ↦ sum_congr rfl fun b _ ↦ by grind
  have h_comm (a b : n) : σ.E a b * σ.E b a - σ.E b a * σ.E a b = σ.E a a - σ.E b b := by
    simp [← σ.map_bracket]
  have h_swap (f : n → n → Module.End ℂ M) : ∑ a : n, ∑ b : n with r a b ∧ l b < l a, f b a =
      ∑ a : n, ∑ b : n with r a b ∧ l a < l b, f a b :=
    sum_comm' fun a b ↦ by simp [comm_of r]
  have h_commuted : σ.casimir (fun a b : n ↦ r a b ∧ l b < l a) -
      σ.casimir (fun a b : n ↦ r a b ∧ l a < l b) = ∑ a : n, (twoRho l r a : ℂ) • σ.E a a :=
    calc _ = ∑ a : n, ∑ b : n with r a b ∧ l b < l a, (σ.E a a - σ.E b b) := by
          rw [casimir, casimir, ← h_swap fun a b ↦ σ.E a b * σ.E b a]
          simp only [← sum_sub_distrib, h_comm]
      _ = ∑ a : n, (twoRho l r a : ℂ) • σ.E a a := by
          simp only [sum_sub_distrib, h_swap fun a _ ↦ σ.E a a]
          simp [twoRho, sub_smul, Nat.cast_smul_eq_nsmul]
  rw [h_split, ← h_commuted, two_mul]
  abel

/-- If `l.HasGap g` (the entries of l are distinct, of the parity of n − 1, and at least 2g apart
where the signs differ; only distinctness is used here), the Casimir operator of 𝔨 acts on a
K-highest vector of weight ν by |ν + ρ_c|² − |ρ_c|² (`New.HCParam.casimirKValue`). -/
theorem HCParam.IsKHighest.casimirK_eq_smul {x : M} [hg : l.HasGap g] (hx : l.IsKHighest σ ν x) :
    σ.casimirK ε x = (l.casimirKValue ν : ℂ) • x := by
  -- Order the sum by `casimir_eq_diag_add_twoRho_add`: its last part kills `x`, and the diagonal
  -- terms act by scalars.
  obtain ⟨h_weight, h_primitive⟩ := hx
  have h_raising : σ.casimir (fun a b : n ↦ ε a = ε b ∧ l a < l b) x = 0 := by
    simp only [casimir, LinearMap.sum_apply, Module.End.mul_apply]
    refine sum_eq_zero fun a _ ↦ sum_eq_zero fun b hb ↦ ?_
    rw [h_primitive b a (by grind) (by grind), map_zero]
  rw [GlModule.casimirK, σ.casimir_eq_diag_add_twoRho_add hg.injective _ ⟨fun _ _ ↦ Eq.symm⟩]
  simp [h_raising, h_weight, casimirKValue, mul_add, add_smul, mul_comm, smul_smul,
    sum_add_distrib, sum_smul]

/-- If ρ satisfies `New.IsUnitaryCasimirGe` (only the invariance of the inner product is used),
⟨x, `ρ.casimir r` x⟩ is the sum of ε_a ε_b ‖E_ba x‖² over the pairs with r(a, b). -/
theorem IsUnitaryCasimirGe.inner_casimir {x : H} (h_unitary : IsUnitaryCasimirGe l ρ)
    (r : n → n → Prop) [DecidableRel r] : ⟪x, ρ.casimir r x⟫_ℂ =
      ∑ a : n, ∑ b : n with r a b, ((ε a * ε b).val * ‖ρ.E b a x‖ ^ 2 : ℝ) := by
  simp [casimir, ← inner_conj_symm x, sum_inner, h_unitary.inner_E_left]

/-- Casimir bound. Let l = 2λ satisfy `l.HasGap g`: distinct entries of the parity of n − 1, at
least 2g apart where the signs differ. Let ρ be a module with an invariant inner product such that
Re⟨y, Ωy⟩ ≥ κ_λ‖y‖² for all y (together these are `New.IsUnitaryCasimirGe`); Ω is the full
Casimir operator and κ_λ = |λ|² − |ρ_G|², with ρ_G the half sum of the roots positive for l. Let
x ≠ 0 be K-highest of weight Λ + ν, with Λ = `l.lowestKType` = λ + ρ_G − 2ρ_c. Then
Σ_a (n² + ν_a(ν_a + l_a)) ≥ 0, that is, |ν|² + 2⟨ν, λ⟩ ≥ −n³. -/
theorem HCParam.IsKHighest.sum_card_sq_add_mul_nonneg {x : H} (h_unitary : IsUnitaryCasimirGe l ρ)
    [hg : l.HasGap g] (hx_high : l.IsKHighest ρ (l.lowestKType + ν) x) (hx_ne : x ≠ 0) :
    0 ≤ ∑ a : n, (Fintype.card n ^ 2 + ν a * (ν a + l a)) := by
  -- Write Ω = Ω_𝔭 + Ω_K and order Ω_𝔭 by `casimir_eq_diag_add_twoRho_add` for −l. On x this is
  -- ∑ c a plus a remainder with Re⟨x, remainder x⟩ ≤ 0, so κ_λ ≤ ∑ c a. Compare entry by entry.
  let μ (a : n) : ℤ := l.lowestKType a + ν a
  let c (a : n) : ℤ := twoRho (-l) (ε · ≠ ε ·) a * μ a + μ a * (μ a + twoRho l (ε · = ε ·) a)
  let remainder : Module.End ℂ H := ρ.casimir fun a b : n ↦ ε a ≠ ε b ∧ l b < l a
  have h_split : ρ.casimirK 1 = ρ.casimir (ε · ≠ ε ·) + ρ.casimirK ε := by
    simp [casimir, ← sum_add_distrib, sum_filter_not_add_sum_filter]
  have h_noncompact : ρ.casimir (ε · ≠ ε ·) =
      ∑ a : n, (twoRho (-l) (ε · ≠ ε ·) a : ℂ) • ρ.E a a + 2 * remainder := by
    simp [remainder,
      ρ.casimir_eq_diag_add_twoRho_add hg.neg.injective (ε · ≠ ε ·) ⟨fun _ _ ↦ Ne.symm⟩]
  have h_casimir : ρ.casimirK 1 x = (∑ a : n, c a : ℂ) • x + (remainder x + remainder x) := by
    simp [h_split, h_noncompact, hx_high.casimirK_eq_smul, two_mul, c, μ, hx_high.1, casimirKValue,
      ← add_smul, smul_smul, ← sum_smul, sum_add_distrib, add_right_comm]
  have h_remainder_nonpos : re ⟪x, remainder x⟫_ℂ ≤ 0 := by
    rw [h_unitary.inner_casimir, ofReal_re]
    refine sum_nonpos fun a _ ↦ sum_nonpos fun b hb ↦ ?_
    have h_sign : ε a = -ε b := Int.units_ne_iff_eq_neg.1 (by grind)
    simp [h_sign]
  have h_value_le : l.casimirValue ≤ ∑ a : n, (c a : ℝ) := by
    have h_lower : l.casimirValue * ‖x‖ ^ 2 ≤
        (∑ a : n, c a : ℝ) * ‖x‖ ^ 2 + (re ⟪x, remainder x⟫_ℂ + re ⟪x, remainder x⟫_ℂ) := by
      simpa [h_casimir, ← ofReal_pow] using h_unitary.casimirValue_mul_le x
    exact le_of_mul_le_mul_right (a := ‖x‖ ^ 2) (by linarith) (by positivity)
  -- As 2ρ_c − 2ρ_n = l − 2Λ (`two_mul_lowestKType`), we have c = ν(ν + l) + Λ(l − Λ);
  -- also 4Λ(l − Λ) ≤ l² and each entry of 2ρ has absolute value at most n.
  have h_entry_le (a : n) : 4 * c a - (l a ^ 2 - twoRho l ⊤ a ^ 2) ≤
      4 * (Fintype.card n ^ 2 + ν a * (ν a + l a)) := by
    have h_c_eq : c a = ν a * (ν a + l a) + l.lowestKType a * (l a - l.lowestKType a) := by
      simp only [c, μ, twoRho_neg]
      linear_combination (l.lowestKType a + ν a) * two_mul_lowestKType hg a
    have h_twoRho_sq : twoRho l ⊤ a ^ 2 ≤ Fintype.card n ^ 2 := by
      grw [(sq_abs _).ge, abs_twoRho_le]
    nlinarith [sq_nonneg (l a - 2 * l.lowestKType a), sq_nonneg (Fintype.card n : ℤ)]
  rify at h_entry_le ⊢
  calc (0 : ℝ) ≤ ∑ a : n, (c a : ℝ) - l.casimirValue := sub_nonneg.2 h_value_le
    _ ≤ ∑ a : n, ((Fintype.card n : ℝ) ^ 2 + ν a * (ν a + l a)) := by
      rw [casimirValue, ← sum_sub_distrib]
      exact sum_le_sum fun a _ ↦ by linarith [h_entry_le a]

end New

end
