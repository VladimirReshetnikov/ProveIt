import Lib.Adelic.AutomorphicForms.AutomorphicAsAlgebraic
import Lib.GLn.Branching.IntegralMap

/-!
# Periods of algebraic forms over a block subgroup as class sums via branching

This file takes an algebraic form `ψ` on a definite unitary group of rank `m + 1`, a finite point
`u` of rank one and an automorphic `Φ(x, g) = L_g(ρ₀(x) c)` on the block subgroup of rank `m`.
It turns the integral of `Φ(h) ψ_t(diag(h, u))` into a class sum (`New.classIntegral`) over the
finite adelic points. Here `ψ_t = New.algFormCoeff 1 t ψ`, and `ρ`, `ρ₀` are the representations
`New.conjWeylRep` of weights `(κ, e)` and `(κ₀, e₀)`. The archimedean integral gives an
intertwiner from weight `(κ, e)` to weight `(κ₀, e₀)`, which multiplicity one for branching
(`New.SpansBranchingMaps`) makes a multiple of the given matrix `A`.

## Main definitions and results

* `New.Seesaw.integral_algFormCoeff_blockEmb`: the period over a block subgroup as a class sum.
* `New.Seesaw.isAutomorphic_algFormCoeff_blockEmb`: for a finite point `u` of rank one, the
  restriction `h ↦ ψ_t(diag(h, u))` to a block is automorphic on the smaller standard space.

Notions from other files:
* `New.Space.IsAutomorphic`: a function on `G = G_∞ × G_f` that is continuous, left invariant under
  rational points and right invariant under an open subgroup of `G_f`.
* `New.algFormCoeff s L φ`: the function `(x, g) ↦ L (ρ(x⁻¹) φ(g))`; it is `New.ofAlgForm l s φ` for
  `L = ⟨v⁺, ·⟩`, where `⟨·, ·⟩ = New.gramForm`.
* `New.classIntegral Γ K f`: the integral of `f` over `Γ \ G_f` for `vol K = 1`, as a finite sum.

## Relation to the literature

Known; see `Lib.Adelic.AutomorphicForms.AutomorphicAsAlgebraic` for sources.
-/

noncomputable section

namespace New.Seesaw

open NumberField MeasureTheory Matrix Space

variable {E ι X : Type} [Field E] [CMType E] [Fintype ι] [Fintype X] [DecidableEq X] [DecidableEq ι]

/-- The archimedean component of `diag((y, k), 1) = G.blockEmb hσ ((y, k), 1)` at a place `τ` is the
block matrix `diag(y τ, 1)`, reindexed along `σ` (`GL.blockScalar`). -/
lemma val_fst_blockEmb_one {σ : ι ⊕ Unit ≃ X} (hσ : (1 : X → ℤˣ) ∘ σ = (1 : ι → ℤˣ) ⊕ᵥ 1)
    (y : GInf E (1 : ι → ℤˣ)) (k : Gf E ι) (τ : InfinitePlace E) :
    ((G.blockEmb hσ ((y, k), (1 : G E (1 : Unit → ℤˣ)))).1 τ : GL X ℂ).val =
      GL.blockScalar (fun _ : InfinitePlace E ↦ σ) (fun w : InfinitePlace E ↦ (y w : GL ι ℂ).val) 1
        τ := by
  ext a b
  obtain ⟨a | a, rfl⟩ := σ.surjective a <;> obtain ⟨b | b, rfl⟩ := σ.surjective b <;>
    rw [← G.adeleMatrix_fst] <;> simp [G.blockEmb, GL.blockScalar]

/-- The block embedding sends a finite point `(1, k)` of the block to a finite point. -/
lemma fst_blockEmb_one_one {σ : ι ⊕ Unit ≃ X}
    (hσ : (1 : X → ℤˣ) ∘ σ = (1 : ι → ℤˣ) ⊕ᵥ 1) (k : Gf E ι) :
    (G.blockEmb hσ ((1, k), (1 : G E (1 : Unit → ℤˣ)))).1 = 1 := by
  ext τ : 3
  simp [val_fst_blockEmb_one, GL.blockScalar]

/-- `conjWeylMatrix κ e y` is `weylRep κ e` at the entrywise complex conjugate of `y`;
`conjWeylRep κ e y v` is `conjWeylMatrix κ e y *ᵥ v`. -/
lemma conjWeylMatrix_eq_weylRep_map_conj {E X : Type} [Field E] [CMType E] [Fintype X]
    [DecidableEq X] (κ : InfinitePlace E → ℕ → ℕ) (e : InfinitePlace E → ℤ)
    (y : GInf E (1 : X → ℤˣ)) :
    conjWeylMatrix κ e y = weylRep κ e
      fun τ : InfinitePlace E ↦ (y τ : GL X ℂ).map (starRingEnd ℂ) :=
  rfl

/-- The entrywise complex conjugate of a unitary matrix is unitary. -/
lemma map_conj_mem_uSign_one {g : GL X ℂ} (hg : g.valᴴ * g.val = 1) :
    g.map (starRingEnd ℂ) ∈ USign (1 : X → ℤˣ) := by
  simp [U, ← conjTranspose_map (⇑(starRingEnd ℂ)) fun _ ↦ rfl, ← Matrix.map_mul, hg]

variable {κ : InfinitePlace E → ℕ → ℕ} {e : InfinitePlace E → ℤ}
  {κ₀ : InfinitePlace E → ℕ → ℕ} {e₀ : InfinitePlace E → ℤ}

/-- Let `ψ` be an algebraic form, `t` a linear functional and `ψ_t = algFormCoeff 1 t ψ` the
function `(x, g) ↦ t (ρ(x⁻¹) ψ(g))`. For a finite point `u` of rank one, the restriction
`h ↦ ψ_t(diag(h, u))` to a block is automorphic on the smaller standard space. Here
`diag = G.blockEmb hσ`. -/
lemma isAutomorphic_algFormCoeff_blockEmb {σ : ι ⊕ Unit ≃ X}
    (hσ : (1 : X → ℤˣ) ∘ σ = (1 : ι → ℤˣ) ⊕ᵥ 1)
    (t : (WeylIndex X κ → ℂ) →ₗ[ℂ] ℂ) (ψ : AlgForm X κ e) (u : Gf E Unit) :
    (stdSpace E ι).IsAutomorphic
      fun h : G E (1 : ι → ℤˣ) ↦ algFormCoeff 1 t ψ (G.blockEmb hσ (h, 1, u)) := by
  let j : G E (1 : ι → ℤˣ) × G E (1 : Unit → ℤˣ) →* G E (1 : X → ℤˣ) := G.blockEmb hσ
  obtain ⟨h_cont, h_rat, K', h_level⟩ := (stdSpace E X).isAutomorphic_algFormCoeff (L := t) ψ
  -- `jf` is the block embedding `k ↦ diag(k, 1)` on finite points.
  let jf : Gf E ι →* Gf E X :=
    (MonoidHom.snd _ _).comp (j.comp (((MonoidHom.inr _ _).prod 1)))
  have jf_cont : Continuous fun k : Gf E ι ↦ (j ((1, k), 1)).2 := by fun_prop
  have j_fin (k : Gf E ι) : j ((1, k), 1) = (1, jf k) := Prod.ext (fst_blockEmb_one_one hσ k) rfl
  refine ⟨by fun_prop, fun γ hγ g ↦ ?_, K'.comap jf jf_cont, fun k hk g ↦ ?_⟩
  · -- `diag(γ, 1)` is a rational point
    have hγ_rat : j (γ, 1) ∈ (stdSpace E X).Γ := by simpa [j]
    calc algFormCoeff 1 t ψ (j (γ * g, 1, u))
      _ = algFormCoeff 1 t ψ (j (γ, 1) * j (g, 1, u)) := by simp [← map_mul]
      _ = algFormCoeff 1 t ψ (j (g, 1, u)) := h_rat _ hγ_rat _
  · -- the preimage of the level `K'` under `jf` is a level of the restriction
    calc algFormCoeff 1 t ψ (j (g * (1, k), 1, u))
      _ = algFormCoeff 1 t ψ (j (g, 1, u) * (1, jf k)) := by simp [← j_fin, ← map_mul]
      _ = algFormCoeff 1 t ψ (j (g, 1, u)) := h_level (jf k) hk _

/-- Suppose every intertwiner from weight `(κ, e)` to weight `(κ₀, e₀)` is a multiple of `A`
(`SpansBranchingMaps`). Then so is a matrix `B` with `B ρ(diag(y, 1)) = ρ₀(y) B` for all `y` in the
archimedean group of the block. Here `ρ` and `ρ₀` are the representations `conjWeylMatrix` of
weights `(κ, e)` and `(κ₀, e₀)`, and `diag(y, 1)` is the archimedean part of `G.blockEmb hσ`. -/
lemma exists_eq_smul_of_intertwines {σ : ι ⊕ Unit ≃ X} (hσ : (1 : X → ℤˣ) ∘ σ = (1 : ι → ℤˣ) ⊕ᵥ 1)
    {A B : Matrix (WeylIndex ι κ₀) (WeylIndex X κ) ℂ}
    (hA : SpansBranchingMaps (fun _ : InfinitePlace E ↦ σ) e₀ e A)
    (hB : ∀ y : GInf E (1 : ι → ℤˣ),
      B * conjWeylMatrix κ e (G.blockEmb hσ ((y, (1 : Gf E ι)), (1 : G E (1 : Unit → ℤˣ)))).1 =
        conjWeylMatrix κ₀ e₀ y * B) :
    ∃ C : ℂ, B = C • A := by
  -- `conjWeylMatrix` acts through complex conjugation: apply `hB` to the conjugate `y` of `g`.
  refine hA B fun g hg ↦ ?_
  let y : InfinitePlace E → USign (1 : ι → ℤˣ) :=
    fun τ ↦ ⟨(g τ).map (starRingEnd ℂ), map_conj_mem_uSign_one (hg τ)⟩
  let d : GInf E (1 : X → ℤˣ) := (G.blockEmb hσ ((y, (1 : Gf E ι)), (1 : G E (1 : Unit → ℤˣ)))).1
  -- The conjugate `x` of `d = diag(y, 1)` is `diag(g, 1)`, as the conjugate of `y` is `g`.
  let x : InfinitePlace E → GL X ℂ := fun τ ↦ (d τ : GL X ℂ).map (starRingEnd ℂ)
  have hx (τ : InfinitePlace E) : (x τ).val =
      GL.blockScalar (fun _ : InfinitePlace E ↦ σ) (fun w ↦ (g w).val) 1 τ := by
    rw [GeneralLinearGroup.val_map_apply, val_fst_blockEmb_one]
    ext a b
    obtain ⟨a | a, rfl⟩ := σ.surjective a <;> obtain ⟨b | b, rfl⟩ := σ.surjective b <;>
      simp [GL.blockScalar, y]
  have hy : (fun τ ↦ (y τ : GL ι ℂ).map (starRingEnd ℂ)) = g := by
    ext
    simp [y]
  refine ⟨x, hx, ?_⟩
  calc B * weylRep κ e x
    _ = conjWeylMatrix κ₀ e₀ y * B := hB y
    _ = weylRep κ₀ e₀ g * B := by rw [conjWeylMatrix_eq_weylRep_map_conj, hy]

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.sum Finset.prod Finset.univ in
/-- Let `V` be standard, `diag = G.blockEmb hσ` the embedding of the product of the block and the
rank-one group, and `A` a matrix of which every intertwiner from weight `(κ, e)` to weight
`(κ₀, e₀)` is a multiple (`SpansBranchingMaps`). For a linear form `t` and a vector `c` there is
`C` such that, for algebraic forms `ψ`, finite points `u` of rank one, every level `K` (an open
subgroup of `stdLevel`) and automorphic `Φ(x, g) = L_g(ρ₀(x) c)`, the integral of
`Φ(h) ψ_t(diag(h, u))` over `Γ \ G` is `C / [stdLevel : K]` times the class integral at level `K` of
`g ↦ L_g(A ψ(diag(g, u)))`. Here `ρ₀ = conjWeylRep κ₀ e₀`, `ψ_t = algFormCoeff 1 t ψ` and
`[stdLevel : K] = stdLevelIndex K`. -/
lemma integral_algFormCoeff_blockEmb {s : ι → ℤˣ}
    (V : Space E ι s) [hV : V.IsStd] {σ : ι ⊕ Unit ≃ X} (hσ : (1 : X → ℤˣ) ∘ σ = s ⊕ᵥ 1)
    {A : Matrix (WeylIndex ι κ₀) (WeylIndex X κ) ℂ}
    (hA : SpansBranchingMaps (fun _ : InfinitePlace E ↦ σ) e₀ e A)
    (t : (WeylIndex X κ → ℂ) →ₗ[ℂ] ℂ) (c : WeylIndex ι κ₀ → ℂ) :
    ∃ C : ℂ,
      ∀ (ψ : AlgForm X κ e) (Φ : G E s → ℂ) (u : Gf E Unit)
        (L : Gf E ι → (WeylIndex ι κ₀ → ℂ) →ₗ[ℂ] ℂ) (K : Subgroup (Gf E ι)) [IsLevel K],
      V.IsAutomorphic Φ →
      (∀ (x : GInf E s) (g : Gf E ι), Φ (x, g) = L g (conjWeylRep κ₀ e₀ x c)) →
      ∫ h : G E s, Φ h * algFormCoeff 1 t ψ (G.blockEmb hσ (h, 1, u)) ∂V.quotMeasure =
        C / stdLevelIndex K *
          classIntegral stdRatPoints K fun g : Gf E ι ↦
            L g (A *ᵥ ψ.val (G.blockEmb hσ ((1, g), 1, u)).2) := by
  -- Averaging the rank-one map `t.smulRight c` over the archimedean group gives an intertwiner `B`,
  -- and `B = C • A` by `hA`. The integral over `Γ \ G` is an archimedean integral, which
  -- produces `B`, inside a class sum over the finite part.
  -- A standard space has all signs `1` and the identity as its point.
  induction hV
  let j : G E (1 : ι → ℤˣ) × G E (1 : Unit → ℤˣ) →* G E (1 : X → ℤˣ) := G.blockEmb hσ
  -- The archimedean group of the block acts on weight `(κ, e)` through `x ↦ diag(x, 1)`.
  let R : GInf E (1 : ι → ℤˣ) →* Matrix (WeylIndex X κ) (WeylIndex X κ) ℂ :=
    (conjWeylMatrix κ e).comp
      ((MonoidHom.fst _ _).comp (j.comp ((MonoidHom.inl _ _).prod 1)))
  let M : Matrix (WeylIndex ι κ₀) (WeylIndex X κ) ℂ := (t.smulRight c).toMatrix'
  have hR : Continuous R := (continuous_conjWeylMatrix κ e 1).comp
    (by fun_prop : Continuous fun x : GInf E (1 : ι → ℤˣ) ↦ (j ((x, 1), 1)).1)
  have hρ₀ : Continuous fun x : GInf E (1 : ι → ℤˣ) ↦ conjWeylMatrix κ₀ e₀ x :=
    continuous_conjWeylMatrix κ₀ e₀ 1
  -- The average `B` of `ρ₀(x) M R(x⁻¹)` intertwines `R` with `ρ₀`.
  obtain ⟨B, hB_comm, hB_int⟩ :=
    exists_intertwining_mean volume (conjWeylMatrix κ₀ e₀) R M (by fun_prop)
  obtain ⟨C, hC⟩ : ∃ C : ℂ, B = C • A := exists_eq_smul_of_intertwines hσ hA hB_comm
  refine ⟨C, fun ψ Φ u L K hK hΦ hΦ_eq ↦ ?_⟩
  -- The restriction `h ↦ ψ_t(diag(h, u))` is automorphic, so the integral over `Γ \ G` is the class
  -- integral of the archimedean integrals, divided by the index `stdLevelIndex K`.
  have h_prod : (stdSpace E ι).IsAutomorphic fun h ↦ Φ h * algFormCoeff 1 t ψ (j (h, 1, u)) :=
    hΦ.map₂ (isAutomorphic_algFormCoeff_blockEmb hσ t ψ u) fun a b ↦ a * b
  rw [integral_eq_classIntegral_of_isLevel h_prod hK, eq_comm, div_eq_inv_mul, mul_assoc,
    ← classIntegral_const_mul]
  congr with g
  -- At each finite point `g`, the archimedean integral is `hB_int` for the linear form
  -- `N ↦ L g (N *ᵥ v)`, with `v` the value of `ψ` at `diag(g, u)`.
  let v : WeylIndex X κ → ℂ := ψ.val (j ((1, g), 1, u)).2
  have h_integrand (x : GInf E (1 : ι → ℤˣ)) :
      L g ((conjWeylMatrix κ₀ e₀ x * M * R x⁻¹) *ᵥ v) =
        Φ (x, g) * algFormCoeff 1 t ψ (j ((x, g), 1, u)) := by
    -- The archimedean part of `diag((x, g), u)` is `diag(x, 1)`; its finite part is `diag(g, u)`.
    have h_rank_one : M *ᵥ R x⁻¹ *ᵥ v = t (R x⁻¹ *ᵥ v) • c := LinearMap.toMatrix'_mulVec _ _
    rw [← mulVec_mulVec, ← mulVec_mulVec, h_rank_one, mulVec_smul, map_smul, smul_eq_mul,
      hΦ_eq, mul_comm]
    rfl
  calc C * L g (A *ᵥ v)
    _ = L g (B *ᵥ v) := by rw [hC, smul_mulVec, map_smul, smul_eq_mul]
    _ = ∫ x, L g ((conjWeylMatrix κ₀ e₀ x * M * R x⁻¹) *ᵥ v) :=
      (hB_int (L g ∘ₗ toLin'.toLinearMap.flip v)).symm
    _ = ∫ x, Φ (x, g) * algFormCoeff 1 t ψ (j ((x, g), 1, u)) :=
      integral_congr_ae (.of_forall h_integrand)

end New.Seesaw

end
