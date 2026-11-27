import Lib.Adelic.Unitary.ComponentsAndBlockSums
import Lib.General.LinearAlgebra.Eigenvalues
import Lib.LocalGL.Iwahori.ParahoricStructure
import Lib.Shimura.Uniformisation.HolomorphicFamilies

/-!
# Quadratic relation and injectivity of U_t at pro-p Iwahori level

Let `ρ` be a smooth representation of `GL_N(F)`, where `F` has compact ring of integers and a
uniformiser `ϖ`. This file shows that conjugation by a monomial matrix carries one parahoric
subgroup into another. With this it proves the quadratic relation for a simple transposition.
It shows that some operator `U_t` with `t` strictly dominant is injective on the vectors fixed by
`New.proIwahori`. For an exponent, it shows that the mean over `New.proIwahori` in the defining
identity can be dropped at diagonal matrices of units and at certain monomial translates.

## Main definitions and results

* `New.quadratic_relation`: the quadratic relation for a simple transposition.
* `New.exists_iwahoriHeckeHom_injective`: some operator `U_t` with `t` strictly dominant is
  injective on the vectors fixed by `New.proIwahori`. Here `U_t = New.iwahoriHeckeHom ρ t` sends
  such a vector `x` to the mean over `New.proIwahori` of `ρ(diag t) x`.

Notions from other files:
* `New.proIwahori`: The pro-p Iwahori subgroup I₁ of GL_n(𝒪): matrices that are upper triangular
  with ones on the diagonal modulo the maximal ideal.
* `New.dominantTorus`: Dominant elements of the diagonal torus: the `t` with `v (t i) ≤ v (t j)` for
  `i ≤ j`.
* `New.IsExponent`: `l (ρ(t) (mean of x over proIwahori)) = ξ(t) l(x)` for all dominant diagonal `t`
  and all `x`.

## Relation to the literature

Known; see `Lib.LocalGL.Iwahori.SphericalExponents` for sources.
-/

/-!
## Monomial matrices and the quadratic relation

Conjugation by a monomial matrix carries one parahoric subgroup into another
(`New.conj_monomial_mem_blockParahoric`); with it the file proves the quadratic relation for a
simple transposition.
-/

namespace New

open Matrix WithZero Valued Equiv Finset IsLocalRing Function Units

attribute [local instance low] Fintype.ofFinite

variable {F W : Type*} [Field F] [Valued F ℤᵐ⁰] [AddCommGroup W] [Module ℂ W]
  {N : ℕ} {ρ : Rep ℂ (GL (Fin N) F)}
  {x : ρ} {c : ℕ → ℕ} {d : ℕ → ℕ} {g : GL (Fin N) F} {a b : Fin N} {φ : ρ →ₗ[ℂ] W}

/-- An element `g` lies in `New.blockParahoric c` iff it lies in `GL_N` of the valuation ring and
its entry `g i j` has valuation less than 1 whenever `c j < c i`. -/
@[grind]
lemma mem_blockParahoric :
    g ∈ blockParahoric c ↔
      g ∈ intGL (Fin N) 𝒪[F] ∧ ∀ i j : Fin N, c j.val < c i.val → v (g i j) < 1 := .rfl

/-- An element lies in `New.proIwahori` iff it lies in the parahoric `New.blockParahoric id` and
every diagonal entry is congruent to 1 modulo the maximal ideal. -/
lemma mem_proIwahori_iff_blockParahoric :
    g ∈ proIwahori ↔ g ∈ blockParahoric id ∧ ∀ i : Fin N, g i i ∈ {x : F | v (x - 1) < 1} :=
  and_assoc.symm

/-- Let `c` and `d` be level functions `ℕ → ℕ` (see `New.blockParahoric`), and let `g` lie in the
parahoric of level function `d`. Let `m = σ diag(t)`, with `σ` a permutation matrix. Suppose that
for all `a`, `b` either `g_{σa,σb} = 0` or
`log v(t_b) + [c(b) < c(a)] ≤ log v(t_a) + [d(σb) < d(σa)]`, where `log` gives the integer exponent
of a valuation. Then `m⁻¹ g m` lies in the parahoric of level function `c`. -/
lemma conj_monomial_mem_blockParahoric_of_mem (t : Fin N → Fˣ) (σ : Perm (Fin N))
    (hg : g ∈ blockParahoric d)
    (ht : ∀ a b : Fin N,
      g (σ a) (σ b) = 0 ∨
      log (v (t b).val) + (if c b < c a then 1 else 0) ≤
        log (v (t a).val) + if d (σ b) < d (σ a) then 1 else 0) :
    (permGL σ * diagGL t)⁻¹ * g * (permGL σ * diagGL t) ∈ blockParahoric c := by
  set k : GL (Fin N) F := (permGL σ * diagGL t)⁻¹ * g * (permGL σ * diagGL t)
  have h_entry (a b : Fin N) : k a b = (t a).val⁻¹ * g (σ a) (σ b) * (t b).val := by
    simp [k, ← map_inv, mul_apply, symm_apply_eq, diagonal, mul_assoc]
  have h_det : k.val.det = g.val.det := det_units_conj' _ _
  simp only [mem_blockParahoric, mem_intGL_iff_det, h_entry, h_det, map_mul, map_inv₀] at hg ⊢
  obtain ⟨⟨hg_int, hg_det⟩, hg_below⟩ :
      ((∀ a b : Fin N, v (g a b) ≤ 1) ∧ v g.val.det = 1) ∧
        (∀ i j : Fin N, d j.val < d i.val → v (g i j) < 1) := hg
  refine ⟨⟨fun a b ↦ ?_, hg_det⟩, fun i j hij ↦ ?_⟩
  -- For a nonzero entry of `g` take `log` of its valuation, an integer that is `≤ 0`, or `≤ -1`
  -- if `d (σ b) < d (σ a)`, and add the inequality `ht`.
  · -- the entries of `k` are integral
    grind [Units.ne_zero, =_ log_le_log, =_ log_lt_log, map_eq_zero, log_mul, log_inv, mul_eq_zero,
      one_pos]
  · -- the entries `(i, j)` of `k` with `c j < c i` lie in the maximal ideal
    grind [Units.ne_zero, =_ log_le_log, =_ log_lt_log, map_eq_zero, log_mul, log_inv, mul_eq_zero,
      one_pos]

omit [Valued F ℤᵐ⁰] in
/-- The diagonal entries of `m⁻¹ g m`, for `m = σ diag(t)`, are those of `g`, permuted by `σ`; so
they lie in every set `S` that holds the diagonal entries of `g`. -/
lemma conj_monomial_apply_self_mem (t : Fin N → Fˣ) (σ : Perm (Fin N)) {S : Set F}
    (hgS : ∀ i : Fin N, g i i ∈ S) (i : Fin N) :
    ((permGL σ * diagGL t)⁻¹ * g * (permGL σ * diagGL t) : GL (Fin N) F) i i ∈ S := by
  have h_entry (a b : Fin N) :
      ((permGL σ * diagGL t)⁻¹ * g * (permGL σ * diagGL t) : GL (Fin N) F) a b =
        (t a).val⁻¹ * g (σ a) (σ b) * (t b).val := by
    simp [← map_inv, mul_apply, symm_apply_eq, diagonal, mul_assoc]
  rw [h_entry, mul_right_comm, inv_mul_cancel₀ (t i).ne_zero, one_mul]
  exact hgS (σ i)

/-- Let `g` lie in the parahoric of level function `d`, with diagonal entries in `S`, and let
`m = σ diag(t)` satisfy the condition of `New.conj_monomial_mem_blockParahoric_of_mem`. Then
`m⁻¹ g m` lies in the parahoric of level function `c`, with diagonal entries in `S`. -/
lemma conj_monomial_mem_blockParahoric (t : Fin N → Fˣ) (σ : Perm (Fin N)) (S : Set F)
    (hg : g ∈ blockParahoric d ∧ ∀ i : Fin N, g i i ∈ S)
    (ht : ∀ a b : Fin N,
      g (σ a) (σ b) = 0 ∨
      log (v (t b).val) + (if c b < c a then 1 else 0) ≤
        log (v (t a).val) + if d (σ b) < d (σ a) then 1 else 0) :
    (permGL σ * diagGL t)⁻¹ * g * (permGL σ * diagGL t) ∈ blockParahoric c ∧
      ∀ i : Fin N, ((permGL σ * diagGL t)⁻¹ * g * (permGL σ * diagGL t) : GL (Fin N) F) i i ∈ S :=
  ⟨conj_monomial_mem_blockParahoric_of_mem t σ hg.left ht,
    conj_monomial_apply_self_mem t σ hg.right⟩

/-- If `x` is fixed by `New.proIwahori` and `σ a < σ b`, then `ρ(σ⁻¹) x` is fixed by `1 + c E_ab`
for integral `c`. -/
lemma transvectionGL_apply_permGL_inv {h : a ≠ b} {σ : Perm (Fin N)}
    (hx : x ∈ levelSpace ρ.ρ proIwahori) (hσ : σ a < σ b) (c : F) (hc : v c ≤ 1) :
    ρ (transvectionGL h c) (ρ (permGL σ⁻¹) x) = ρ (permGL σ⁻¹) x := by
  -- Moved past the permutation, `transvectionGL h c` becomes an upper triangular element of
  -- `proIwahori`.
  have h_comm : transvectionGL h c * permGL σ⁻¹ = permGL σ⁻¹ * transvectionGL hσ.ne c := by
    simpa using (permGL_mul_transvectionGL σ⁻¹ hσ.ne c).symm
  have h_fix : ρ (transvectionGL hσ.ne c) x = x := by
    simpa using hx ⟨_, transvectionGL_mem_proIwahori hσ.ne (.inr ⟨hc, hσ⟩)⟩
  rw [← Module.End.mul_apply, ← map_mul ρ.ρ, h_comm, map_mul ρ.ρ, Module.End.mul_apply, h_fix]

/-- If `c j < c i` forces `j < i`, as it does for monotone `c`, then the pro-`p` Iwahori subgroup
lies in the parahoric subgroup for the blocks of `c`. -/
lemma proIwahori_le_blockParahoric {c : ℕ → ℕ} (hc : ∀ i j : ℕ, c j < c i → j < i) :
    (proIwahori : Subgroup (GL (Fin N) F)) ≤ blockParahoric c := by
  intro g hg
  -- The condition for the level function `id` implies the one for `c`, by `hc`.
  obtain ⟨h_int, h_below⟩ :=
    mem_blockParahoric.mp (mem_proIwahori_iff_blockParahoric.mp hg).left
  exact mem_blockParahoric.mpr ⟨h_int, fun i j hij ↦ h_below i j (hc i j hij)⟩

/-! ### The quadratic relation -/

omit [Valued F ℤᵐ⁰] in
/-- The factorisation `s (1 + u E_ab) = (1 + u⁻¹ E_ab) d (1 + u⁻¹ E_ba)`, for `s` the transposition
of `a` and `b` and `d` diagonal with `-u⁻¹` at `a`, `u` at `b` and `1` elsewhere. -/
@[local simp]
lemma swap_mul_transvectionGL (h : a ≠ b) (u : Fˣ) :
    permGL (Equiv.swap a b) * transvectionGL h u.val =
      transvectionGL h u.val⁻¹ * diagGL (Pi.mulSingle a (-u⁻¹) * Pi.mulSingle b u) *
        transvectionGL h.symm u.val⁻¹ := by
  -- Compare entries: after unfolding, the entry `(i, j)` is a case split on `i, j ∈ {a, b}`.
  ext i j
  simp [PEquiv.toMatrix_mul_apply, transvection, mul_add, add_mul, single_apply, one_apply,
    diagonal_apply, apply_ite Units.val, Pi.mulSingle_apply]
  grind

/-- For adjacent indices (`h : a ⋖ b`, that is `b = a + 1`) and `g` in `New.proIwahori` there is an
integral `c` such that the transposition of `a` and `b` conjugates `g (1 + c E_ab)` into
`New.proIwahori`. -/
lemma exists_swap_conj_mem_proIwahori (h : a ⋖ b) (hg : g ∈ proIwahori) :
    ∃ c : 𝒪[F],
      MulAut.conj (permGL (Equiv.swap a b)) (g * transvectionGL h.ne c.val) ∈ proIwahori := by
  -- Choose `c` so that the column operation `transvectionGL h.ne c` clears the entry `(a, b)`. As
  -- `a` and `b` are adjacent, this is the only entry that the swap moves from above the diagonal to
  -- below it.
  let c : F := -g a b / g a a
  have hc_int : v c ≤ 1 := by simp_all [c, v_diag_eq_one_of_mem_proIwahori, mem_proIwahori]
  have h_cleared : g * transvectionGL h.ne c ∈ proIwahori :=
    mul_mem hg (transvectionGL_mem_proIwahori _ (.inr ⟨hc_int, h.lt⟩))
  have h_conj_eq : MulAut.conj (permGL (Equiv.swap a b)) (g * transvectionGL h.ne c) =
      (permGL (swap a b) * diagGL 1)⁻¹ * (g * transvectionGL h.ne c) *
        (permGL (swap a b) * diagGL 1) := by simp [MulAut.conj_apply, ← map_inv]
  refine ⟨⟨c, hc_int⟩, ?_⟩
  rw [mem_proIwahori_iff_blockParahoric] at h_cleared
  rw [h_conj_eq, mem_proIwahori_iff_blockParahoric]
  refine conj_monomial_mem_blockParahoric 1 (swap a b) _ h_cleared ?_
  -- For `t = 1` the condition of `conj_monomial_mem_blockParahoric` asks only that the entry
  -- `(a, b)` vanish.
  have h_entry_zero : (g.val * transvection a b c) a b = 0 := by
    have h_aa_ne : g a a ≠ 0 := fun h_zero ↦ by
      simpa [h_zero] using v_diag_eq_one_of_mem_proIwahori hg a
    simp [mul_transvection_apply_same, c, h_aa_ne]
  obtain ⟨h_lt, h_adj⟩ := h
  -- Only the pair `(a, b)` is exchanged across the diagonal, and there the entry is `0`.
  suffices h_pairs : ∀ i j : Fin N, (g.val * transvection a b c) (swap a b i) (swap a b j) = 0 ∨
        ((if j < i then 1 else 0 : ℤ) ≤ if swap a b j < swap a b i then 1 else 0) by
    simpa using h_pairs
  grind [one_pos]

/-- If `v u = 1`, every entry of the diagonal torus element with `-u⁻¹` at `a`, `u` at `b` and `1`
elsewhere has valuation `1`. -/
lemma v_mulSingle_neg_inv_mul_mulSingle_eq_one {u : Fˣ} (hu : v u.val = 1) (i : Fin N) :
    v ((Pi.mulSingle a (-u⁻¹) * Pi.mulSingle b u : Fin N → Fˣ) i).val = 1 := by
  aesop (add simp Pi.mulSingle_apply)

/-- The quadratic relation. Let `b = a + 1`, let `s` be the transposition of `a` and `b`, `q` the
order of the residue field, and `φ` a linear map invariant under `New.proIwahori`. Let `x` be fixed
by all `1 + r E_ba` with `r` integral. Let `φ (ρ(d) x) = c` for every diagonal `d` with `-u⁻¹` at
`a`, `u` at `b` and `1` elsewhere, where `v u = 1`. Then
`q φ (s (mean of x over New.proIwahori)) = φ (s x) + (q - 1) c`. -/
lemma quadratic_relation [CompactSpace 𝒪[F]] [IsSmoothRep ρ.ρ]
    (hab : a ⋖ b) (c : W) (hφ : ∀ k ∈ proIwahori, ∀ z : ρ, φ (ρ k z) = φ z)
    (hx : ∀ r : F, v r ≤ 1 → ρ (transvectionGL hab.ne' r) x = x)
    (hc : ∀ u : Fˣ, v u.val = 1 →
      φ (ρ (diagGL (Pi.mulSingle a (-u⁻¹) * Pi.mulSingle b u)) x) = c) :
    Nat.card 𝓀[F] • φ (ρ (permGL (Equiv.swap a b)) (compactMean ρ.ρ proIwahori x)) =
      φ (ρ (permGL (Equiv.swap a b)) x) + (Nat.card 𝓀[F] - 1) • c := by
  classical
  -- Let `y = ∑ r, ρ (transvectionGL hab.ne (f r)) x`, with `f r` running over lifts of the residue
  -- field, and `τ` the matrix of the transposition. The mean of `y` is `q` times that of `x`, and
  -- `φ (ρ τ (ρ g y))` is the right side for every `g ∈ proIwahori`.
  choose f hf using (residue_surjective : ∀ r : 𝓀[F], ∃ f : 𝒪[F], residue 𝒪[F] f = r)
  set τ : GL (Fin N) F := permGL (swap a b) with hτ
  have h_term {w : F} (hw : v w ≤ 1) :
      φ (ρ (τ * transvectionGL hab.ne w) x) = if v w < 1 then φ (ρ τ x) else c := by
    rcases hw.lt_or_eq with hw_lt | hw_eq
    · -- Moved to the left of `τ`, `transvectionGL hab.ne w` lies in `proIwahori`.
      rw [ite_eq_left hw_lt, hτ, permGL_mul_transvectionGL, map_mul ρ.ρ, Module.End.mul_apply]
      exact hφ _ (transvectionGL_mem_proIwahori _ (.inl hw_lt)) _
    · -- Factor `τ (1 + w E_ab) = (1 + w⁻¹ E_ab) d (1 + w⁻¹ E_ba)`: the left factor lies in
      -- `proIwahori`, the right one fixes `x`, and `φ (ρ d x) = c`.
      have hw_unit : IsUnit w := isUnit_iff_ne_zero.mpr fun hw_zero ↦ by simp [hw_zero] at hw_eq
      lift w to Fˣ using hw_unit
      have hw_inv : v w.val⁻¹ ≤ 1 := by simp [hw_eq]
      rw [ite_eq_right hw_eq.not_lt, hτ, swap_mul_transvectionGL hab.ne w]
      simp only [map_mul ρ.ρ, Module.End.mul_apply, hx _ hw_inv,
        hφ _ (transvectionGL_mem_proIwahori hab.ne (.inr ⟨hw_inv, hab.lt⟩))]
      exact hc w hw_eq
  have h_tv (p q : F) :
      transvectionGL hab.ne p * transvectionGL hab.ne q = transvectionGL hab.ne (p + q) :=
    Units.ext (transvection_mul_transvection_same _ _ hab.ne p q)
  let y : ρ := ∑ r, ρ (transvectionGL hab.ne (f r)) x
  -- Each summand of `y` has the mean of `x`, as the transvections lie in `proIwahori`.
  have h_mean_term (r : 𝓀[F]) :
      compactMean ρ.ρ proIwahori (ρ (transvectionGL hab.ne (f r)) x) =
        compactMean ρ.ρ proIwahori x :=
    compactMean_apply (transvectionGL_mem_proIwahori hab.ne (.inr ⟨(f r).prop, hab.lt⟩)) x
  have h_mean : compactMean ρ.ρ proIwahori y = Nat.card 𝓀[F] • compactMean ρ.ρ proIwahori x := by
    simp [y, h_mean_term]
  have h_const (g : GL (Fin N) F) (hg : g ∈ proIwahori) :
      φ (ρ τ (ρ g y)) = φ (ρ τ x) + (Nat.card 𝓀[F] - 1) • c := by
    -- Modulo `proIwahori` on the left, `τ * g` is `τ * transvectionGL hab.ne (-z)`, which shifts
    -- `f r` to `f r - z`.
    obtain ⟨z, hk⟩ : ∃ z : 𝒪[F],
        MulAut.conj (permGL (Equiv.swap a b)) (g * transvectionGL hab.ne z.val) ∈ proIwahori :=
      exists_swap_conj_mem_proIwahori hab hg
    have h_shift (r : 𝓀[F]) :
        φ (ρ (τ * g * transvectionGL hab.ne (f r).val) x) =
          φ (ρ (τ * transvectionGL hab.ne (f r - z).val) x) := by
      have h_prod : τ * g * transvectionGL hab.ne (f r).val =
          MulAut.conj (permGL (Equiv.swap a b)) (g * transvectionGL hab.ne z.val) *
            (τ * transvectionGL hab.ne (f r - z).val) := by
        simp [τ, MulAut.conj_apply, mul_assoc, h_tv]
      rw [h_prod, map_mul ρ.ρ, Module.End.mul_apply, hφ _ hk]
    have h_lt_iff (r : 𝓀[F]) : v (f r - z).val < 1 ↔ r = residue 𝒪[F] z := by
      rw [← residue_eq_zero_iff_valuation_lt_one, map_sub, hf, sub_eq_zero]
    calc
      _ = ∑ r, φ (ρ (τ * g * transvectionGL hab.ne (f r).val) x) := by simp [y]
      _ = ∑ r, if v (f r - z).val < 1 then φ (ρ τ x) else c :=
        sum_congr rfl fun r _ ↦ (h_shift r).trans (h_term (f r - z).prop)
      -- Exactly one `r`, the residue of `z`, has `v (f r - z) < 1`.
      _ = ∑ r, if r = residue 𝒪[F] z then φ (ρ τ x) else c :=
        sum_congr rfl fun r _ ↦ if_congr (h_lt_iff r) rfl rfl
      _ = _ := by simp [sum_ite, filter_ne', card_filter]
  simpa [h_mean] using map_compactMean_of_const (φ ∘ₗ ρ τ) h_const

end New

/-!
## Injectivity of some U_t, and invariance properties of exponents

Some `U_t` with `t` strictly dominant is injective. For an exponent, the mean over `New.proIwahori`
in its defining identity can be dropped in two cases: at diagonal matrices of units
(`New.IsExponent.apply_diagGL_unit`) and at certain monomial translates
(`New.IsExponent.apply_diagGL_apply_diagGL_mul_permGL`).
-/

section IwahoriInjective

open WithZero Valued Finset Equiv OrderDual

namespace New

variable {F : Type*} [Field F] [Valued F ℤᵐ⁰]
  {N : ℕ} {ϖ : Fˣ} (ρ : Rep ℂ (GL (Fin N) F)) [IsSmoothRep ρ.ρ] (hϖ : v ϖ.val = exp (-1))

/-- A diagonal matrix whose entries are units of the ring of integers conjugates every element of
`New.proIwahori` into `New.proIwahori`. -/
lemma diagGL_conj_mem_proIwahori_of_v_eq_one {t : Fin N → Fˣ} {k : GL (Fin N) F}
    (hk : k ∈ proIwahori) (ht : ∀ i : Fin N, v (t i).val = 1) :
    diagGL t * k * (diagGL t)⁻¹ ∈ proIwahori := by
  -- All entries of `t` have the same valuation, so every matrix is block triangular for it.
  exact diagGL_conj_mem_proIwahori hk fun i j hij ↦ by simp [ht] at hij

/-- Let `F` have a uniformiser `ϖ` (`v ϖ = exp (-1)`) and let `ρ` be a smooth representation of
`GL_N(F)`. For dominant diagonal `t`, `U_t = iwahoriHeckeHom ρ t` acts on the vectors fixed by the
pro-`p` Iwahori subgroup `New.proIwahori`: it applies `ρ (diagGL t)` and then takes the mean
`compactMean` over `proIwahori`. There is a strictly dominant `t` (the valuations `v (t i)`, written
multiplicatively, strictly increase) such that `U_t` is injective. It is a case of the Moy–Prasad
and Morris injectivity of fixed vectors into the Jacquet module. -/
lemma exists_iwahoriHeckeHom_injective [CompactSpace 𝒪[F]] (hϖ : v ϖ.val = exp (-1)) :
    ∃ t : Fin N → Fˣ, ∃ h : StrictMono fun i : Fin N ↦ v (t i).val,
      Function.Injective (iwahoriHeckeHom ρ ⟨t, h.monotone⟩) := by
  -- Take `t = ∏ a, s a`, where `s a` is `ϖ⁻¹` from the index `a` on and `1` before it.
  let s (a : Fin N) : dominantTorus (n := Fin N) (F := F) :=
    ⟨fun i ↦ if a ≤ i then ϖ⁻¹ else 1, by
      simp +decide [dominantTorus, Monotone, apply_ite, ite_apply, hϖ]
      lia⟩
  have h_strict : StrictMono fun i : Fin N ↦ v ((∏ a, s a).val i).val := by
    simp [StrictMono, prod_ite, filter_ge_eq_Iic, s, hϖ]
  -- The `U` with zero kernel form a submonoid, so it is enough that each `U (s a)` has zero kernel.
  suffices h_ker :
      ∀ (a : Fin N) (x : levelSpace ρ.ρ proIwahori), iwahoriHeckeHom ρ (s a) x = 0 → x = 0 by
    have h_mem : (∏ a, s a) ∈ (nonZeroSMulDivisors (Module.End ℂ (levelSpace ρ.ρ proIwahori))
        (levelSpace ρ.ρ proIwahori)).comap (iwahoriHeckeHom ρ) := prod_mem fun a _ ↦ h_ker a
    exact ⟨(∏ a, s a).val, h_strict, (injective_iff_map_eq_zero _).mpr h_mem⟩
  intro a x hx
  -- A cyclic permutation makes `s a` an element `n` that normalises `proIwahori`, so `proIwahori`
  -- fixes `y`.
  have hN : NeZero N := a.neZero
  let n : GL (Fin N) F := permGL (finCycle a)⁻¹ * diagGL (s a)
  let y : ρ := ρ n x
  have h_conj (k : GL (Fin N) F) (hk : k ∈ proIwahori) : n⁻¹ * k * n ∈ proIwahori := by
    refine mem_proIwahori_iff_blockParahoric.mpr
      -- The torus element, the permutation and the set are inferred from the goal.
      (conj_monomial_mem_blockParahoric _ _ _ (mem_proIwahori_iff_blockParahoric.mp hk) ?_)
    -- The valuation condition is an inequality between indicator functions on `Fin N`, which
    -- holds for every pair of indices.
    suffices h_ind : ∀ i j : Fin N,
        ((if a ≤ j then 1 else 0) + if j < i then 1 else 0 : ℤ) ≤
          (if a ≤ i then 1 else 0) + if j - a < i - a then 1 else 0 by
      simpa [s, apply_ite Units.val, apply_ite v, apply_ite log, hϖ] using
        fun i j : Fin N ↦ Or.inr (h_ind i j)
    fin_omega
  have hy : y ∈ levelSpace ρ.ρ proIwahori := by
    simpa [y, Representation.inv_apply_eq_iff] using fun k hk ↦ x.prop ⟨_, h_conj k hk⟩
  -- `U (s a) x = 0` says that `P` holds for the inverse of the cycle.
  let φ : Module.End ℂ ρ := compactMean ρ.ρ proIwahori
  let P (σ : Perm (Fin N)) : Prop := φ (ρ (permGL σ⁻¹) y) = 0
  have hx_zero : compactMean ρ.ρ proIwahori (ρ (diagGL (s a)) x) = 0 := congrArg Subtype.val hx
  have h_start : P (finCycle a)⁻¹ := by simpa [P, φ, y, n] using hx_zero
  -- The quadratic relation, with `c = 0`, carries `P` across a transposition that removes an
  -- inversion.
  have h_swap (σ : Perm (Fin N)) (i j : Fin N) (hij : i ⋖ j) (hσ : σ j < σ i) (hP : P σ) :
      P (σ * swap i j) := by
    let z : ρ := ρ (permGL σ⁻¹) y
    let w : Module.End ℂ ρ := ρ (permGL (swap i j))
    have hz : φ z = 0 := hP
    -- a diagonal matrix of units normalises `proIwahori`, so `z` may be replaced by its mean
    have h_diag (t : Fin N → Fˣ) (ht : ∀ i : Fin N, v (t i).val = 1) : φ (ρ (diagGL t) z) = 0 :=
      calc
        _ = φ (ρ (diagGL t) (φ z)) :=
          (map_compactMean_of_factor (fun _ ↦ compactMean_apply) fun k hk ↦
            ⟨k, diagGL_conj_mem_proIwahori_of_v_eq_one hk ht, by simp⟩).symm
        _ = 0 := by simp [hz]
    have h_quad : Nat.card 𝓀[F] • φ (w (φ z)) = φ (w z) + (Nat.card 𝓀[F] - 1) • 0 :=
      quadratic_relation hij 0 (fun _ ↦ compactMean_apply) (transvectionGL_apply_permGL_inv hy hσ)
        fun u hu ↦ h_diag _ (v_mulSingle_neg_inv_mul_mulSingle_eq_one hu)
    -- the left side vanishes by `hz`, so the first term on the right does
    simpa [P, w, z, hz, ← map_inv] using h_quad.symm
  -- Sorting (`exists_antitone_of_swap`) ends at the monotone permutation `σ = 1`, where `P` says
  -- `y = 0`; and `ρ n` is injective.
  obtain ⟨σ, hP, h_anti⟩ := exists_antitone_of_swap toDual P ⟨_, h_start⟩ h_swap
  have hσ_one : σ = 1 := (Perm.monotone_iff σ).mp (antitone_toDual_comp_iff.mp h_anti)
  -- `y` is fixed by `proIwahori`, so it equals its mean, which vanishes by `P 1`.
  have hy_zero : y = 0 := by simpa [P, φ, hσ_one, compactMean_eq_self _ hy] using hP
  exact Subtype.ext ((map_eq_zero_iff (ρ.ρ n) (ρ.ρ.apply_bijective n).injective).mp hy_zero)

variable [CompactSpace 𝒪[F]]

variable {ρ} {y z : ρ} {ξ : (Fin N → Fˣ) →* ℂˣ} {l : ρ →ₗ[ℂ] ℂ} {t : Fin N → Fˣ}
  {K : Subgroup (GL (Fin N) F)} {c : ℕ → ℕ}

/-! ### Exponents -/

/-- An exponent `l` (with character `ξ`) does not change under the mean over `New.proIwahori`:
this is its defining identity at `t = 1`. -/
lemma IsExponent.apply_compactMean (hl : IsExponent ρ ξ l) :
    l (compactMean ρ.ρ proIwahori z) = l z := by simpa using hl (one_mem _) z

/-- An exponent `l` (with character `ξ`) is invariant under `New.proIwahori`:
`l (ρ k z) = l z` for `k` in `New.proIwahori`. -/
lemma IsExponent.apply_proIwahori (hl : IsExponent ρ ξ l) (k : GL (Fin N) F) (hk : k ∈ proIwahori)
    (z : ρ) : l (ρ k z) = l z := by simp [← hl.apply_compactMean, hk]

/-- Let `l` be an exponent with character `ξ`, and let `t` be a diagonal element all of whose
entries are units of the ring of integers. Then `l (ρ(diag t) z) = ξ(t) · l z` for every vector `z`,
so the mean over `New.proIwahori` can be dropped. -/
lemma IsExponent.apply_diagGL_unit (hl : IsExponent ρ ξ l) (ht : ∀ a : Fin N, v (t a).val = 1)
    (z : ρ) : l (ρ (diagGL t) z) = ξ t * l z := by
  -- `t` is dominant and normalises `proIwahori`, so the mean in the eigen-equation `hl` can be
  -- dropped.
  rw [← hl (t := t) fun i j _ ↦ by simp [ht]]
  exact (map_compactMean_of_factor hl.apply_proIwahori fun k hk ↦
    ⟨k, diagGL_conj_mem_proIwahori_of_v_eq_one hk ht, by simp⟩).symm

/-- Let `ρ` be a smooth complex representation of `GL_N(F)`, and let `l` be an exponent with
character `ξ`: `l (ρ(t) (mean of z over New.proIwahori)) = ξ(t) l z` for all vectors `z` and all
dominant diagonal `t`. Let `y` be fixed by a subgroup `K` containing every `g` of
`blockParahoric c` (entries `g i j` in the maximal ideal whenever `c j < c i`) whose diagonal
entries are `≡ 1` mod the maximal ideal; let `σ` be a permutation, `s` a diagonal torus element
and `d` dominant, and suppose that for `σ b < σ a` either `v s_{σ b} ≤ v s_{σ a}`, or `c a ≤ c b`
and `v s_{σ b} ≤ v s_{σ a} · exp 1`. Then at `x = ρ(diagGL s · permGL σ) y` the mean over
`New.proIwahori` can be dropped: `l (ρ(diagGL d) x) = ξ(d) l x`. -/
lemma IsExponent.apply_diagGL_apply_diagGL_mul_permGL (hl : IsExponent ρ ξ l)
    (hy : y ∈ levelSpace ρ.ρ K)
    (hK : ∀ {g : GL (Fin N) F}, g ∈ blockParahoric c ∧ (∀ i : Fin N, v (g i i - 1) < 1) → g ∈ K)
    (σ : Perm (Fin N)) {d s : Fin N → Fˣ} (hd : d ∈ dominantTorus)
    (hs : ∀ a b : Fin N, σ b < σ a → v (s (σ b)).val ≤ v (s (σ a)).val ∨
      c a.val ≤ c b.val ∧ v (s (σ b)).val ≤ v (s (σ a)).val * exp 1) :
    l (ρ (diagGL d) (ρ (diagGL s * permGL σ) y)) = ξ d * l (ρ (diagGL s * permGL σ) y) := by
  -- Write `g ∈ proIwahori` as `u * (u⁻¹ * g)` with `u` upper unitriangular; `d` conjugates `u`
  -- into `proIwahori`, and the lower triangular `u⁻¹ * g` fixes `ρ (diagGL s * permGL σ) y`.
  rw [← hl hd]
  refine (map_compactMean_of_factor hl.apply_proIwahori fun g hg ↦ ?_).symm
  obtain ⟨u, hu, -, h_iw⟩ := exists_iwasawa_bruhat g
  obtain ⟨hu_iw, h_lower⟩ : u ∈ proIwahori ∧ ∀ i j : Fin N, i < j → (u⁻¹ * g) i j = 0 := h_iw hg
  have h_conj : (diagGL s * permGL σ)⁻¹ * (u⁻¹ * g) * (diagGL s * permGL σ) ∈ K := by
    rw [diagGL_mul_permGL]
    refine hK (conj_monomial_mem_blockParahoric _ σ _
      (mem_proIwahori_iff_blockParahoric.mp (mul_mem (inv_mem hu_iw) hg)) ?_)
    intro i j
    rcases lt_trichotomy (σ i) (σ j) with h_lt | h_eq | h_gt
    · -- above the diagonal the entry of the lower triangular `u⁻¹ * g` vanishes
      exact .inl (h_lower (σ i) (σ j) h_lt)
    · -- on the diagonal both sides of the inequality agree
      simp [σ.injective h_eq]
    · -- below the diagonal take `log` of the valuations in `hs` (they are nonzero)
      right
      rcases hs i j h_gt with h_le | ⟨h_c, h_le⟩
      · have h_log : log (v (s (σ j)).val) ≤ log (v (s (σ i)).val) :=
          (log_le_log (by simp) (by simp)).mpr h_le
        grind [id_eq]
      · have h_log : log (v (s (σ j)).val) ≤ log (v (s (σ i)).val) + 1 := by
          simpa [log_mul] using (log_le_log (by simp) (by simp)).mpr h_le
        grind [id_eq]
  have h_fix : ρ (u⁻¹ * g) (ρ (diagGL s * permGL σ) y) = ρ (diagGL s * permGL σ) y := by
    simpa [Representation.inv_apply_eq_iff] using hy ⟨_, h_conj⟩
  exact ⟨u, conj_unitriangular_mem_proIwahori hd ⟨hu, hu_iw⟩, h_fix⟩

/-- The value of an exponent `l` of character `ξ` on monomial translates. Let `y` be fixed by a
subgroup `K` that contains the elements of the parahoric of level function `c` (integral `g` with
`v (g i j) < 1` whenever `c j < c i`) with diagonal entries `≡ 1`. Suppose that for `σ b < σ a`
either `v t_{σ b} ≤ v t_{σ a}`, or `c a ≤ c b` and `v t_{σ b} ≤ v t_{σ a} · exp 1`. Then
`l (ρ(t) ρ(σ) y) = ξ(t) l (ρ(σ) y)`. Here `ϖ` is a uniformiser (`hϖ`). -/
lemma IsExponent.apply_monomial_translate (hϖ : v ϖ.val = exp (-1)) {y : ρ}
    {ξ : (Fin N → Fˣ) →* ℂˣ} {l : ρ →ₗ[ℂ] ℂ} {t : Fin N → Fˣ} {K : Subgroup (GL (Fin N) F)}
    {c : ℕ → ℕ} (hl : IsExponent ρ ξ l) (hy : y ∈ levelSpace ρ.ρ K)
    (hK : ∀ {g : GL (Fin N) F}, g ∈ blockParahoric c ∧ (∀ i : Fin N, v (g i i - 1) < 1) → g ∈ K)
    (σ : Perm (Fin N))
    (ht : ∀ a b : Fin N, σ b < σ a → v (t (σ b)).val ≤ v (t (σ a)).val ∨
      c a.val ≤ c b.val ∧ v (t (σ b)).val ≤ v (t (σ a)).val * exp 1) :
    l (ρ (diagGL t * permGL σ) y) = ξ t * l (ρ (permGL σ) y) := by
  -- Choose `k` with `t₀ ^ k * t` dominant, `t₀` strictly dominant. Drop the mean at
  -- `(d, s) = (t₀ ^ k, t)` and at `(t₀ ^ k * t, 1)`: the left sides agree; cancel `ξ (t₀ ^ k)`.
  let t₀ : Fin N → Fˣ := fun i ↦ ϖ⁻¹ ^ (i : ℕ)
  have ht₀ : StrictMono fun i : Fin N ↦ v (t₀ i).val := fun i j hij ↦ by simpa [t₀, hϖ] using hij
  obtain ⟨k, hk⟩ := (eventually_pow_mul_mem_dominantTorus ht₀ t).exists
  refine mul_left_cancel₀ (ξ (t₀ ^ k)).ne_zero ?_
  calc ξ (t₀ ^ k) * l (ρ (diagGL t * permGL σ) y)
      = l (ρ (diagGL (t₀ ^ k)) (ρ (diagGL t * permGL σ) y)) :=
        (hl.apply_diagGL_apply_diagGL_mul_permGL hy hK σ (pow_mem ht₀.monotone k) ht).symm
    _ = l (ρ (diagGL (t₀ ^ k * t)) (ρ (diagGL 1 * permGL σ) y)) := by simp
    _ = ξ (t₀ ^ k * t) * l (ρ (diagGL 1 * permGL σ) y) :=
        hl.apply_diagGL_apply_diagGL_mul_permGL hy hK σ hk fun a b _ ↦ .inl le_rfl
    _ = ξ (t₀ ^ k) * (ξ t * l (ρ (permGL σ) y)) := by simp [mul_assoc]

end New

end IwahoriInjective
