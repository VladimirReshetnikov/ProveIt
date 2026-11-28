import Lib.Weil.DualPair.MixedModel
import Lib.Weil.Unramified.HeckeTransfer

/-!
# Lagrangians, zero terms of the Weil representation and vanishing of dominated functionals

Let `S` and `T` be hermitian spaces. The two unitary groups act by `New.SiegelWeil.splitWeil S T` on
the function space of `Hom(S, T)`. The file defines complete splittings of `S`, Lagrangians and the
zero term of a Lagrangian: the mean of `θ (ϱ z f)` over the maps `z : S → T` vanishing on it, adelic
modulo rational, where `ϱ z` is the Heisenberg translation by `z`. It computes the norm of the zero
term `P.lagrangian.zeroTerm T` of a splitting `P` under the parabolic, and bounds it along the
normalised torus of a second splitting. It then shows, by the Hecke maximum principle, that a
continuous invariant functional vanishes if it is dominated by the norms of the zero terms of the
vacuum and `rank T > rank S > 0`.

## Main definitions and results

* `New.SiegelWeil.CompleteSplitting S p`: splittings of `S` into `p` hyperbolic planes;
  `New.SiegelWeil.Lagrangian S`: Lagrangians. Every Lagrangian comes from a splitting
  (`New.SiegelWeil.Lagrangian.exists_completeSplitting`), and one is chosen for each
  (`New.SiegelWeil.Lagrangian.chosenSplitting`).
* `New.SiegelWeil.mixedValue`, `New.SiegelWeil.Lagrangian.zeroTerm`: the value `f[x]` in the model
  of a splitting, and the zero term `f[0]` of a Lagrangian, which depends on the Lagrangian only
  (`New.SiegelWeil.zeroTerm_lagrangian_eq_theta`).
* `New.SiegelWeil.theta_normalisedTorus_le`: if `rank T > rank S`, an integrable bound for theta,
  uniform along the torus `New.SiegelWeil.normalisedTorus`.
* `New.SiegelWeil.norm_zeroTerm_parabolic_mul`: an element `g` with `g k = k a` multiplies the norm
  of the zero term by `√|det a| ^ rank T`.
* `New.SiegelWeil.exists_zeroTerm_normalisedTorus_le`: an upper bound, along the normalised torus
  `New.SiegelWeil.normalisedTorus T P x`, for the zero term of a second splitting.
* `New.SiegelWeil.eq_zero_of_le_tsum_zeroTerm`: let `S` have even positive rank less than that of
  `T`, with summable zero terms. A continuous functional `ℓ` that is invariant under the group of
  `T` and is dominated, up to an additive constant, by the sum of the norms of the zero terms of the
  translated vacuum is zero.

Notions from other files:
* `New.pairWeil`: the representation `(g, h) ↦ a (det h) b (det g)⁻¹ ω (x ↦ h x g⁻¹)` of the product
  of the two adelic unitary groups on the function space of `Hom(S, T)`.
* `New.Space.Splitting.homSource`, `New.Space.Splitting.homSlice`: the splitting of `Hom(S, T)` over
  `Hom(S₁, T)` induced by a splitting of `S` over `S₁`, and the term `f ↦ f[x]` of its mixed model
  at an adelic matrix `x`.
* `New.Space.schrodingerOp`: the operator on `𝒮 V` attached to a function `Ψ` above a set of split
  places; the indicator `New.boxIndicator` gives the projection `New.Space.projOn` on the vacua
  there.

## Relation to the literature

Known; see `Lib.SiegelWeil.Formula.WeilRange` for sources.
-/

noncomputable section

/-!
## Splittings, Lagrangians and zero terms

A splitting `D : S.Splitting S₁ p` consists of dual isotropic frames `D.k`, `D.l` and an isometry
`D.i` from `S₁` to their complement; `θ _` on the space of rank zero turns a vector into a number.
-/

section Lagrangians

namespace New.SiegelWeil

open Matrix WeilData Space Splitting ENNReal Fintype Filling Subsingleton New.Core MeasureTheory

variable {E n m n₁ r : Type} [Field E] [CMType E] [WeilData E] [Fintype n] [DecidableEq n]
  [Fintype m] [DecidableEq m] [Fintype n₁] [DecidableEq n₁] [Fintype r] [DecidableEq r]
  {s : n → ℤˣ} {t : m → ℤˣ} {s₁ : n₁ → ℤˣ} (S : Space E n s) {S₁ : Space E n₁ s₁} (T : Space E m t)
  (p : Type) [Fintype p] [DecidableEq p]

/-- The type of splittings of `S` into `p` hyperbolic planes with zero-dimensional complement, that
is, of decompositions `S = l E ^ p ⊕ k E ^ p` with dual isotropic frames `l`, `k`. -/
abbrev CompleteSplitting : Type := S.Splitting (stdSpace E Empty) p

/-- The Weil representation of the pair `(S, T)` on the function space of `Hom(S, T)`, twisted by
the character `upsilonU1 ^ (n / 2)` of `det h`, where `n` is the rank of `S` and `n / 2` is rounded
down. In `splitWeil S T (g, h)` the element `g` is in the group of `S` and `h` in that of `T`. For
split `S` this twist makes the group of `T` act on slices by substitution alone
(`New.SiegelWeil.mixedValue_splitWeil`). -/
abbrev splitWeil : G E s × G E t →* 𝒮 (S.hom T) →L[ℂ] 𝒮 (S.hom T) :=
  pairWeil S T (1 * upsilonU1 ^ (card n / 2)) 1

/-- The type of Lagrangians of `S`: subspaces `L` of `E ^ n` that are equal to their own orthogonal
complement for the form `x* J y` of `S`. -/
abbrev Lagrangian : Type :=
  {L : Submodule E (n → E) // ∀ y : n → E, y ∈ L ↔ ∀ x ∈ L, star x ⬝ᵥ S.J *ᵥ y = 0}

variable {S p} (D₁ : S.Splitting S₁ r) {A : Matrix n r E}

lemma homSlice_zero : D₁.homSlice T 0 = (D₁.homSource T).zeroTerm := by
  ext
  simp [homSlice]

attribute [scoped simp] homSlice_zero

omit [WeilData E] [DecidableEq n] in
@[local simp↓]
lemma forall_colSpan_dot_eq_zero_iff {y : n → E} :
    (∀ x ∈ colSpan A, star x ⬝ᵥ y = 0) ↔ Aᴴ *ᵥ y = 0 := by
  refine ⟨fun h ↦ funext fun j ↦ h (A.col j) ⟨Pi.single j 1, A.mulVec_single_one j⟩, ?_⟩
  rintro h _ ⟨a, rfl⟩
  simp [star_mulVec_dotProduct, h]

/-- Let `D₁` be a splitting of `S` over `S₁`, with isotropic frame `k` and embedding `i` of `S₁`.
Every vector orthogonal to the columns of `k` has the form `k a + i w`. -/
lemma exists_mulVec_add_mulVec_of_orthogonal (y : n → E) (hy : D₁.kᴴ *ᵥ S.J *ᵥ y = 0) :
    ∃ (a : r → E) (w : n₁ → E), D₁.k *ᵥ a + D₁.i *ᵥ w = y := by
  -- The frame `(l, k, i)` has an invertible Gram matrix and is square, so it spans. Write
  -- `y = l b + k a + i w`; orthogonality to `k` gives `b = 0`.
  let M : Matrix n ((r ⊕ r) ⊕ n₁) E := fromCols (fromCols D₁.l D₁.k) D₁.i
  have h_gram : IsUnit (Mᴴ * S.J * M) := by simp only [M, D₁.gram_eq_hyperbolicSum, isUnit_J]
  obtain ⟨X, hXM⟩ : HasLeftInv M := .of_isUnit_gram h_gram
  have hMX : M * X = 1 :=
    (mul_eq_one_comm_of_card_eq _ _ _ (by simp +arith [D₁.card_eq])).1 hXM
  obtain ⟨b, a, w, rfl⟩ :
      ∃ (b a : r → E) (w : n₁ → E), D₁.l *ᵥ b + D₁.k *ᵥ a + D₁.i *ᵥ w = y := by
    have h_span : M *ᵥ X *ᵥ y = y := by rw [mulVec_mulVec, hMX, one_mulVec]
    rw [fromCols_mulVec, fromCols_mulVec] at h_span
    exact ⟨(X *ᵥ y) ∘ .inl ∘ .inl, (X *ᵥ y) ∘ .inl ∘ .inr, (X *ᵥ y) ∘ .inr, h_span⟩
  have hb : b = 0 := by simpa [mulVec_add, ← Matrix.mul_assoc] using hy
  exact ⟨a, w, by simp [hb]⟩

variable (P : CompleteSplitting S p) (L : Lagrangian S) (γ : U S.J) (x : p → ℕ)

/-- For a complete splitting `P` of `S` and an adelic matrix `x`, the continuous functional
`f ↦ f[x]`: the slice of `f` at `x`, which is a number, the value at `x` in the Schrödinger model
attached to `P`. -/
def mixedValue (x : Matrix m p (𝔸 E)) : 𝒮 (S.hom T) →L[ℂ] ℂ :=
  θ ((stdSpace E Empty).hom T) ∘L P.homSlice T x

/-- The Lagrangian `k E ^ p` spanned by the columns of the frame `k` of a complete splitting `P`. -/
def CompleteSplitting.lagrangian : Lagrangian S :=
  ⟨colSpan P.k, by simpa [iff_def, forall_and, eq_zero P.i] using
                     exists_mulVec_add_mulVec_of_orthogonal P⟩

omit [WeilData E] in
lemma Lagrangian.eq_of_le {L L' : Lagrangian S} (h_le : L.val ≤ L') : L = L' :=
  Subtype.ext (h_le.antisymm fun y hy ↦
    (L.property y).2 fun x hx ↦ (L'.property y).1 hy x (h_le hx))

open Lagrangian CompleteSplitting

/-- Every Lagrangian `L` of `S` is the span of the isotropic frame `k` of a splitting `P` of `S`
into `r` hyperbolic planes, for some natural number `r`. -/
lemma Lagrangian.exists_completeSplitting (L : Lagrangian S) :
    ∃ (r : ℕ) (P : CompleteSplitting S (Fin r)), P.lagrangian = L := by
  -- Extend a basis `k` of `L` to a splitting `S = ⟨k, l⟩ ⊥ V`. The space `V` is orthogonal to
  -- `L`, so lies in `L`; then its invertible Gram matrix is zero, and `V` has rank zero.
  obtain ⟨k, k_linv, k_range⟩ := exists_hasLeftInv_colSpan_eq L.val
  have mem_iff {y : n → E} : y ∈ colSpan k ↔ (kᴴ * S.J) *ᵥ y = 0 := by
    rw [← mulVec_mulVec, ← forall_colSpan_dot_eq_zero_iff, k_range]
    exact L.property y
  have isotropic : kᴴ * S.J * k = 0 :=
    ext_col fun j ↦ mem_iff.1 ⟨Pi.single j 1, k.mulVec_single_one j⟩
  obtain ⟨d, ε, V, D, rfl⟩ := S.exists_splitting k_linv isotropic
  cases d with
  | zero =>
    let P : CompleteSplitting S (Fin (Module.finrank E L.val)) := by
      use D.k, D.l, 0 <;> simp [D.card_eq, ← ext_iff]
    exact ⟨Module.finrank E L.val, P, Subtype.ext k_range⟩
  | succ d =>
    obtain ⟨c, hc⟩ : ∃ c, D.k * c = D.i :=
      exists_mul_eq_of_col_mem_range fun j ↦ mem_iff.2 (congrArg (col · j) D.gram_ki)
    have h_zero : V.J = 0 :=
      calc V.J = D.iᴴ * S.J * (D.k * c) := by rw [hc, D.gram_ii]
        _ = 0 := by rw [← Matrix.mul_assoc, D.gram_ik, Matrix.zero_mul]
    exact absurd h_zero V.isUnit_J.ne_zero

/-- A natural number `r` and a splitting of `S` into `r` hyperbolic planes whose isotropic frame `k`
spans the Lagrangian `L`, chosen once. -/
def Lagrangian.completeSplitting :
    {P : Σ r : ℕ, CompleteSplitting S (Fin r) // P.snd.lagrangian = L} :=
  Nonempty.some <| by
    obtain ⟨r, P, hP⟩ := L.exists_completeSplitting
    exact ⟨⟨r, P⟩, hP⟩

/-- The number of hyperbolic planes in the splitting chosen for the Lagrangian `L`. -/
abbrev Lagrangian.numPlanes : ℕ := L.completeSplitting.val.fst

/-- The complete splitting of `S` chosen for the Lagrangian `L`; its frame `k` spans `L`
(`New.SiegelWeil.Lagrangian.lagrangian_chosenSplitting`). -/
abbrev Lagrangian.chosenSplitting : CompleteSplitting S (Fin L.numPlanes) :=
  L.completeSplitting.val.snd

lemma Lagrangian.lagrangian_chosenSplitting (L : Lagrangian S) :
    L.chosenSplitting.lagrangian = L :=
  L.completeSplitting.property

/-- The zero term along a Lagrangian `L`: the value at `0` in the Schrödinger model of the chosen
complete splitting `L.chosenSplitting`, whose frame `k` spans `L`. It sends `f` to the mean of
`θ (ϱ z f)` over the maps `z : S → T` that vanish on `L`, adelic modulo rational
(`New.Space.Splitting.zeroTerm_apply`). -/
def Lagrangian.zeroTerm : 𝒮 (S.hom T) →L[ℂ] ℂ := mixedValue T L.chosenSplitting 0

/-- For a complete splitting `P` of `S`, the zero term along its Lagrangian is the value `f[0]` in
the Schrödinger model of `P`, so it does not depend on the splitting chosen. Here `P.homSource T` is
the induced splitting of `Hom(S, T)`, and `θ` on the space of rank zero turns a vector into a
number. -/
lemma zeroTerm_lagrangian_eq_theta (f : 𝒮 (S.hom T)) :
    P.lagrangian.zeroTerm T f = θ ((stdSpace E Empty).hom T) ((P.homSource T).zeroTerm f) := by
  -- The frame `P.k` lies in the span of the chosen frame `Q.k`, so is orthogonal to it.
  let Q : CompleteSplitting S (Fin P.lagrangian.numPlanes) := P.lagrangian.chosenSplitting
  have hQ : Q.lagrangian = P.lagrangian := P.lagrangian.lagrangian_chosenSplitting
  obtain ⟨c, hc⟩ : ∃ c, Q.k * c = P.k := exists_mul_eq_of_col_mem_range fun j ↦
    (congrArg Subtype.val hQ).ge ⟨Pi.single j 1, mulVec_single_one P.k j⟩
  have h_orth : Q.kᴴ * S.J * P.k = 0 := by simp [← hc, ← Matrix.mul_assoc]
  have h_congr : (Q.homSource T).zeroTerm = (P.homSource T).zeroTerm :=
    P.zeroTerm_homSource_congr T h_orth (Subsingleton.elim Q.i P.i)
  change mixedValue T Q 0 f = _
  simp [mixedValue, h_congr]

/-- For a rational isometry `γ` of `S`, the splitting of `S` with no hyperbolic planes whose
complement is `S` itself, mapped in by `γ`. -/
def isometrySplitting : S.Splitting S Empty := by
  use 0, 0, γ <;> simp [↓← mem_U, ← ext_iff]

/-- For a rational isometry `γ` of `S`, the zero term on `Hom(S, T)` of the splitting without planes
given by `γ` is the Weil operator of `(γ⁻¹, 1)`, where `S.ratEmbed` embeds the rational points. -/
lemma zeroTerm_isometrySplitting (f : 𝒮 (S.hom T)) :
    ((isometrySplitting γ).homSource T).zeroTerm f = splitWeil S T (S.ratEmbed γ⁻¹, 1) f := by
  -- A rational point acts by a change of variables, and the mean in `zeroTerm` is over a point.
  have h_iCoord : (isometrySplitting γ).iCoord = (S.ratEmbed γ⁻¹).adeleMatrix := by
    rw [map_inv, G.adeleMatrix_inv, iCoord,
      show (isometrySplitting γ).iAdelic = (S.ratEmbed γ).adeleMatrix from rfl]
  ext y
  rw [Splitting.zeroTerm_apply, pairWeil_of_mem_Gamma S T _ _ (by simp [Γ]) (one_mem _),
    homSource_iAdelic, h_iCoord, eq_zero (kAdelic _)]
  simp

/-- Let `P` be a complete splitting of `S` with frame `k` and `γ` a rational isometry. The zero term
along the Lagrangian spanned by `γ k`, that of the splitting `P` moved by `γ`, is the zero term
along the Lagrangian of `P` taken after the Weil operator of `(γ⁻¹, 1)`. -/
lemma zeroTerm_lagrangian_isometrySplitting_comp (f : 𝒮 (S.hom T)) :
    (lagrangian ((isometrySplitting γ).comp P)).zeroTerm T f =
      P.lagrangian.zeroTerm T (splitWeil S T (S.ratEmbed γ⁻¹, 1) f) := by
  rw [zeroTerm_lagrangian_eq_theta, zeroTerm_homSource_comp, zeroTerm_lagrangian_eq_theta,
    ← zeroTerm_isometrySplitting]

/-- For a complete splitting `P` of `S` and an isotropic frame `A` with a left inverse, some
rational isometry `γ` makes the columns of `γ P.k` orthogonal to those of `A`. -/
lemma exists_isometry_orthogonal (hA : HasLeftInv A) (h_isotropic : Aᴴ * S.J * A = 0) :
    ∃ γ : U S.J, Aᴴ * S.J * (γ.val.val * P.k) = 0 := by
  -- `A` extends to a splitting of `S`, which has rank `2 * card p`.
  have card_le : card r ≤ card p := by
    obtain ⟨d, ε, V, D, -⟩ := S.exists_splitting hA h_isotropic
    have hP : card n = 2 * card p := by simpa using P.card_eq
    linarith [D.card_eq]
  obtain ⟨ι⟩ : Nonempty (r ↪ p) := Function.Embedding.nonempty_of_card_le card_le
  -- By Witt's theorem some `γ` takes the columns `ι` of the isotropic frame `P.k` to `A`.
  let k' : Matrix n r E := P.k.submatrix id ι
  have h_linv : (P.lᴴ * S.J).submatrix ι id * k' = 1 := (show
    (P.lᴴ * S.J * P.k).submatrix ι ι = 1 by simp)
  have h_orth : k'ᴴ * S.J * P.k = 0 := (show (P.kᴴ * S.J * P.k).submatrix ι id = 0 by simp)
  have h_gram : k'ᴴ * S.J * k' = 0 := (show (P.kᴴ * S.J * P.k).submatrix ι ι = 0 by simp)
  obtain ⟨γ, hγ⟩ : ∃ γ : U S.J, γ.val.val * k' = A :=
    S.witt ⟨_, h_linv⟩ hA (h_gram.trans h_isotropic.symm)
  exact ⟨γ, by rw [← hγ, U.gram_invariant, h_orth]⟩

/-- Let `D₁` split `S` over `S₁`, and let `L` be a Lagrangian of `S` that contains the columns of
`D₁.k`. The preimage of `L` under the embedding `D₁.i` is its own orthogonal complement in `S₁`. -/
lemma mem_comap_iff_forall_dot_eq_zero {L : Lagrangian S} (hL : colSpan D₁.k ≤ L) (y : n₁ → E) :
    y ∈ L.val.comap D₁.i.mulVecLin ↔
      ∀ x ∈ L.val.comap D₁.i.mulVecLin, star x ⬝ᵥ S₁.J *ᵥ y = 0 := by
  have h_isometry (a : r → E) (w : n₁ → E) :
      star (D₁.k *ᵥ a + D₁.i *ᵥ w) ⬝ᵥ S.J *ᵥ D₁.i *ᵥ y = star w ⬝ᵥ S₁.J *ᵥ y := by
    simp [star_mulVec_dotProduct, ← Matrix.mul_assoc]
  rw [Submodule.mem_comap, mulVecLin_apply, L.property]
  refine ⟨fun h w hw ↦ by simpa [← h_isometry 0 w] using h (D₁.i *ᵥ w) hw, fun h x hx ↦ ?_⟩
  -- A vector of `L` is orthogonal to `k`, so is `k a + i w`, and `i w` lies in `L`.
  have h_orth : D₁.kᴴ *ᵥ S.J *ᵥ x = 0 :=
    forall_colSpan_dot_eq_zero_iff.1 fun z hz ↦ (L.property x).1 hx z (hL hz)
  obtain ⟨a, w, rfl⟩ := exists_mulVec_add_mulVec_of_orthogonal D₁ x h_orth
  have hw : D₁.i *ᵥ w ∈ L.val := (add_mem_cancel_left (hL ⟨a, rfl⟩)).1 hx
  rw [h_isometry, h w hw]

/-- Let `D₁` be a Witt decomposition `S = (l E^r ⊕ k E^r) ⊥ S₁` with isotropic frame `D₁.k`. The
Lagrangians of `S₁` are in bijection with the Lagrangians of `S` that contain the columns of `D₁.k`.
The zero term of the image is the zero term in `S₁` composed with the zero term
`𝒮(Hom(S,T)) → 𝒮(Hom(S₁,T))` along the induced splitting `D₁.homSource T`. Here the zero term along
`L` sends `f` to the mean of `θ(ϱ z f)` over the maps `z` vanishing on `L`, adelic modulo
rational. -/
lemma exists_lagrangian_equiv_containing :
    ∃ σ : Lagrangian S₁ ≃ {L : Lagrangian S // colSpan D₁.k ≤ L},
      ∀ (L : Lagrangian S₁) (f : 𝒮 (S.hom T)),
        Lagrangian.zeroTerm T (σ L) f = Lagrangian.zeroTerm T L ((D₁.homSource T).zeroTerm f) := by
  -- A Lagrangian `L₁` of `S₁` goes to the span of `k` and `i L₁`; a Lagrangian `L` that contains
  -- `k` goes back to its preimage under `i`.
  let up (L : Lagrangian S₁) : Lagrangian S := lagrangian (D₁.comp L.chosenSplitting)
  let down (L : {L : Lagrangian S // colSpan D₁.k ≤ L}) : Lagrangian S₁ :=
    ⟨L.val.val.comap D₁.i.mulVecLin, mem_comap_iff_forall_dot_eq_zero D₁ L.property⟩
  have mem_up (L : Lagrangian S₁) (y : n → E) :
      y ∈ (up L).val ↔ ∃ a : r → E, ∃ w ∈ L.val, D₁.k *ᵥ a + D₁.i *ᵥ w = y := by
    conv_rhs => rw [← L.lagrangian_chosenSplitting]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x ∘ .inl, _, ⟨x ∘ .inr, rfl⟩, by simp [Splitting.comp]⟩
    · rintro ⟨a, _, ⟨b, rfl⟩, rfl⟩
      exact ⟨a ⊕ᵥ b, by simp [Splitting.comp]⟩
  have le_up (L : Lagrangian S₁) : colSpan D₁.k ≤ up L :=
    fun _ ⟨a, ha⟩ ↦ (mem_up L _).2 ⟨a, 0, zero_mem _, by simpa using ha⟩
  have down_up (L : Lagrangian S₁) : down ⟨up L, le_up L⟩ = L :=
    (eq_of_le fun w hw ↦ (mem_up L (D₁.i *ᵥ w)).2 ⟨0, w, hw, by simp⟩).symm
  have up_down (L : {L : Lagrangian S // colSpan D₁.k ≤ L}) : up (down L) = L :=
    eq_of_le fun y hy ↦ by
      obtain ⟨a, w, hw, rfl⟩ := (mem_up (down L) y).1 hy
      exact add_mem (L.property ⟨a, rfl⟩) hw
  refine ⟨⟨fun L ↦ ⟨up L, le_up L⟩, down, down_up, fun L ↦ Subtype.ext (up_down L)⟩, fun L f ↦ ?_⟩
  -- The zero term of the composite splitting is taken in two stages.
  change (lagrangian (D₁.comp L.chosenSplitting)).zeroTerm T f = _
  rw [zeroTerm_lagrangian_eq_theta, zeroTerm_homSource_comp]
  simp [Lagrangian.zeroTerm, mixedValue]

/-- Let `P.levi (a, 1)` be the Levi element that acts on the frame `P.k` by `a`, and let `h` be in
the group of `T`. In the Schrödinger model of `P` the pair acts by
`f[x] ↦ χ (det a)⁻¹ √|det a| ^ rank T f[h⁻¹ x a]`, where `χ = AutChar.spaceChar 1 (rank T)` is
a unitary character of the ideles, `|·|` is `ideleAbs` and `h⁻¹.adeleMatrix` is the matrix of
`h⁻¹`. -/
lemma mixedValue_splitWeil_levi (a : GL p (𝔸 E)) (h : G E t) (x : Matrix m p (𝔸 E))
    (f : 𝒮 (S.hom T)) :
    mixedValue T P x (splitWeil S T (P.levi (a, 1), h) f) =
      (((AutChar.spaceChar 1 (card m)).val a.det : ℂ)⁻¹ * √(ideleAbs a.det) ^ card m) *
        mixedValue T P (h⁻¹.adeleMatrix * x * a.val) f := by
  -- The complement of `P` has rank zero, so `h` acts trivially on its function space.
  have h_trivial (φ : 𝒮 ((stdSpace E Empty).hom T)) :
      pairWeil (stdSpace E Empty) T 1 1 (1, h) φ = φ := by
    simp [pairWeil, eq_one (G.onHom _)]
  simp only [mixedValue, splitWeil, ContinuousLinearMap.comp_apply, homSlice_levi, h_trivial,
    show card n / 2 = card p by simp [P.card_eq], map_smul, smul_eq_mul]

/-- The group of `T` acts in the Schrödinger model by substitution:
`(splitWeil S T (1, h) f)[x] = f[h⁻¹ x]`, where `f[x] = mixedValue T P x f`. -/
lemma mixedValue_splitWeil (h : G E t) (x : Matrix m p (𝔸 E)) (f : 𝒮 (S.hom T)) :
    mixedValue T P x (splitWeil S T (1, h) f) = mixedValue T P (h⁻¹.adeleMatrix * x) f := by
  simpa [Prod.mk_one_one] using mixedValue_splitWeil_levi T P 1 h x f

/-- The theta function in the Schrödinger model of `P`: `θ (splitWeil S T (1, h) f)` is the sum of
the slices `f[h⁻¹ ξ]` over the rational matrices `ξ`, which `T.x⁻¹` puts in standard coordinates. -/
lemma hasSum_mixedValue_theta_splitWeil (h : G E t) (f : 𝒮 (S.hom T)) :
    HasSum (fun ξ : Matrix m p E ↦ mixedValue T P (h⁻¹.adeleMatrix * (T.x⁻¹.val * ξ.map toAdele)) f)
      (θ (S.hom T) (splitWeil S T (1, h) f)) := by
  simp only [← mixedValue_splitWeil]
  exact P.hasSum_theta_homSlice T _

/-- For `x : p → ℕ`, the operator `2 ^ (-d * rank T * ∑ i, x i) • splitWeil S T (P.levi (δ, 1), 1)`,
where `d` is the number of infinite places and `δ = New.Core.dyadicDiag x` is diagonal with entries
`2 ^ x i` at the infinite places and `1` at the finite places. -/
def normalisedTorus : 𝒮 (S.hom T) →L[ℂ] 𝒮 (S.hom T) :=
  (((2 ^ Core.numInfPlaces E) ^ ∑ i : p, x i) ^ card m : ℂ)⁻¹ •
    splitWeil S T (P.levi (dyadicDiag (x ·), 1), 1)

/-- For a complete splitting `P` of `S`, the normalised torus operator `normalisedTorus T P x` on
the function space of `Hom(S, T)` is the identity at `x = 0`. -/
@[simp]
lemma normalisedTorus_zero : normalisedTorus T P 0 = 1 := by
  simp [normalisedTorus, dyadicDiag, ← Pi.one_def, Prod.mk_one_one]

/-- The normalising factor of `normalisedTorus T P x` cancels `√|det δ| ^ rank T` for
`δ = New.Core.dyadicDiag x`: the value at `y` of the image of `f` has the norm of `f[y δ]`. -/
lemma norm_mixedValue_normalisedTorus (y : Matrix m p (𝔸 E)) (f : 𝒮 (S.hom T)) :
    ‖mixedValue T P y (normalisedTorus T P x f)‖ =
      ‖mixedValue T P (y * (dyadicDiag fun i : p ↦ x i : GL p (𝔸 E)).val) f‖ := by
  simp [normalisedTorus, mixedValue_splitWeil_levi, ideleAbs_det_dyadicDiag_natCast,
    Real.sqrt_sq_eq_abs, Circle.norm_coe, field]

/-- Let `P` be a complete splitting of `S` into `p` planes and let the rank of `T` exceed `2 p`.
There is a measurable function `N` on the group of `T`, with finite integral for `T.quotMeasure`
(the measure that computes integrals over the quotient by the rational points), such that the theta
functional `θ` satisfies `‖θ (splitWeil S T (1, h) (A x f))‖ ≤ N h * ‖f‖` for all `h`, `f` and
`x : p → ℕ`, where `A x = normalisedTorus T P x`. At `x = 0` this is the convergence of the theta
integral in the Siegel–Weil formula; the bound is uniform in the torus element.

Compare Weil's convergence criterion for the theta integral of a unitary dual pair; the hypothesis
here, that `T` has rank above `2 p`, is stronger than Weil's condition on the Witt index of `T`. -/
lemma theta_normalisedTorus_le (hm : 2 * card p < card m) :
    ∃ N : G E t → ℝ≥0∞,
      Measurable N ∧
      ∫⁻ h : G E t, N h ∂T.quotMeasure ≠ ⊤ ∧
      ∀ (h : G E t) (x : p → ℕ) (f : 𝒮 (S.hom T)),
        ‖θ (S.hom T) (splitWeil S T (1, h) (normalisedTorus T P x f))‖ₑ ≤ N h * ‖f‖ₑ := by
  -- Expand `θ` as a sum over rational matrices `ξ`. The term of `ξ` is read at `pt ξ = h⁻¹ ξ δ`
  -- with `δ = dyadicDiag x`, so `exists_tsum_slice_le` bounds the sum by `M * ‖f‖` times the
  -- number of `ξ` with `pt ξ` in a compact set `Ω`. For these, `h⁻¹ ξ` lies in a compact set `B`
  -- independent of `x`.
  obtain ⟨Ω, hΩ, M, hM⟩ :
      ∃ Ω : Set (m × p → 𝔸 E), IsCompact Ω ∧ ∃ M : NNReal,
        ∀ {ι : Type} [AddGroup ι] (φ : ι →+ m × p → 𝔸 E) (f : 𝒮 (S.hom T)),
          ∑' ξ : ι, ‖(P.homSource T).slice (φ ξ) f‖ₑ ≤ (φ ⁻¹' Ω).encard * M * ‖f‖ₑ :=
    (P.homSource T).exists_tsum_slice_le
  let B : Set (Matrix m p (𝔸 E)) := (fun (a, (c : Matrix p p (𝔸 E))) ↦ vecToMatrix a * c) ''
    Ω ×ˢ (Metric.closedBall 0 1 ×ˢ Ô E : Set (𝔸 E)).matrix
  have hB : IsCompact B :=
    (hΩ.prod isCompact_closedBall_prod_integral.matrix).image (by fun_prop [vecToMatrix])
  let near (h : G E t) : Set (Matrix m p E) :=
    {ξ | (T.toRatCoords h).val⁻¹.val * ξ.map toAdele ∈ B}
  have meas_mem (ξ : Matrix m p E) : MeasurableSet {h : G E t | ξ ∈ near h} :=
    (hB.isClosed.preimage_of_continuous
      (f := fun h : G E t ↦ T.x.val * (h⁻¹.adeleMatrix * T.x⁻¹.val) * ξ.map toAdele)).measurableSet
  have meas : Measurable fun h : G E t ↦ ((near h).encard : ℝ≥0∞) :=
    .comp .of_discrete (measurable_encard.comp (measurable_pi_iff.2 fun ξ ↦ (meas_mem ξ).mem))
  refine ⟨fun h ↦ (near h).encard * (‖θ ((stdSpace E Empty).hom T)‖ₑ * M), meas.mul_const _, ?_,
    fun h x f ↦ ?_⟩
  · -- The count has a finite integral by reduction theory; here the rank condition is used.
    rw [lintegral_mul_const _ meas]
    exact mul_ne_top (T.lintegral_encard_ne_top hB fun _ ↦ hm) coe_ne_top
  let δ : GL p (𝔸 E) := dyadicDiag (x ·)
  let pt : Matrix m p E →+ m × p → 𝔸 E :=
    .mk' (fun ξ ↦ matrixToVec ((T.toRatCoords h).val⁻¹.val * ξ.map toAdele * δ.val))
      (by simp [Matrix.map_add, Matrix.mul_add, Matrix.add_mul])
  -- The inverse of `δ` lies in the unit box.
  have preimage_sub : pt ⁻¹' Ω ⊆ near h :=
    fun ξ hξ ↦ ⟨(pt ξ, δ⁻¹.val), ⟨hξ, dyadicDiag_inv_mem x⟩, by simp [pt]⟩
  have term_eq (ξ : Matrix m p E) :
      ‖mixedValue T P (h⁻¹.adeleMatrix * (T.x⁻¹.val * ξ.map toAdele)) (normalisedTorus T P x f)‖ₑ =
        ‖θ ((stdSpace E Empty).hom T) ((P.homSource T).slice (pt ξ) f)‖ₑ := by
    have h_point : h⁻¹.adeleMatrix * (T.x⁻¹.val * ξ.map toAdele) * δ.val =
        T.x⁻¹.val * ((T.toRatCoords h).val⁻¹.val * ξ.map toAdele * δ.val) := by
      simp [toRatCoords, G.adeleMatrix, ← Matrix.mul_assoc]
    rw [← ofReal_norm, norm_mixedValue_normalisedTorus, ofReal_norm, h_point, mixedValue,
      ContinuousLinearMap.comp_apply, homSlice_eq_slice, AddMonoidHom.mk'_apply]
  calc _ ≤ ∑' ξ, ‖θ ((stdSpace E Empty).hom T) ((P.homSource T).slice (pt ξ) f)‖ₑ := by
        grw [← (hasSum_mixedValue_theta_splitWeil T P h _).tsum_eq, enorm_tsum_le_tsum_enorm]
        exact (tsum_congr term_eq).le
    _ ≤ ‖θ ((stdSpace E Empty).hom T)‖ₑ * ((pt ⁻¹' Ω).encard * M * ‖f‖ₑ) := by
        grw [← hM pt, ← ENNReal.tsum_mul_left, ← ContinuousLinearMap.le_opENorm]
    _ ≤ (near h).encard * (‖θ ((stdSpace E Empty).hom T)‖ₑ * M) * ‖f‖ₑ := by
        grw [Set.encard_mono preimage_sub]
        exact le_of_eq (by ring)

end New.SiegelWeil

end Lagrangians

/-!
## Size of the zero term under the parabolic and along the torus

The tool is the Iwasawa decomposition. `P.kAdelic` is the frame `k` in adelic coordinates,
`New.Core.dyadicDiag x` is the diagonal matrix with `2 ^ x i` at the infinite places and `1` at the
finite ones, and `New.Core.numInfPlaces E` is the number of infinite places.
-/

namespace New.SiegelWeil

open Matrix Fintype Space Splitting New.Core Real ContinuousLinearMap G Subsingleton

variable {E n m p r : Type} [Field E] [CMType E] [WeilData E] [Fintype n] [DecidableEq n]
  [Fintype m] [DecidableEq m] [Fintype p] [DecidableEq p] [Fintype r] [DecidableEq r]
  {s : n → ℤˣ} {t : m → ℤˣ} {S : Space E n s} {T : Space E m t} {P : CompleteSplitting S p}
  (P' : CompleteSplitting S r)

/-- Let `P` be a complete splitting of `S` with isotropic frame `k`. If `g` acts on the frame by
`a`, that is `g k = k a`, then a left factor `g` multiplies the norm of the zero term along the
Lagrangian of `P` by `√|det a| ^ card m`, where `card m` is the rank of `T`. -/
lemma norm_zeroTerm_parabolic_mul {g : G E s} {a : GL p (𝔸 E)} (hk : P.ActsOnFrame g a.val)
    (g' : G E s) (f : 𝒮 (S.hom T)) :
    ‖P.lagrangian.zeroTerm T (splitWeil S T (g * g', 1) f)‖ =
      √(ideleAbs a.det) ^ card m * ‖P.lagrangian.zeroTerm T (splitWeil S T (g', 1) f)‖ := by
  -- The complement of `P` has rank zero, so the block of `g` on it is `1`. Hence `g` multiplies
  -- the zero term by `√|det a| ^ card m` and a character of norm one.
  have h_scale (φ : 𝒮 (S.hom T)) : (P.homSource T).zeroTerm (splitWeil S T (g, 1) φ) =
      (((AutChar.spaceChar 1 (card m)).val a.det : ℂ)⁻¹ * √(ideleAbs a.det) ^ card m) •
        (P.homSource T).zeroTerm φ := by
    rw [splitWeil, show card n / 2 = card p by simp [P.card_eq],
      P.homSource_zeroTerm_pairWeil T 1 1 g 1 a hk (Subsingleton.elim _ _)]
    simp [Prod.mk_one_one]
  rw [← Prod.mk_one_mul_mk_one, ← rep_apply_apply, zeroTerm_lagrangian_eq_theta,
    zeroTerm_lagrangian_eq_theta, h_scale]
  simp [Circle.norm_coe, abs_of_nonneg]

/-- Let `D` split `V` completely (`V₀` has rank zero). For every `g`, the slice `D.slice x` of
`ω(g) vac` is the vacuum of `V₀` times a nonzero constant `c`, the standard additive character at
`-xᴴ z x / 2` for a hermitian matrix `z`, and `‖vacuumFn (γᴴ x)‖ ^ 2` for an invertible matrix `γ`;
the last factor is a Gaussian times the indicator of a lattice. -/
lemma _root_.New.Space.Splitting.exists_slice_omega_vacElem_of_isEmpty {n₀ : Type} [Fintype n₀]
    [DecidableEq n₀] [IsEmpty n₀] {s₀ : n₀ → ℤˣ} {V : Space E n s} {V₀ : Space E n₀ s₀}
    (D : V.Splitting V₀ p) (g : G E s) :
    ∃ (c : ℂ) (z : Matrix p p (𝔸 E)) (γ : GL p (𝔸 E)),
      c ≠ 0 ∧
      zᴴ = z ∧
      ∀ x : p → 𝔸 E, D.slice x (V.ω g V.vacElem) =
        (c * stdAddChar E (-(toAdele (2⁻¹ : E) * star x ⬝ᵥ z *ᵥ x)) *
          ‖vacuumFn (γ.valᴴ *ᵥ x)‖ ^ 2) • V₀.vacElem := by
  -- Write `g` as radical times Levi times adapted; the slices of the adapted vacuum are known, and
  -- the other two factors act on slices by a substitution and by the character.
  obtain ⟨c₀, b, γ, g₀, h, h_adapted : D.IsAdapted h 1,
      hg : g = D.radicalElement c₀ b * D.levi (γ, g₀) * h⟩ :=
    D.exists_eq_radicalElement_mul_levi_mul_isAdapted g
  obtain ⟨c, hc_ne, hc⟩ : ∃ c ≠ (0 : ℂ), ∀ x : p → 𝔸 E,
      D.slice x (V.ω h V.vacElem) = (c * ‖vacuumFn x‖ ^ 2) • V₀.vacElem := by
    simpa using h_adapted.slice_omega_vacElem
  let z : Matrix p p (𝔸 E) := toAdele (2⁻¹ : E) • (b + bᴴ)
  have hz : zᴴ = z := by simp [z, add_comm]
  have h_sum : z + zᴴ = b + bᴴ := by
    rw [hz, ← add_smul, ← map_add, ← two_mul, mul_inv_cancel₀ two_ne_zero, map_one, one_smul]
  have h_centre : D.radicalElement c₀ b = D.radicalElement 0 z :=
    G.ext_adeleMatrix (by simp only [radicalElement, G.adeleMatrix_ofMatrix, h_sum,
      Subsingleton.elim c₀ 0])
  obtain rfl : g₀ = 1 := G.ext_adeleMatrix (Subsingleton.elim _ _)
  refine ⟨(chiAdelic γ.det)⁻¹ * c, z, γ,
    mul_ne_zero (inv_ne_zero (chiAdelic.toHomUnits γ.det).ne_zero) hc_ne, hz, fun x ↦ ?_⟩
  let ψx : ℂ := stdAddChar E (-(toAdele (2⁻¹ : E) * star x ⬝ᵥ z *ᵥ x))
  calc D.slice x (V.ω g V.vacElem)
      = D.slice x (V.ω (D.radicalElement 0 z) (V.ω (D.levi (γ, 1)) (V.ω h V.vacElem))) := by
        rw [hg, h_centre, map_mul, map_mul, mul_apply_eq_comp, mul_apply_eq_comp]
    _ = ψx • (chiAdelic γ.det)⁻¹ • D.slice (γ.valᴴ *ᵥ x) (V.ω h V.vacElem) := by
        rw [D.slice_omega_radicalElement_zero hz, D.slice_omega_levi, map_one,
          one_apply_eq_self]
    _ = ((chiAdelic γ.det)⁻¹ * c * ψx * ‖vacuumFn (γ.valᴴ *ᵥ x)‖ ^ 2) • V₀.vacElem := by
        rw [hc, smul_smul, smul_smul]
        ring_nf

variable (T P)

/-- The zero term along the Lagrangian of a complete splitting `P` of `S` does not vanish on any
translate of the vacuum vector `vacElem` of `Hom(S, T)` by an element `g` of the group of `S`. -/
lemma norm_zeroTerm_vacElem_pos (g : G E s) :
    0 < ‖P.lagrangian.zeroTerm T (splitWeil S T (g, 1) (vacElem (S.hom T)))‖ := by
  -- Up to a character this is the zero term of the splitting `P.homSource T` of `S.hom T`; only
  -- that splitting and the image of `g` matter.
  suffices (P.homSource T).zeroTerm ((S.hom T).ω (onHom (g, 1)) (S.hom T).vacElem) 0 ≠ 0 by
    simpa [zeroTerm_lagrangian_eq_theta, pairWeil]
  generalize P.homSource T = D, onHom (g, 1) (s' := t) = g
  -- The zero term is the slice at `0`, where the character and the Gaussian take the value `1`.
  obtain ⟨c, z, γ, hc_ne : c ≠ 0, -, h_slice⟩ := D.exists_slice_omega_vacElem_of_isEmpty g
  have h_zero : D.zeroTerm ((S.hom T).ω g (S.hom T).vacElem) =
      c • ((stdSpace E Empty).hom T).vacElem := by
    simpa [slice_zero, vacuumFn] using h_slice 0
  have h_vac : ((stdSpace E Empty).hom T).vacElem 0 = 1 := by
    simp [vacElem_apply_eq_prod_lineTheta (h := fun _ ↦ Subsingleton.elim _ _), Fintype.prod_empty]
  simpa [h_zero, h_vac] using hc_ne

/-- The idele norm is bounded on the ideles that lie in a compact set `C` of adeles. -/
lemma exists_ideleAbs_le_of_isCompact {F : Type} [Field F] [CMType F] [WeilData F] {C : Set (𝔸 F)}
    (hC : IsCompact C) : ∃ R : ℝ, ∀ d : (𝔸 F)ˣ, d.val ∈ C → ideleAbs d ≤ R := by
  -- The ideles in `C` of norm at least `1`, read as `1 × 1` matrices, form a compact set.
  have h_compact : IsCompact {A : GL (Fin 1) (𝔸 F) |
      A.val ∈ (fun d : 𝔸 F ↦ !![d]) '' C ∧ 1 ≤ ideleAbs A.det} :=
    isCompact_setOf_le_ideleAbs_det (hC.image_of_continuous _) one_pos
  obtain ⟨R, hR⟩ := (h_compact.image_of_continuous fun A ↦ ideleAbs A.det).bddAbove
  refine ⟨max R 1, fun d hd ↦ (le_total (ideleAbs d) 1).elim le_max_of_le_right fun h_ge ↦ ?_⟩
  have h_det : (GeneralLinearGroup.scalar (Fin 1) d).det = d := Units.ext (by simp)
  rw [← h_det] at h_ge ⊢
  exact le_max_of_le_left (hR ⟨.scalar (Fin 1) d, ⟨⟨d, hd, by simp [← ext_iff]⟩, h_ge⟩, rfl⟩)

/-- Let `P` and `P'` be complete splittings of `S` into `p` and `r` planes, with frames `k` and
`k'`. Let `Z` be an adelic `r × n` matrix with `Z k' = 1`, and let `K` be a compact set in the group
of `S`. Let `normalisedTorus T P x` be the normalised action of the Levi element `δ(x)` of `P`
(`δ = New.Core.dyadicDiag`). There is a constant `R` such that, for all `g ∈ K`, all `x`, `u` in
`ℕ ^ p` with `Z g k δ(x) = Z g k δ(u)` and all `f`, the zero term along the Lagrangian of `P'` of
`splitWeil S T (g, 1) (normalisedTorus T P x f)` has norm at most
`R * ‖f‖ * 2 ^ (d * (∑ u - ∑ x) * card m)`. Here `d` is the number of infinite places and `card m`
is the rank of `T`. `splitWeil` is the Weil representation of the pair `(S, T)` on test functions on
`Hom(S, T)`. The zero term along `L` sends `f` to the mean of `θ (ϱ z f)` over the maps `z : S → T`
vanishing on `L`, adelic modulo rational. -/
lemma exists_zeroTerm_normalisedTorus_le {K : Set (G E s)} (Z : Matrix r n (𝔸 E))
    (hZ : Z * P'.kAdelic = 1) (hK : IsCompact K) :
    ∃ R : NNReal, ∀ g ∈ K, ∀ x u : p → ℕ,
      Z * g.adeleMatrix * P.kAdelic * (dyadicDiag fun i : p ↦ x i : GL p (𝔸 E)).val =
        Z * g.adeleMatrix * P.kAdelic * (dyadicDiag fun i : p ↦ u i : GL p (𝔸 E)).val →
      ∀ f : 𝒮 (S.hom T),
        ‖P'.lagrangian.zeroTerm T (splitWeil S T (g, 1) (normalisedTorus T P x f))‖ ≤
          R * ‖f‖ * ((2 ^ Core.numInfPlaces E) ^ (∑ i : p, u i - ∑ i : p, x i : ℤ)) ^ card m := by
  -- Write `g · levi (dyadicDiag x) · κ · k' = k' a` by Iwasawa. Then `det a / det (dyadicDiag u)`
  -- is the determinant of a block matrix that stays in a compact set, and
  -- `norm_zeroTerm_parabolic_mul` moves `a` out.
  let blockDet : G E s × G E s × Matrix p p (𝔸 E) × Matrix p p (𝔸 E) → 𝔸 E := fun (g, κ, b, c) ↦
    (fromBlocks (Z * g.adeleMatrix * (P.lAdelic * cᴴ * P.lCoord) * κ.adeleMatrix * P'.kAdelic)
      (Z * g.adeleMatrix * P.kAdelic) (-P.kCoord * κ.adeleMatrix * P'.kAdelic) b).det
  let box : Set (Matrix p p (𝔸 E)) := Set.matrix (Metric.closedBall 0 1 ×ˢ Ô E)
  have h_box : IsCompact box := isCompact_closedBall_prod_integral.matrix
  obtain ⟨R₁, hR₁⟩ := exists_ideleAbs_le_of_isCompact
    ((hK.prod (isCompact_maxCompact.prod (h_box.prod h_box))).image_of_continuous blockDet)
  -- The maximal compact subgroup acts by operators of bounded norm.
  obtain ⟨R₂, hR₂⟩ : ∃ R₂ : ℝ, ∀ k ∈ (maxCompact E s : Set (G E s)) ×ˢ
      (maxCompact E t : Set (G E t)), ‖splitWeil S T k‖ ≤ R₂ :=
    (pairThetaKer ..).exists_norm_le_of_isCompact (isCompact_maxCompact.prod isCompact_maxCompact)
  refine ⟨(√R₁ ^ card m * (‖P'.lagrangian.zeroTerm T‖ * R₂)).toNNReal, fun g hg x u hu f ↦ ?_⟩
  let δx : GL p (𝔸 E) := dyadicDiag (x ·)
  let δu : GL p (𝔸 E) := dyadicDiag (u ·)
  obtain ⟨κ, hκ, a, -, ha, -⟩ := P'.iwasawa (g * P.levi (δx, 1)) (wt := 0)
  -- Multiply `ha` by `Z` to read off `a`, which is the Schur complement of the lower right block.
  have h_schur : a.val = Z * g.adeleMatrix * (P.lAdelic * δx⁻¹.valᴴ * P.lCoord) * κ.adeleMatrix *
    P'.kAdelic +
      Z * g.adeleMatrix * P.kAdelic * δu.val * P.kCoord * κ.adeleMatrix * P'.kAdelic := by
    rw [← Matrix.one_mul a.val, ← hZ, Matrix.mul_assoc, ← ha]
    simp [δx, δu, ← hu, Splitting.levi, add_comm, Matrix.mul_add, Matrix.add_mul,
      eq_zero iAdelic, ← Matrix.mul_assoc]
  have h_mem : (δu.det⁻¹ * a.det).val ∈ blockDet '' K ×ˢ maxCompact E s ×ˢ box ×ˢ box :=
    ⟨(g, κ, δu⁻¹.val, δx⁻¹.val), ⟨hg, hκ, dyadicDiag_inv_mem u, dyadicDiag_inv_mem x⟩,
      by simp [blockDet, h_schur, det_fromBlocks₂₂ .., ← Matrix.mul_assoc]⟩
  have sqrt_a : √(ideleAbs a.det) ≤ (2 ^ Core.numInfPlaces E) ^ (∑ i, u i) * √R₁ := by
    rw [← mul_inv_cancel_left δu.det a.det, map_mul, sqrt_mul' _ ideleAbs_nonneg_and_ne_zero.1,
      ideleAbs_det_dyadicDiag_natCast u, sqrt_sq (by positivity)]
    grw [hR₁ _ h_mem]
  -- Clear the normalising factor of `normalisedTorus`, which accounts for `∑ i, x i`.
  have h_norm : ‖P'.lagrangian.zeroTerm T (splitWeil S T (g, 1) (normalisedTorus T P x f))‖ =
      (((2 ^ Core.numInfPlaces E : ℝ) ^ ∑ i, x i) ^ card m)⁻¹ *
        ‖P'.lagrangian.zeroTerm T (splitWeil S T (g * P.levi (δx, 1), 1) f)‖ := by
    simp [δx, normalisedTorus, rep_apply_apply]
  suffices h_unscaled : ‖P'.lagrangian.zeroTerm T (splitWeil S T (g * P.levi (δx, 1), 1) f)‖ ≤
      √R₁ ^ card m * (‖P'.lagrangian.zeroTerm T‖ * R₂) * ‖f‖ *
        ((2 ^ Core.numInfPlaces E) ^ ∑ i, u i) ^ card m by
    grw [h_norm, h_unscaled, zpow_natCast_sub_natCast₀ (by positivity), div_pow, ← le_coe_toNNReal]
    exact le_of_eq (by ring)
  calc _ = √(ideleAbs a.det) ^ card m * ‖P'.lagrangian.zeroTerm T (splitWeil S T (κ⁻¹, 1) f)‖ := by
        rw [← norm_zeroTerm_parabolic_mul ha, mul_inv_cancel_right]
    _ ≤ ((2 ^ Core.numInfPlaces E) ^ (∑ i, u i) * √R₁) ^ card m *
          (‖P'.lagrangian.zeroTerm T‖ * (R₂ * ‖f‖)) := by
        grw [sqrt_a, le_opNorm, le_opNorm, hR₂ (κ⁻¹, 1) ⟨inv_mem hκ, one_mem _⟩]
    _ = _ := by ring

end New.SiegelWeil

/-!
## Vanishing of functionals dominated by vacuum zero terms

At a split place `w` and for `φ` fixed by the projection on the vacua at `w`, the Hecke transfer
`New.SiegelWeil.hecke_transfer_of_equivariant` writes `g ↦ λ * ℓ (splitWeil S T (g, 1) φ)`, for a
scalar `λ`, in norm as a weighted sum of translates. The total weight is less than `‖λ‖`, the sum of
the norms of the zero terms of the vacuum is a supersolution, and the maximum principle
`New.SiegelWeil.maximum_principle` applies.
-/

section CuspidalVanishing

open Finset Matrix Real Fintype ComplexOrder New WeilData Space Splitting AutChar HeckeChar
  SiegelWeil.Lagrangian G Complex

/-- For a real `x > 1` and positive `p`, `k`, write `q = x * x`. The product of
`∏ j < k, (1 + q ^ j * x ^ (2 * p))` and `∏ j < 2 * p, (1 + q ^ j * x ^ k)` is less than
`∏ j < 2 * p + k, (1 + q ^ j)`. The first product consists of the middle `k` factors of the last. -/
lemma New.SiegelWeil.prod_mul_prod_lt_prod_one_add_pow {x : ℝ} (hx : 1 < x) {p k : ℕ} (hp : 0 < p)
    (hk : 0 < k) :
    (∏ j ∈ range k, (1 + (x * x) ^ j * x ^ (2 * p))) *
        ∏ j ∈ range (2 * p), (1 + (x * x) ^ j * x ^ k) <
      ∏ j ∈ range (2 * p + k), (1 + (x * x) ^ j) := by
  -- The outer factors are compared in pairs, whose exponents have the same sums; the difference of
  -- the two sides of `pair` is `x ^ (2j) (x ^ k - 1) (x ^ (2p + k) - 1)`.
  have pair (j : ℕ) : (1 + (x * x) ^ j * x ^ k) * (1 + (x * x) ^ (p + j) * x ^ k) <
      (1 + (x * x) ^ j) * (1 + (x * x) ^ (p + k + j)) := by
    linear_combination x ^ (2 * j) *
      mul_add_mul_lt_mul_add_mul (one_lt_pow₀ hx hk.ne') (one_lt_pow₀ hx (by omega : 2 * p + k ≠ 0))
  have middle (j : ℕ) : (x * x) ^ j * x ^ (2 * p) = (x * x) ^ (p + j) := by ring
  -- Group the outer factors in pairs and set the middle `k` factors aside.
  calc _ = (∏ j ∈ range k, (1 + (x * x) ^ (p + j))) *
          ∏ j ∈ range p, (1 + (x * x) ^ j * x ^ k) * (1 + (x * x) ^ (p + j) * x ^ k) := by
        simp only [middle]
        rw [two_mul, prod_range_add, prod_mul_distrib]
    _ < (∏ j ∈ range k, (1 + (x * x) ^ (p + j))) *
          ∏ j ∈ range p, (1 + (x * x) ^ j) * (1 + (x * x) ^ (p + k + j)) :=
        mul_lt_mul_of_pos_left (prod_lt_prod_of_nonempty₀ (fun j _ ↦ by positivity)
          (fun j _ ↦ pair j) (nonempty_range_iff.2 hp.ne')) (by positivity)
    _ = _ := by rw [show 2 * p + k = p + k + p by ring, prod_range_add, prod_range_add,
          prod_mul_distrib, mul_left_comm, mul_assoc]

section SplitPlace

variable {E n m : Type} [Field E] [CMType E] [WeilData E] [Fintype n] [DecidableEq n] [Fintype m]
  [DecidableEq m] {s : n → ℤˣ} {t : m → ℤˣ} {S : Space E n s} {T : Space E m t} {w : FinPlace E}

/-- The weight of the subspace `U` of `𝔽_w ^ n` in the Hecke operator at `w` that the Hecke transfer
at `-1` gives on the side of `S`, for `S` of rank `2 * p` and `T` of rank `N = 2 * p + k`. Here
`𝔽_w = ResField w` is the residue field, `w.q` is the norm of `w` and `υ.atUniformizer w` the value
of the splitting character at a uniformiser. For `x ≥ 0`, `qPochhammer q k (-x)` has norm
`∏ j < k, (1 + q ^ j * x)`, and `heckePolyCoeff y U = (-y) ^ dim U * q ^ (dim U choose 2)`. -/
def New.SiegelWeil.transferWeight (p k N : ℕ) (U : Submodule (ResField w) (n → ResField w)) : ℂ :=
  qPochhammer w.q k (-√w.q ^ (2 * p)) *
    heckePolyCoeff (-(w.q ^ k * √w.q ^ (2 * p) / ((υ.atUniformizer w ^ N)⁻¹ * √w.q ^ N))) U

/-- The point of the unitary group `G E s`, supported above the split place `w` (the inverse of the
representative `basicCosetRep U` of `U`, put at `w` by `ofSplitPlace`), by which the summand of the
subspace `U` of `𝔽_w ^ n` in the Hecke operator at `w` translates. -/
def New.SiegelWeil.transferPoint (s : n → ℤˣ) (hw : w.IsSplit)
    (U : Submodule (ResField w) (n → ResField w)) : G E s :=
  (1, ofSplitPlace hw (basicCosetRep U)⁻¹)

/-- The Hecke transfer at `-1`. Let `S` have rank `2 * p` and `T` rank `2 * p + k`, let `f` be
fixed by the projection on the vacua at the split place `w` of norm `q = w.q`, and let `Λ` be a
functional invariant under the group of `T`. Then, in norm, `Λ (splitWeil S T (g, 1) f)` times
`qPochhammer q (card m) (-1) = ∏ l < card m, (1 + q ^ l)` is the sum, over the subspaces `U` of
`𝔽_w ^ n`, of the values of `Λ` at the translates by the points `transferPoint s hw U`, with the
weights `transferWeight p k (card m) U`. -/
lemma New.SiegelWeil.norm_qPochhammer_mul_norm_eq_norm_sum {p k : ℕ}
    (hn : Fintype.card n = 2 * p) (hk : Fintype.card m = 2 * p + k) (hw : w.IsSplit)
    {f : 𝒮 (S.hom T)} (hf : (S.hom T).projOn {w} f = f) {Λ : 𝒮 (S.hom T) →L[ℂ] ℂ}
    (hΛ : ∀ (h : G E t) (f : 𝒮 (S.hom T)), Λ (splitWeil S T (1, h) f) = Λ f) (g : G E s) :
    ‖qPochhammer w.q (Fintype.card m) (-1)‖ * ‖Λ (splitWeil S T (g, 1) f)‖ =
      ‖∑ U : Submodule (ResField w) (n → ResField w), transferWeight p k (Fintype.card m) U *
        Λ (splitWeil S T (g * transferPoint s hw U, 1) f)‖ := by
  -- Apply the transfer to the matrix coefficients `g ↦ Λ (ω(g, 1) f)`. The group of `S` acts on
  -- them by right translation, and that of `T` trivially.
  let coeff : 𝒮 (S.hom T) →ₗ[ℂ] G E s → ℂ := .pi fun g ↦ (Λ ∘L splitWeil S T (g, 1)).toLinearMap
  have equivariant (x : Gf E n) (h : Gf E m) :
      coeff (pairWeil S T (upsilonU1 ^ p) 1 ((1, x), 1, h) f) = finRightRep E s x (coeff f) := by
    funext g
    simpa [coeff, splitWeil, hn, rep_apply_apply] using hΛ (1, h) (splitWeil S T (g * (1, x), 1) f)
  obtain ⟨h_sph, -, h_hecke⟩ :=
    hecke_transfer_of_equivariant (hk.trans (by rw [hn]))
      ((hasWeight_upsilonU1_pow p).charUnramifiedAt rfl rfl)
      (HasWeight.one.charUnramifiedAt rfl rfl) hw hf coeff (finRightRep E s) 1 equivariant
  have h_source : (upsilonU1 ^ p).frobValue n w = (√w.q : ℂ) ^ (2 * p) := by
    simp [frobValue, AutChar.spaceChar, ← pow_mul, atUniformizer, finPart, hn, -map_inv]
  have h_target : frobValue (1 : AutChar E) m w =
      (υ.atUniformizer w ^ Fintype.card m : ℂ)⁻¹ * (√w.q : ℂ) ^ Fintype.card m := by
    simp [frobValue, AutChar.spaceChar, atUniformizer, finPart, -map_inv]
  -- On the left the Hecke polynomial is a scalar, on the right it is a sum over `U`.
  have h_norm := congrArg (‖· g‖) (h_hecke (-1))
  rw [(heckePolyOp_eq_sum hw h_sph _).2, h_source, h_target] at h_norm
  -- The remaining `simpa` evaluates the trivial action of the group of `T` and `coeff` at `g`.
  simpa [coeff, transferWeight, transferPoint, (hasHeckePolynomial_qPochhammer ..).2, mul_sum,
    ← mul_assoc] using h_norm

/-- For `x ≥ 0`, the norm of `qPochhammer q k (-x)` is `∏ j < k, (1 + q ^ j * x)`. -/
lemma New.SiegelWeil.norm_qPochhammer_neg (q k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    ‖qPochhammer q k (-x)‖ = ∏ j ∈ range k, (1 + (q : ℝ) ^ j * x) := by
  rw [← Real.norm_of_nonneg (prod_nonneg fun j _ ↦ by positivity), ← norm_real]
  simp

omit [Fintype n] [DecidableEq n] in
/-- The norm of the weight of `U` for `N = 2 * p + k`: with `x = √q`, `q = w.q` the norm of `w`, it
is `∏ j < k, (1 + q ^ j * x ^ (2 * p))` times `(x ^ k) ^ dim U * q ^ (dim U choose 2)`. -/
lemma New.SiegelWeil.norm_transferWeight (p k : ℕ) (U : Submodule (ResField w) (n → ResField w)) :
    ‖transferWeight p k (2 * p + k) U‖ =
      (∏ j ∈ range k, (1 + (w.q : ℝ) ^ j * √w.q ^ (2 * p))) *
        ((√w.q ^ k) ^ Module.finrank (ResField w) U *
          (w.q : ℝ) ^ (Module.finrank (ResField w) U).choose 2) := by
  have h_hecke : ‖qPochhammer w.q k (-√w.q ^ (2 * p))‖ =
      ∏ j ∈ range k, (1 + (w.q : ℝ) ^ j * √w.q ^ (2 * p)) := by
    simpa using norm_qPochhammer_neg w.q k (x := √w.q ^ (2 * p)) (by positivity)
  have hq_pos : 0 < √(w.q : ℝ) := zero_lt_one.trans (by simp [lt_sqrt])
  have h_ratio : (w.q : ℝ) ^ k * √w.q ^ (2 * p) / √w.q ^ (2 * p + k) = √w.q ^ k := by
    nth_rw 1 [← Real.mul_self_sqrt w.q.cast_nonneg]
    field_simp
    ring
  rw [transferWeight, norm_mul, h_hecke, ← h_ratio]
  simp [heckePolyCoeff, card_ResField, abs_of_pos hq_pos,
    show ‖υ.atUniformizer w‖ = 1 from Circle.norm_coe _]

omit [DecidableEq n] in
/-- If `card n = 2 * p`, `p` and `k` are positive and `N = 2 * p + k`, the total weight
`∑ U, ‖transferWeight p k N U‖` is less than `‖qPochhammer w.q N (-1)‖ = ∏ l < N, (1 + q ^ l)`,
where `q = w.q` is the norm of the place `w`. -/
lemma New.SiegelWeil.sum_norm_transferWeight_lt {p k N : ℕ} (hn : Fintype.card n = 2 * p)
    (hN : N = 2 * p + k) (hp : 0 < p) (hk : 0 < k) :
    ∑ U : Submodule (ResField w) (n → ResField w), ‖transferWeight p k N U‖ <
      ‖qPochhammer w.q N (-1)‖ := by
  -- The total weight is a product, by the `q`-binomial theorem, and so is the right side.
  -- With `x = √q` this is `prod_mul_prod_lt_prod_one_add_pow`.
  have binomial : ∑ U : Submodule (ResField w) (n → ResField w),
      (√w.q ^ k) ^ Module.finrank (ResField w) U *
        (w.q : ℝ) ^ (Module.finrank (ResField w) U).choose 2 =
      ∏ j ∈ range (2 * p), (1 + (w.q : ℝ) ^ j * √w.q ^ k) := by
    simpa [← Complex.ofReal_inj, heckePolyCoeff, hn, card_ResField] using
      q_binomial_submodule n (ResField w) ⊤ (-√w.q ^ k)
  have h_right : ‖qPochhammer w.q (2 * p + k) (-1)‖ =
      ∏ j ∈ range (2 * p + k), (1 + (w.q : ℝ) ^ j) := by
    simpa using norm_qPochhammer_neg w.q (2 * p + k) zero_le_one
  have hq : 1 < √(w.q : ℝ) := by simp [lt_sqrt]
  simp only [hN, norm_transferWeight, ← mul_sum, binomial, h_right]
  simpa only [Real.mul_self_sqrt w.q.cast_nonneg] using prod_mul_prod_lt_prod_one_add_pow hq hp hk

/-- Let `D` split `V` over a space `V₀` of rank zero, let `A` be a set of finite places disjoint
from its conjugate, `g` in the group of `V` and `f` in `𝒮 V`. As `Ψ` runs over the nonnegative
Schwartz–Bruhat functions above `A`, the zero terms of `V.ω g (V.schrodingerOp A Ψ f)` are
nonnegative real multiples of one vector `v`. Here `V.ω` is the Weil representation, and
`V.schrodingerOp A Ψ` is the combination of Heisenberg operators on `𝒮 V` whose counterpart in the
Schrödinger model is `Ψ`. -/
lemma New.SiegelWeil.exists_zeroTerm_omega_schrodingerOp_eq_smul {n₀ q : Type} [Fintype n₀]
    [DecidableEq n₀] [IsEmpty n₀] [Fintype q] [DecidableEq q] {s₀ : n₀ → ℤˣ} {V : Space E n s}
    {V₀ : Space E n₀ s₀} (D : V.Splitting V₀ q) {A : Set (FinPlace E)} (hA : A.IsConjDisjoint)
    (g : G E s) (f : 𝒮 V) :
    ∃ v : 𝒮 V₀, ∀ (Ψ : (n → 𝔸f E) → ℂ) [IsSchwartzBruhat A Ψ], 0 ≤ Ψ →
      ∃ r : ℝ, 0 ≤ r ∧ D.zeroTerm (V.ω g (V.schrodingerOp A Ψ f)) = (r : ℂ) • v := by
  -- Write `g = g₀ h` with `g₀` adapted to `D`. The element `h` moves `Ψ` and replaces `f` by a
  -- vector `u` independent of `Ψ`; the zero term after `g₀` integrates the moved function.
  obtain ⟨g₀, hg₀, -⟩ := D.exists_isAdapted_and_frame_eq 1
  obtain ⟨h, rfl⟩ : ∃ h : G E s, g₀ * h = g := ⟨_, mul_inv_cancel_left g₀ g⟩
  let u : 𝒮 V := V.ω h (V.schrodingerOp A (fun x : n → 𝔸f E ↦ boxIndicator n A (h.2 *ᵥ x)) f)
  refine ⟨V₀.schrodingerOp A 1 (D.zeroTerm (V.ω g₀ (V.projOn A u))), fun Ψ _ hΨ ↦ ?_⟩
  let Φ (x : n → 𝔸f E) : ℂ := Ψ (↑h.2⁻¹ *ᵥ x)
  have h_zero : D.zeroTerm (V.ω g₀ (V.schrodingerOp A Φ u)) =
      V₀.schrodingerOp A (D.sliceDatum A g₀ 1 Φ 0) (D.zeroTerm (V.ω g₀ (V.projOn A u))) := by
    simpa [slice_zero] using
      hg₀.omega_schrodingerOp_of_isMixedLaw isMixedLaw_slice 0 u hA (IsSchwartzBruhat.comp_mulVec _)
  -- The function `sliceDatum` lives on a point, and its value is the integral of `Φ ≥ 0`.
  let I : ℂ := D.sliceDatum A g₀ 1 Φ 0 0
  have hI : 0 ≤ I := MeasureTheory.integral_nonneg fun b ↦ by simpa using hΨ _
  have h_slice : D.sliceDatum A g₀ 1 Φ 0 = (‖I‖ : ℂ) • (1 : (n₀ → 𝔸f E) → ℂ) := by
    funext y
    simp [Subsingleton.elim y 0, ← eq_coe_norm_of_nonneg hI, I]
  refine ⟨‖I‖, norm_nonneg I, ?_⟩
  rw [← rep_apply_apply, (V.omega_schrodingerOp hA h f).2, h_zero, h_slice, map_smul,
    _root_.smul_apply]

/-- Let `w` be a split place (one that differs from its conjugate), `L` a Lagrangian of `S`, and `g`
in the group of `S`, which acts by the Weil representation `splitWeil S T (·, 1)`. For a subspace
`U` of `𝔽_w ^ n`, `transferPoint s hw U` is the element of the group of `S`, supported above `w`, by
which the summand of `U` in the Hecke operator at `w` translates. The zero terms along `L` of the
vacuum translated by `g * transferPoint s hw U`, multiplied by
`(υ.atUniformizer w ^ card m) ^ dim U`, are nonnegative real multiples of one complex number `v`.
Here the zero term is the mean of `θ (ϱ z f)` over maps `z : S → T` vanishing on `L`, adelic modulo
rational, and `υ.atUniformizer w` is the value of the splitting character at a uniformiser of
`w`. -/
lemma New.SiegelWeil.exists_zeroTerm_transferPoint_eq (hw : w.IsSplit) (L : Lagrangian S)
    (g : G E s) :
    ∃ (v : ℂ) (r : Submodule (ResField w) (n → ResField w) → ℝ),
      ∀ U : Submodule (ResField w) (n → ResField w), 0 ≤ r U ∧
        (υ.atUniformizer w ^ Fintype.card m) ^ Module.finrank (ResField w) U *
          L.zeroTerm T (splitWeil S T (g * transferPoint s hw U, 1) (vacElem (S.hom T))) =
        r U * v := by
  -- The vacuum is fixed by `schrodingerOp {w} boxIndicator`. The point of `U` moves that function
  -- and gives a character, whose unitary part cancels the power of `υ.atUniformizer w`; then
  -- `exists_zeroTerm_omega_schrodingerOp_eq_smul` applies.
  have h_disj : Set.IsConjDisjoint {w} := by simp [hw]
  obtain ⟨⟨d, P⟩, rfl : P.lagrangian = L⟩ := L.completeSplitting
  obtain ⟨v, hv⟩ : ∃ v : 𝒮 ((stdSpace E Empty).hom T),
      ∀ (Ψ : (m × n → 𝔸f E) → ℂ) [IsSchwartzBruhat {w} Ψ], 0 ≤ Ψ → ∃ r : ℝ, 0 ≤ r ∧
        (P.homSource T).zeroTerm ((S.hom T).ω (G.onHom (g, 1))
          ((S.hom T).schrodingerOp {w} Ψ (vacElem (S.hom T)))) = (r : ℂ) • v :=
    exists_zeroTerm_omega_schrodingerOp_eq_smul (P.homSource T) h_disj _ _
  suffices h_term : ∀ U : Submodule (ResField w) (n → ResField w), ∃ r : ℝ, 0 ≤ r ∧
      (υ.atUniformizer w ^ Fintype.card m) ^ Module.finrank (ResField w) U *
        P.lagrangian.zeroTerm T
          (splitWeil S T (g * transferPoint s hw U, 1) (vacElem (S.hom T))) = r * θ _ v from
    ⟨θ _ v, Classical.skolem.1 h_term⟩
  intro U
  -- The image of the point of `U` in the group of `Hom(S, T)` is a finite element `κ` above `w`.
  let κ : Gf E (m × n) := (G.onHom (transferPoint s hw U, (1 : G E t))).2
  let δ : (𝔸 E)ˣ := detOn {w} κ.val
  have hκ : G.onHom (transferPoint s hw U, (1 : G E t)) = (1, κ) := onHom_fin _ 1
  have hκ_supp : κ ∈ Gf.supportedOn (m × n) {w} := by simp [κ, transferPoint]
  let Ψ (x : m × n → 𝔸f E) : ℂ := boxIndicator (m × n) {w} (↑κ⁻¹ *ᵥ x)
  have h_vac : (S.hom T).ω (1, κ) (vacElem (S.hom T)) =
      starRingEnd ℂ (chiAdelic δ) • (S.hom T).schrodingerOp {w} Ψ (vacElem (S.hom T)) := by
    rw [← (S.hom T).omega_schrodingerOp_of_mem_supportedOn h_disj hκ_supp,
      schrodingerOp_boxIndicator h_disj, projOn_vacElem]
  obtain ⟨ρ, hρ, h_term⟩ := hv Ψ fun x ↦ by simp [Ψ, boxIndicator, ite_nonneg]
  have h_char : pairChar (1 * upsilonU1 ^ (Fintype.card n / 2)) 1
      (g * transferPoint s hw U, (1 : G E t)) = 1 := by simp [pairChar]
  have cancel : (υ.val δ : ℂ) =
      (υ.atUniformizer w ^ Fintype.card m) ^ Module.finrank (ResField w) U := by
    -- `υ` is unramified at `w`, and the determinant of `basicCosetRep U` has order `dim U`.
    obtain ⟨⟨-, h_order⟩, -⟩ := basicCosetRep_mem_and_residueKer_eq U
    simp [δ, κ, transferPoint, ← coe_singleton, detOn_eq_prod, det_kronecker, h_order,
      (charUnramifiedAt_upsilon _).apply_locFullIdele, atUniformizer, finPart, _root_.zpow_mul]
  have h_chi : (υ.val δ : ℂ) * starRingEnd ℂ (chiAdelic δ) = (√(ideleAbs δ))⁻¹ := by
    simp [chiAdelic, ← Circle.coe_inv_eq_conj]
  refine ⟨(√(ideleAbs δ))⁻¹ * ρ, by positivity, ?_⟩
  have h_translate : splitWeil S T (g * transferPoint s hw U, 1) (vacElem (S.hom T)) =
      (S.hom T).ω (G.onHom (g, 1)) ((S.hom T).ω (1, κ) (vacElem (S.hom T))) := by
    rw [pairWeil_apply, h_char, one_smul, ← Prod.mk_one_mul_mk_one, map_mul, ← rep_apply_apply, hκ]
  calc _ = (υ.val δ : ℂ) * (starRingEnd ℂ (chiAdelic δ) * (ρ * θ _ v)) := by
        simp only [cancel, zeroTerm_lagrangian_eq_theta, h_translate, h_vac, map_smul, h_term,
          smul_eq_mul]
    _ = _ := by rw [← mul_assoc, h_chi, ofReal_mul, ofReal_inv, mul_assoc]

/-- For the zero term along a Lagrangian `L` of `S` and the vacuum vector `vacElem` translated by
`g`, all summands of the Hecke operator at a split place `w` (weights `transferWeight`, points
`transferPoint`, indexed by the subspaces `U` of `𝔽_w ^ n`) have the same phase: the sum of their
norms is at most the norm of their sum. -/
lemma New.SiegelWeil.sum_norm_mul_norm_zeroTerm_le (p k : ℕ) (hw : w.IsSplit) (L : Lagrangian S)
    (g : G E s) :
    ∑ U : Submodule (ResField w) (n → ResField w), ‖transferWeight p k (Fintype.card m) U‖ *
        ‖L.zeroTerm T (splitWeil S T (g * transferPoint s hw U, 1) (vacElem (S.hom T)))‖ ≤
      ‖∑ U : Submodule (ResField w) (n → ResField w), transferWeight p k (Fintype.card m) U *
        L.zeroTerm T (splitWeil S T (g * transferPoint s hw U, 1) (vacElem (S.hom T)))‖ := by
  -- For every `U` the zero term, times a power of the phase `υ.atUniformizer w`, is `r U * v` with
  -- `r U ≥ 0`.
  obtain ⟨v, r, hr⟩ := exists_zeroTerm_transferPoint_eq (T := T) hw L g
  -- The weight of `U` is a constant `c`, times a real number `a U ≥ 0`, times the phase in `hr`.
  let c : ℂ := qPochhammer w.q k (-√w.q ^ (2 * p))
  let a (U : Submodule (ResField w) (n → ResField w)) : ℝ :=
    (w.q ^ k * √w.q ^ (2 * p) / √w.q ^ Fintype.card m) ^ Module.finrank (ResField w) U *
      Nat.card (ResField w) ^ (Module.finrank (ResField w) U).choose 2
  have weight (U : Submodule (ResField w) (n → ResField w)) :
      transferWeight p k (Fintype.card m) U =
        c * a U * (υ.atUniformizer w ^ Fintype.card m) ^ Module.finrank (ResField w) U := by
    simp only [transferWeight, heckePolyCoeff, a, c, neg_neg, div_eq_mul_inv, mul_inv, inv_inv]
    push_cast
    ring
  -- So each summand is a nonnegative real multiple of `c * v`.
  have nonneg (U : Submodule (ResField w) (n → ResField w)) : 0 ≤ a U * r U :=
    mul_nonneg (by positivity) (hr U).1
  have summand (U : Submodule (ResField w) (n → ResField w)) :
      transferWeight p k (Fintype.card m) U *
        L.zeroTerm T (splitWeil S T (g * transferPoint s hw U, 1) (vacElem (S.hom T))) =
      (a U * r U : ℝ) * (c * v) := by
    linear_combination (norm := (push_cast [weight]; ring)) c * a U * (hr U).2
  simp only [← norm_mul, summand, ← sum_mul, ← ofReal_sum]
  simp only [norm_mul, norm_real, Real.norm_of_nonneg (nonneg _), ← sum_mul]
  exact mul_le_mul_of_nonneg_right (le_norm_self _) (by positivity)

end SplitPlace

/-- Let `S` have rank `2 * p > 0` and `T` rank greater than `2 * p`, and let `ℓ` be a continuous
functional on the function space of `Hom(S, T)` that is invariant under the group of `T` acting by
`ω(1, h)`, where `ω = splitWeil S T`. Suppose that for every `f` the zero terms along the
Lagrangians `L` of `S` are summable over `L`; the zero term sends `f` to the mean of `θ (ϱ z f)`
over the maps `z : S → T` vanishing on `L`, adelic modulo rational. Suppose also that for every `f`
the function `g ↦ ‖ℓ (ω(g, 1) f)‖ - ∑ L, ‖zero term along L of ω(g, 1) vacElem‖` on the group of `S`
is bounded above, with `vacElem` the vacuum vector; then `ℓ f = 0` for every `f`. -/
lemma New.SiegelWeil.eq_zero_of_le_tsum_zeroTerm {E n m : Type} {p : ℕ} [Field E] [CMType E]
    {s : n → ℤˣ} {t : m → ℤˣ} [WeilData E] [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    {S : Space E n s} {T : Space E m t} [Nonempty n]
    (hn : Fintype.card n = 2 * p) (hm : 2 * p < Fintype.card m) {ℓ : 𝒮 (S.hom T) →L[ℂ] ℂ}
    (hℓ : ∀ (h : G E t) (f : 𝒮 (S.hom T)), ℓ (splitWeil S T (1, h) f) = ℓ f)
    (h_summable : ∀ f : 𝒮 (S.hom T), Summable fun L : Lagrangian S ↦ Lagrangian.zeroTerm T L f)
    (h_bound : ∀ f : 𝒮 (S.hom T), BddAbove (Set.range fun g : G E s ↦
      ‖ℓ (splitWeil S T (g, 1) f)‖ -
        ∑' L : Lagrangian S, ‖Lagrangian.zeroTerm T L (splitWeil S T (g, 1) (vacElem (S.hom T)))‖))
    {f : 𝒮 (S.hom T)} : ℓ f = 0 := by
  -- It is enough to kill the vectors `φ` of `map_eq_zero_of_map_integrated_eq_zero`, given by a
  -- polynomial `P` and a finite adelic vector `z`. Take a split place `w` with `z` integral at `w`
  -- and at `star w`, and apply the maximum principle to the Hecke operator at `w`.
  refine map_eq_zero_of_map_integrated_eq_zero _ (projOn_empty ..) fun P (z : m × n → 𝔸f E) _ ↦ ?_
  set φ : 𝒮 (S.hom T) :=
    (S.hom T).integrated (Fock.polyVector _ P) ((S.hom T).finHeisenbergOp z (vacElem _))
  by_contra h_ne : ℓ φ ≠ 0
  obtain ⟨k, hk_pos, hk⟩ : ∃ k > 0, card m = 2 * p + k := lt_iff_exists_add.1 hm
  have hp : 0 < p := by simpa using card_pos.trans_eq hn
  -- Infinitely many places have prime norm, hence are split; `z` is integral at almost all places.
  obtain ⟨w, hw, hz⟩ : ∃ w : FinPlace E, w.IsSplit ∧ ∀ i : m × n,
      z i w ∈ w.adicCompletionIntegers E ∧ z i (star w) ∈ (star w).adicCompletionIntegers E := by
    have split : ∃ᶠ w : FinPlace E in Filter.cofinite, w.IsSplit :=
      frequently_prime_q.mono fun _ ↦ isSplit_of_q_prime
    have integral (i : m × n) :
        ∀ᶠ w : FinPlace E in Filter.cofinite, z i w ∈ w.adicCompletionIntegers E := (z i).2
    exact (split.and_eventually (Filter.eventually_all.2 fun i ↦ (integral i).and
      (star_injective.tendsto_cofinite.eventually (integral i)))).exists
  have hφ : (S.hom T).projOn {w} φ = φ := by
    rw [projOn_integrated, projOn_finHeisenbergOp_vacElem, ite_eq_left]
    simpa [mem_integralBox, idem_mul_mem_Ô, star_eq_iff_star_eq,
      IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] using hz
  let γ : Submodule (ResField w) (n → ResField w) → G E s := transferPoint s hw
  let c : Submodule (ResField w) (n → ResField w) → ℂ := transferWeight p k (card m)
  -- The sum `σ` of the norms of the zero terms of the vacuum is a supersolution, term by term.
  let σ (g : G E s) : ℝ :=
    ∑' L : Lagrangian S, ‖L.zeroTerm T (splitWeil S T (g, 1) (vacElem (S.hom T)))‖
  have super (g : G E s) :
      ∑ U, ‖c U‖ * σ (g * γ U) ≤ ‖qPochhammer w.q (card m) (-1)‖ * σ g := by
    refine hasSum_le (fun L ↦ ?_) (hasSum_sum fun U _ ↦ (h_summable _).norm.hasSum.mul_left _)
      ((h_summable _).norm.hasSum.mul_left _)
    have invariant (h : G E t) (f : 𝒮 (S.hom T)) :
        L.zeroTerm T (splitWeil S T (1, h) f) = L.zeroTerm T f := by
      simp [Lagrangian.zeroTerm, mixedValue_splitWeil]
    exact (sum_norm_mul_norm_zeroTerm_le p k hw L g).trans_eq
      (norm_qPochhammer_mul_norm_eq_norm_sum hn hk hw (projOn_vacElem _) invariant g).symm
  -- The maximum principle bounds `ℓ` by `σ` on the translates of each `f` that is vacuum at `w`.
  have h_le {f : 𝒮 (S.hom T)} (hf : (S.hom T).projOn {w} f = f) (g : G E s) :
      ‖ℓ (splitWeil S T (g, 1) f)‖ - σ g ≤ 0 := by
    refine maximum_principle (h_bound f) c (fun g U ↦ g * γ U)
      (sum_norm_transferWeight_lt hn hk hp hk_pos) (fun g ↦ ?_) g
    have sub := (norm_qPochhammer_mul_norm_eq_norm_sum hn hk hw hf hℓ g).trans_le
      (norm_sum_le_of_le _ fun U _ ↦ norm_mul_le (c U) (ℓ (splitWeil S T (g * γ U, 1) f)))
    simpa only [mul_sub, sum_sub_distrib] using sub_le_sub sub (super g)
  -- If `ℓ φ ≠ 0`, a large multiple of `φ` violates this bound at `g = 1`.
  obtain ⟨a, ha⟩ := NormedField.exists_lt_norm ℂ (σ 1)
  have h_large : ‖ℓ (splitWeil S T (1, 1) ((a / ℓ φ) • φ))‖ - σ 1 ≤ 0 := h_le (by simp [hφ]) 1
  rw [hℓ 1, map_smul, smul_eq_mul, div_mul_cancel₀ _ h_ne] at h_large
  linarith

end CuspidalVanishing

end
