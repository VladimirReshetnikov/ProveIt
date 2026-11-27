import New.UpperBound.Objects.AuxiliaryPair

/-!
# The theta kernel of a descent pair with values in the weight representation

For a descent pair `O : New.DescentPair` with spaces `W` and `V`, the theta kernels of the data
`v_{P_ξ} ⊗ Ψ_bl ⊗ vac = O.fockDatum ξ` depend linearly on the vector `ξ` of the representation of
weight `(O.columnCount, O.detExp)`. Here `v_{P_ξ}` is the Fock vector of the polynomial
`P_ξ = O.fockPoly ξ`, and `Ψ_bl ⊗ vac = O.blockDatum` is the finite datum: a block datum at the
places of the level and the vacuum at the other finite places. So there is one kernel `θ_W(g, h)`
with values in this representation such that the kernel of `O.fockDatum ξ` is `⟨ξ̄, θ_W(g, h)⟩`. The
pairing `⟨ζ, η⟩` is `New.gramForm ζ η`, conjugate linear in `ζ`.

## Main definitions and results

* `New.DescentPair.vectorKernel`, `New.DescentPair.gramForm_vectorKernel`: the kernel `θ_W(g, h)`
  and its defining property.
* `New.DescentPair.vectorKernelForm`: the function `θ_W(g, ·)` as an algebraic form on `V`.
* `New.DescentPair.normalizedDescent_eq_inner_vectorKernelForm`: the normalized descent
  `New.DescentPair.normalizedDescent` of a form `Ξ` on `V` has the value `⟨θ_W(g, ·), Ξ⟩` at `g`.

Notions from other files:
* `New.DescentPair`: the data of a space `W` of signs `O.signs`, an embedding of its index set in
  that of `V = I_n`, weights and a character, from which `(O.columnCount, O.detExp)` and the level
  are built.
* `New.WeylIndex n κ`: the index set of the coordinates of the representation of weight `κ`, on
  which `New.weylGramOver` is the Gram matrix of `New.gramForm`.
* `New.G E s`, `New.Gf E n`: the adelic unitary group of signs `s` and the finite part of that of
  the standard definite space `New.stdSpace E n = I_n`.
* `New.stdClassSum K f`: the sum of `f` over the double cosets of the rational points and `K`, each
  weighted by the inverse of the order of its automorphism group.
-/

noncomputable section

namespace New.DescentPair

open Matrix Space ComplexConjugate ComplexOrder

variable {E r n : Type} [Field E] [CMType E] [WeilData E] [Fintype r] [DecidableEq r] [Fintype n]
  [DecidableEq n] (O : DescentPair E r n)

/-- The value at `ξ` of the linear form `O.conjKernel g h` is the conjugate of the theta kernel at
`(g, h)` of `O.fockDatum (star ξ)`. The kernel `New.pairTheta` is formed with the characters
`O.charW` and `O.charV` at the point `(g, 1, h)`, whose component `(1, h)` in `U(V)(𝔸)` is trivial
at the infinite places. -/
lemma conjKernel_apply (g : G E O.signs) (h : Gf E n) (ξ : WeylIndex n O.columnCount → ℂ) :
    O.conjKernel g h ξ =
      conj (pairTheta O.W (stdSpace E n) O.charW O.charV (O.fockDatum (star ξ)) (g, 1, h)) := rfl

/-- The normalized descent `O.normalizedDescent Ξ` of a form `Ξ` on `V = stdSpace E n` has at `g`
the value `∑ O.conjKernel g h (Ξ h) / #(Γ ∩ h K h⁻¹)`, where `h` runs over chosen representatives of
the double cosets `Γ \ U(V)(𝔸_f) / K` of the rational points `Γ` and the level
`K = O.levelGroup`. -/
lemma normalizedDescent_apply (Ξ : O.FormV) (g : G E O.signs) :
    O.normalizedDescent Ξ g = stdClassSum O.levelGroup fun h : Gf E n ↦ O.conjKernel g h (Ξ h) :=
      rfl

/-- The theta kernel `θ_W(g, h)` with values in the representation of weight
`(O.columnCount, O.detExp)`, for `g` in `U(W)(𝔸)` and a finite point `h` of `U(V)`. It is the vector
whose pairing with `ζ` is the theta kernel of the datum `O.fockDatum (star ζ)` at `(g, h)`
(`New.DescentPair.gramForm_vectorKernel`). -/
def vectorKernel (g : G E O.signs) (h : Gf E n) : WeylIndex n O.columnCount → ℂ :=
  weylGramOver⁻¹ *ᵥ fun i : WeylIndex n O.columnCount ↦ conj (O.conjKernel g h (Pi.single i 1))

/-- For every coordinate vector `ζ` of the representation of weight `(O.columnCount, O.detExp)`, the
Gram pairing `⟨ζ, θ_W(g, h)⟩` is the theta kernel `New.pairTheta` of `O.fockDatum (star ζ)` at
`(g, 1, h)`. -/
lemma gramForm_vectorKernel (g : G E O.signs) (h : Gf E n) (ζ : WeylIndex n O.columnCount → ℂ) :
    gramForm ζ (O.vectorKernel g h) =
      pairTheta O.W (stdSpace E n) O.charW O.charV (O.fockDatum (star ζ)) (g, 1, h) := by
  have isUnit_det_gram : IsUnit (weylGramOver : Matrix (WeylIndex n O.columnCount)
    (WeylIndex n O.columnCount) ℂ).det :=
    (isUnit_iff_isUnit_det _).1 weylGramOver_posDef.isUnit
  calc gramForm ζ (O.vectorKernel g h)
      = conj (∑ i : WeylIndex n O.columnCount, ζ i * O.conjKernel g h (Pi.single i 1)) := by
        simp [gramForm_apply, vectorKernel, mul_nonsing_inv _ isUnit_det_gram, dotProduct]
    _ = conj (O.conjKernel g h ζ) := by
        conv_rhs => rw [pi_eq_sum_univ' ζ, map_sum]
        simp only [map_smul, smul_eq_mul]
    _ = pairTheta O.W (stdSpace E n) O.charW O.charV (O.fockDatum (star ζ)) (g, 1, h) :=
        Complex.conj_conj _

/-- The pairing of the kernel vector `θ_W(g, h) = O.vectorKernel g h` with `ξ` in the Gram form,
conjugate linear in its first argument, is `O.conjKernel g h ξ`, the conjugate of the theta kernel
at `(g, h)` of `O.fockDatum (star ξ)`. -/
lemma gramForm_vectorKernel_left (g : G E O.signs) (h : Gf E n)
    (ξ : WeylIndex n O.columnCount → ℂ) :
    gramForm (O.vectorKernel g h) ξ = O.conjKernel g h ξ := by
  rw [← conj_gramForm, gramForm_vectorKernel, conjKernel_apply]

/-- Let `O` be a descent pair over a CM field `E` with Weil data, let `g` be an adelic point of the
unitary group of `W`, whose signs are `O.signs`, and `x` a finite point of `U(V)`. For rational `γ`
in `U(V)` and `k` in the level `O.levelGroup`, `θ_W(g, γ x k) = c(k) ρ(γ) θ_W(g, x)`. Here
`θ_W = O.vectorKernel` and `stdEmbFin γ` is the image of `γ` in the finite points. With
`k⁺ = O.colsPlus`, `k⁻ = O.colsMinus` and `N` the rank of `V`, the representation `ρ` has at an
infinite place `τ` the weight with `O.columnCount τ i = k⁺(τ, i) + k⁻(τ, N - i)` columns of height
`i` and the power `O.detExp τ = -∑_{1 ≤ i < N} k⁻(τ, i)` of the determinant. The character
`c = O.levelChar` sends `k` to the product, over the places `w` of the family `O.twistPlace`, of
`(O.tamePart w)⁻¹ (det k_w)`. Here `O.tamePart w` is a multiplicative character of the residue field
at `w`, and `k_w` is the diagonal block of the reduction of `k` at `w` whose rows and columns are
indexed by the image of `O.incl : r ↪ n`, the embedding of the basis indices of `W` in those of
`V`. -/
lemma vectorKernel_equivariant (γ : U (stdSpace E n).J) (k : O.levelGroup) (g : G E O.signs)
    (x : Gf E n) :
    O.vectorKernel g (stdEmbFin γ * x * k.val) =
      O.levelChar k • (stdSpace E n).weightRep O.columnCount O.detExp γ (O.vectorKernel g x) := by
  -- The operator `c(k) ρ(γ)` is unitary for the Gram form and onto, so it is enough to pair both
  -- sides with its values; there `conjKernel_equivariant` applies.
  set ρ : Representation ℂ (U (stdSpace E n).J) (WeylIndex n O.columnCount → ℂ) :=
    (stdSpace E n).weightRep O.columnCount O.detExp with hρ
  set c : ℂ := O.levelChar k with hc
  have h_norm : conj c * c = 1 := by
    rw [hc, Complex.conj_mul', (LevelPlaces.isOfFinOrder_level_char k).norm_eq_one]
    simp
  have h_unitary (u v : WeylIndex n O.columnCount → ℂ) :
    gramForm (c • ρ γ u) (c • ρ γ v) = gramForm u v := by
    rw [map_smul, LinearMap.map_smulₛₗ₂, smul_smul, mul_comm, h_norm, one_smul, hρ,
      weightRep_apply, gramForm_conjWeylRep]
  refine ext_gramForm_left fun ζ ↦ ?_
  obtain ⟨v, rfl⟩ : ∃ v : WeylIndex n O.columnCount → ℂ, c • ρ γ v = ζ :=
    ⟨conj c • ρ γ⁻¹ ζ, by rw [map_smul, smul_smul, mul_comm, h_norm, one_smul, ρ.self_inv_apply]⟩
  calc gramForm (c • ρ γ v) (O.vectorKernel g (stdEmbFin γ * x * k.val))
      = conj (O.conjKernel g x v) := by
        rw [← conj_gramForm, gramForm_vectorKernel_left, O.conjKernel_equivariant]
    _ = gramForm (c • ρ γ v) (c • ρ γ (O.vectorKernel g x)) := by
        rw [h_unitary, ← gramForm_vectorKernel_left, conj_gramForm]

/-- For a rational point `γ` of `U(V)`, where `V = stdSpace E n` and `stdEmbFin γ` is the image of
`γ` in the finite points, `θ_W(g, γ x) = ρ(γ) θ_W(g, x)`. With `k⁺ = O.colsPlus`, `k⁻ = O.colsMinus`
and `N` the rank of `V`, the representation `ρ` has at an infinite place `τ` the weight with
`O.columnCount τ i = k⁺(τ, i) + k⁻(τ, N - i)` columns of height `i` and the power
`O.detExp τ = -∑_{1 ≤ i < N} k⁻(τ, i)` of the determinant. -/
lemma vectorKernel_rational_mul (γ : U (stdSpace E n).J) (g : G E O.signs) (x : Gf E n) :
    O.vectorKernel g (stdEmbFin γ * x) =
      (stdSpace E n).weightRep O.columnCount O.detExp γ (O.vectorKernel g x) := by
  simpa using O.vectorKernel_equivariant γ 1 g x

/-- For `g` in `U(W)(𝔸)`, the kernel `θ_W(g, ·) = O.vectorKernel g` transforms under right
translation by the level `O.levelGroup` of `U(V)` by the character `O.levelChar`. -/
lemma vectorKernel_mul_level (k : O.levelGroup) (g : G E O.signs) (x : Gf E n) :
    O.vectorKernel g (x * k.val) = O.levelChar k • O.vectorKernel g x := by
  simpa using O.vectorKernel_equivariant 1 k g x

/-- For `g` in `U(W)(𝔸)`, the function `θ_W(g, ·) = O.vectorKernel g` as an element of `O.FormV`,
the algebraic forms on `V`: smooth functions on the finite points of `U(V)` with values in the
representation of weight `(O.columnCount, O.detExp)` that are equivariant under the rational points
and transform by `O.levelChar` under the level `O.levelGroup`. -/
def vectorKernelForm (g : G E O.signs) : O.FormV :=
  have h_level (k : O.levelGroup) :
      rightRegular ℂ (Gf E n) (WeylIndex n O.columnCount → ℂ) k.val (O.vectorKernel g) =
        O.levelChar k • O.vectorKernel g :=
    funext (O.vectorKernel_mul_level k g)
  ⟨⟨O.vectorKernel g, mem_smoothFunctions_of_eigen O.levelChar isOpen_levelOf h_level,
      fun (γ : U (stdSpace E n).J) (x : Gf E n) ↦ O.vectorKernel_rational_mul γ g x⟩,
    fun k : O.levelGroup ↦ Subtype.ext (h_level k)⟩

lemma vectorKernelForm_apply (g : G E O.signs) (h : Gf E n) :
    O.vectorKernelForm g h = O.vectorKernel g h := rfl

/-- Let `Ξ` be an algebraic form on `V`. The normalized descent `O.normalizedDescent Ξ` has at `g`
the value `⟨θ_W(g, ·), Ξ⟩`, the inner product of the form `θ_W(g, ·) = O.vectorKernelForm g` with
`Ξ`. -/
lemma normalizedDescent_eq_inner_vectorKernelForm (Ξ : O.FormV) (g : G E O.signs) :
    O.normalizedDescent Ξ g = inner ℂ (O.vectorKernelForm g) Ξ := by
  have h_sum : O.normalizedDescent Ξ g =
      stdClassSum O.levelGroup fun h : Gf E n ↦ gramForm (O.vectorKernelForm g h) (Ξ h) := by
    simp only [normalizedDescent_apply, vectorKernelForm_apply, gramForm_vectorKernel_left]
  exact h_sum.trans (LevelPlaces.LevelForm.innerAt_eq_stdClassSum 1 (O.vectorKernelForm g) Ξ).symm

end New.DescentPair

end
