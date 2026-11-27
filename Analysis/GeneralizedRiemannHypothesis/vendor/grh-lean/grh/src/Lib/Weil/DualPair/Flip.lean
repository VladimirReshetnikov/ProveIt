import Lib.Weil.DualPair.KernelLaws

/-!
# Flipping a dual pair by adjoints: Weil actions and theta kernels modulo ideals

For hermitian spaces `V`, `W`, the Weil representation on the data space of `Hom(V, W)` gives the
action `New.pairWeil V W` of the two unitary groups and the theta kernel `New.pairTheta V W`.
Taking adjoints identifies this pair with the pair `(W, V⁻)`, where `V⁻ = New.Seesaw.flipSpace V`
has the signs opposite to those of `V`. This file gives the effect of the adjoint on Weil actions,
on theta kernels and on the polynomial vectors of the Fock model (`New.flipPoly`). For theta
kernels `New.modKernel` built from functions on matrices modulo an ideal `𝔪`, the flip is expressed
by a finite Fourier transform.

## Main definitions and results

* `New.flipCoords`: the adjoint, twisted by the idele `New.flipIdele`, as a change of coordinates
  `New.CoordChange`; it depends on a unit `c` of `Ô` with `c̄ c = -1`. `New.Seesaw.flipSpace` is the
  opposite space `V⁻`.
* `New.flipCoords_map_pairWeil`, `New.exists_theta_flipCoords_map_eq_mul`,
  `New.flipCoords_map_schrodingerOp`: it intertwines the actions of the pairs once the characters
  are changed, keeps the theta functional up to a number of modulus one, and moves a datum to the
  conjugate places.
* `New.exists_pairTheta_flip`: the resulting identity of theta kernels, after a change of point.
* `New.Modulus.exists_modKernel_flip`: a kernel `New.modKernel` of (V, S) as a constant times a
  kernel of (S, T), where V has the signs opposite to T.
* `New.Exchange.exists_conj_modKernel_eq_swap`: the complex conjugate of a kernel of (S, T) as a
  kernel of (T, S).

Notions from other files:
* `New.WeilData`: Weil data on a stably unramified E. They consist of ȷ in E with ȷ = −ȷ̄, Im τȷ > 0
  for every τ in the CM type and (1 − ȷ⁻¹)/2 integral; a finite idele α for which the completed
  integers Ô are self-dual under (z, u) ↦ ψ_f(ȷαᾱzu); and a splitting character υ equal to −1 at
  uniformisers of the places w with w = w̄; its restriction to the norm-one ideles is
  `New.WeilData.upsilonU1`.
* `New.Modulus`: a nonzero ideal 𝔪 of O_E prime to its complex conjugate; `𝔪.ResidueRing` is O_E/𝔪,
  `𝔪.generator` a finite idele generating 𝔪 in Ô, equal to 1 off 𝔪, and `𝔪.primAddChar` the
  primitive additive character x ↦ ψ_f(ȷαᾱ x / 𝔪.generator) of O_E/𝔪.
* `New.Space`: a hermitian space with a point, given by a matrix J over E and x in GL_n(𝔸) with xᴴJx
  equal to the diagonal matrix of its signs at the infinite places and 1 at the finite places.
* `New.𝒮`: The Banach space 𝒮(V) of integrable functions c on 𝔸^n with c(x) = ∫ c(y)β(y,x)e(x−y) dy,
  under the L¹ norm; β is the adelic bicharacter and e the vacuum function `New.vacuumFn`.
* `New.pairWeil`: The action ω_{a,b}(g, h) = χ_{a,b}(g, h) ω(x ↦ hxg⁻¹) on 𝒮(Hom(S, T)), where
  χ_{a,b}(g, h) = a(det h) b(det g)⁻¹ is `New.pairChar`. The theta kernel `New.pairTheta` S T a b f
  (g, h) is θ(ω_{a,b}(g, h) f), where θ is the theta functional `New.Space.θ`.

## Relation to the literature

Known; see `Lib.Weil.DualPair.ThetaLiftConvergence` for sources.
-/

noncomputable section

namespace New

/-!
## The adjoint flip on Weil actions and theta kernels

The change of coordinates `New.flipCoords`, its effect on Weil actions and theta kernels, the
opposite space `New.Seesaw.flipSpace`, and its effect on the polynomial vectors of the Fock model
(`New.flipPoly`, `New.realMap_flipCoords_polyVector`).
-/

section Flip

open NumberField Matrix WeilData Fock stdLattice Fintype CoordChange G Int Weil MvPolynomial

variable {E : Type} [Field E] [CMType E] [WeilData E]
  {n a : Type} [Fintype n] [DecidableEq n] [Fintype a] [DecidableEq a]
  {s : n → ℤˣ} {t t' : a → ℤˣ} {c : (Ô E)ˣ} (hc : star (c : 𝔸f E) * c = -1) (ht : t' = -t)
  (V : Space E a t) (W : Space E n s) (V' : Space E a t')

/-- For a unit `c` of `Ô` and a sign `t`, the idele with component `t` at every infinite place and
finite part `c α / ᾱ`, where `α` is the finite idele of the Weil data. -/
@[simps! -isSimp val]
def flipIdele (c : (Ô E)ˣ) (t : ℤˣ) : (𝔸 E)ˣ :=
  MulEquiv.prodUnits.symm (t.map (castRingHom (InfinitePlace E → ℂ)).1, c.map (Ô E).subtype * α *
    star α⁻¹)

/-- For a unit c of Ô with c̄c = −1 (hypothesis `hc`) and signs t′ = −t (hypothesis `ht`), the
change of coordinates x ↦ (1, cα/ᾱ) ε_s xᴴ ε_t, where ε_s, ε_t are the standard diagonal forms of
the signs (`New.flipCoords_apply`). On points it goes from signs t′_i s_j to signs s_j t_i. It
carries functions from signs s_j t_i to signs t′_i s_j. -/
def flipCoords : CoordChange E (.id ℂ) (homSigns t s) (homSigns s t') where
  φ := starCoordEquiv (.prodComm ..) (flipIdele c ∘ homSigns t s)
  realEquiv :=
    starCoordEquiv (.prodCongr 1 (.prodComm ..)) fun i ↦ .map (castRingHom ℂ) (homSigns t s i.2)
  finEquiv := starCoordEquiv (.prodComm ..) fun _ ↦ c.map (Ô E).subtype
  apply_adelicSum := by
    -- In the finite part the factors `star α` and `star α⁻¹` cancel.
    simp [adelicSum, val_scaleIdele_fst, val_scaleIdele_snd, ← mul_assoc, mul_comm,
      starCoordEquiv, val_flipIdele, _root_.funext_iff, Prod.ext_iff]
    grind [star_mul', star_one, α.mul_inv]
  beta_realEquiv := by
    -- Conjugation exchanges the two sums in the exponent, and `t' = -t` changes their signs.
    simp [ht, realHeisenberg, signMatrix, dotProduct, Finset.sum_comm (γ := a), ← mul_assoc,
      ← cast_mul,
      mul_comm, pairSign, mulVec_diagonal, sum_prod_type, starCoordEquiv]
    grind
  vac_realEquiv := by
    simp [dotProduct, Finset.sum_comm (γ := a), ← mul_assoc, ← cast_mul, mul_comm, realVac,
      starCoordEquiv, sum_prod_type]
  selfDualAddChar_finEquiv := by
    -- The sign from `star c * c = -1` is made up for by `selfDualAddChar_star`.
    simp_all [dotProduct, Finset.sum_comm (γ := a), mul_right_comm _ _ (star c.1.1), ← mul_assoc,
      mul_comm, ← selfDualAddChar_star, star_half, starCoordEquiv, sum_prod_type]
  dot_finEquiv := by
    simp_all [dotProduct, Finset.sum_comm (γ := a), mul_right_comm _ _ (star c.1.1), ← mul_assoc,
      mul_comm, starCoordEquiv, sum_prod_type]
  finEquiv_mem x := by
    -- Both the unit `c` and conjugation preserve `Ô E`.
    erw [Submodule.smul_mem_iff' _ c]
    simp [intVectors, stdLattice]
    grind [star_star, star_mem_Ô]

/-- For a unit `c` of `Ô E` with c̄c = −1 and signs `t' = -t`, the map `φ` of the change of
coordinates `flipCoords` is computed as follows. It reads a vector `x` on pairs in `a × n` as a
matrix and sends it to ε_s xᴴ ε_t, where ε_s = `stdForm E s` and ε_t = `stdForm E t` are diag(s) and
diag(t) at the infinite places and the identity at the finite places. It then scales by the idele
`flipIdele c 1` (1 at the infinite places, cα/ᾱ at the finite places, α from the Weil data) and
reads the result back as a vector on pairs. -/
lemma flipCoords_apply (hc : star (c : 𝔸f E) * c = -1) (ht : t' = -t) (x : a × n → 𝔸 E) :
    (flipCoords (s := s) hc ht).φ x =
      matrixToVec ((flipIdele c 1).1 • (stdForm E s * (vecToMatrix x)ᴴ * stdForm E t)) := by
  simp [flipCoords, stdForm, matrixToVec, vecToMatrix, field, starCoordEquiv, pairSign,
    val_flipIdele, _root_.funext_iff, Prod.ext_iff]

/-- Let V, W be spaces of ranks |a| and |n|, let V' have the signs opposite to those of V, and let c
be a unit of Ô with c̄c = −1. Transport by `New.flipCoords` is the change of coordinates x ↦ (1,
cα/ᾱ) ε_s xᴴ ε_t, where α is the idele of the Weil data and ε are the diagonal sign forms. It sends
ω(g, h) f of the pair (V, W) to the value at (h, g) of `New.pairChar` for υ^|n| and υ^|a|, times
ω(h, g⁻) of the pair (W, V') applied to the transported f. Here ω(g, h) is the Weil action of
`New.G.onHom` (g, h), υ is `New.WeilData.upsilonU1`, and g⁻ = `New.G.neg` g has the matrix of g, in
the group of the opposite signs. -/
lemma flipCoords_map_omega (hc : star (c : 𝔸f E) * c = -1) (V : Space E a t) (W : Space E n s)
    {V' : Space E a (-t)} (g : G E t) (h : G E s) (f : 𝒮 (V.hom W)) :
    (flipCoords hc rfl).map ((V.hom W).ω (onHom (g, h)) f) =
      pairChar (upsilonU1 ^ card n) (upsilonU1 ^ card a) (h, g) •
        (W.hom V').ω (onHom (h, G.neg g)) ((flipCoords hc rfl).map f) := by
  -- The flip turns `onHom (h, neg g)` into `onHom (g, h)`, so by `map_omega` it intertwines the two
  -- Weil representations up to the ratio of the multipliers `weilMultiplier`.
  have h_mulVec (x : a × n → 𝔸 E) :
      (flipCoords (s := s) (t := t) hc rfl).φ ((onHom (h, neg g)).adeleMatrix *ᵥ x) =
        (onHom (g, h)).adeleMatrix *ᵥ (flipCoords (s := s) (t := t) hc rfl).φ x := by
    -- `↓`: `onHom_mulVec` must apply before the simp set unfolds `onHom` to a Kronecker product.
    simp [↓onHom_mulVec, flipCoords_apply, adeleMatrix_inv, Matrix.mul_assoc, -matrixToVec_smul]
  suffices h_ratio : weilMultiplier (onHom (g, h)) =
      pairChar (upsilonU1 ^ card n) (upsilonU1 ^ card a) (h, g) *
        weilMultiplier (onHom (h, neg g)) from
    map_omega _ h_mulVec h_ratio f
  -- `onHom (h, neg g)` is the reindexed transpose of `neg (onHom (g, h))⁻¹`, so they have the same
  -- `weilMultiplier`: its finite factor and the principal minors of its real factors do not see
  -- transposition or reindexing.
  have Δ_transpose : weilMultiplier (onHom (h, neg g)) = weilMultiplier (neg (onHom (g, h))⁻¹) := by
    let swap : Matrix (n × a) (n × a) (𝔸f E) →+* Matrix (a × n) (a × n) (𝔸f E) :=
      (reindexRingEquiv (𝔸f E) (Equiv.prodComm n a)).toRingHom
    have h_fin_eq : (((onHom (h, neg g)).2 : GL (a × n) (𝔸f E)) : Matrix (a × n) (a × n) (𝔸f E)) =
        ((Units.map swap.toMonoidHom ((neg (onHom (g, h))⁻¹).2 : GL (n × a) (𝔸f E)) :
          GL (a × n) (𝔸f E)) : Matrix (a × n) (a × n) (𝔸f E))ᵀ := ext fun _ _ ↦ mul_comm ..
    have h_le : (Ô E).matrix ≤ (Ô E).matrix.comap swap := by tauto
    rw [weilMultiplier, finMultiplier, IsSaturating.glMultiplier_transpose
      ((saturatingElem _).property.map_of_le_comap swap h_le) h_fin_eq]
    congrm (∏ w, starRingEnd ℂ ?_) * chiFin $(Units.ext (det_reindex_self ..))
    rw [← principalMinor_submatrix (.prodComm ..), ← principalMinor_transpose]
    congr!
    · exact ext fun _ _ ↦ mul_comm ..
    · simp [mul_comm, pairSign]
  -- So `conj_weilMultiplier_of_eq_neg` at `(onHom (g, h))⁻¹` is the required ratio, as inversion
  -- conjugates `weilMultiplier`.
  simpa [Δ_transpose, det_onHom, weilMultiplier_inv]
    using conj_weilMultiplier_of_eq_neg rfl (onHom (g, h))⁻¹.adeleMatrix_neg

/-- The opposite space of the space V with matrix J and point x: it has matrix −J and the opposite
signs. Its point is x scaled by the idele (1, ūᾱ/α), where u = `New.Weil.normNegOne` is a fixed
unit of Ô with ūu = −1. -/
@[simps -isSimp]
def Seesaw.flipSpace : Space E a (-t) where
  J := -V.J
  x := .scalar a (star (flipIdele normNegOne 1)) * V.x
  gram_point := by
    -- The scalar is `1` at the infinite places, where the signs change with `J`; its finite part
    -- has norm `-1`, which makes up for the sign of `-J`.
    simp [Matrix.map_neg, V.gram_point, stdForm, ← smul_eq_diagonal_mul, ← diagonal_smul,
      val_flipIdele, Prod.ext_iff, _root_.funext_iff]
    grind [star_normNegOne_mul_self, star_mul, star_one, α.mul_inv]

/-- The adjoint intertwines the actions of the pairs. Let V, W be spaces of ranks |a| and |n|, and
let V' have the signs opposite to those of V. Transport by `New.flipCoords` takes ω_{a',b}(g, h) of
the pair (V, W) to ω_{b⁻¹υ^|n|, a'⁻¹υ^|a|}(h, g⁻) of the pair (W, V'); these are the characters that
belong to the inverse splitting characters. Here ω is `New.pairWeil`, υ is
`New.WeilData.upsilonU1` and g⁻ = `New.G.neg` g has the matrix of g. -/
lemma flipCoords_map_pairWeil (hc : star (c : 𝔸f E) * c = -1) (V : Space E a t) (W : Space E n s)
    (V' : Space E a (-t)) (a' b : AutChar E) (g : G E t) (h : G E s) (f : 𝒮 (V.hom W)) :
    (flipCoords hc rfl).map (pairWeil V W a' b (g, h) f) =
      pairWeil W V' (b⁻¹ * upsilonU1 ^ card n) (a'⁻¹ * upsilonU1 ^ card a) (h, G.neg g)
        ((flipCoords hc rfl).map f) := by
  -- The powers of `upsilonU1` in the new characters give the factor of `flipCoords_map_omega`.
  have h_char : pairChar a' b (g, h) * pairChar (upsilonU1 ^ card n) (upsilonU1 ^ card a) (h, g) =
      pairChar (b⁻¹ * upsilonU1 ^ card n) (a'⁻¹ * upsilonU1 ^ card a) (h, G.neg g) := by
    simp [field]
  rw [pairWeil_apply, pairWeil_apply, map_smul, flipCoords_map_omega, smul_smul, h_char]

/-- The adjoint keeps the theta functional up to a number of modulus one. Let E be a CM field with
Weil data and finite idele α, and let c be a unit of Ô with c̄c = −1. Let V' have the signs t′ = −t
opposite to those of V, and let its point be `star (flipIdele c 1) • x_V`, that is, x_V multiplied
by 1 at the infinite places and by conj(cα/ᾱ) at the finite places.

Then there is z ∈ ℂ with ‖z‖ = 1 such that θ(f^φ) = z θ(f) for all f in 𝒮(Hom(V, W)). Here f^φ on
Hom(W, V') is the transport of f by φ = `New.flipCoords`. -/
lemma exists_theta_flipCoords_map_eq_mul
    (hV' : (V'.x : Matrix a a (𝔸 E)) = star (flipIdele c 1 : 𝔸 E) • V.x) :
    ∃ z : ℂ, ‖z‖ = 1 ∧
      ∀ f : 𝒮 (V.hom W), (W.hom V').θ ((flipCoords hc ht).map f) = z * (V.hom W).θ f := by
  -- The flip matches rational points: the adjoint of a rational matrix `ξ` is `V.J⁻¹ * ξᴴ * W.J`.
  have h_ratVectors (x : a × n → 𝔸 E)
      (hx : (flipCoords (s := s) hc ht).φ x ∈ (V.hom W).ratVectors) :
      (1 : G E (homSigns s t')) • x ∈ (W.hom V').ratVectors := by
    obtain ⟨ξ, hξ⟩ := V.mem_ratVectors_hom.1 hx
    refine W.mem_ratVectors_hom.2 ⟨V.J⁻¹ * ξᴴ * W.J, ?_⟩
    simp_all [← conjTranspose_map_toAdele, V.map_J_inv, W.map_J, flipCoords_apply,
      conjTranspose_nonsing_inv, Matrix.mul_assoc, -matrixToVec_smul]
  -- Hence the two theta functionals are proportional, by the uniqueness of theta functionals.
  obtain ⟨z, hz, hθ⟩ :=
    (flipCoords hc ht).exists_theta_omega_map (V.hom W) (W.hom V') 1 h_ratVectors
  have hz_ne : z ≠ 0 := fun hz_zero ↦ by simp [hz_zero] at hz
  refine ⟨z⁻¹, by rw [norm_inv, hz, inv_one], fun f ↦ ?_⟩
  simpa [eq_inv_mul_iff_mul_eq₀ hz_ne] using (hθ f).symm

/-- The adjoint moves a datum to the conjugate places. Let `A` be a set of finite places disjoint
from its conjugate and `Ψ` a Schwartz–Bruhat function above `A`. Transport by `New.flipCoords`
sends the vector named by `Ψ` at `A` on the vacuum of Hom(V, W) to the vector named by
`y ↦ Ψ (c yᴴ)` at the conjugate of `A` on the vacuum of Hom(W, V'). -/
lemma flipCoords_map_schrodingerOp {A : Set (FinPlace E)} (hA : A.IsConjDisjoint)
    (Ψ : (n × a → 𝔸f E) → ℂ) [hΨ : IsSchwartzBruhat A Ψ] :
    (flipCoords hc ht).map ((V.hom W).schrodingerOp A Ψ (V.hom W).vacElem) =
      (W.hom V').schrodingerOp (star ⁻¹' A)
        (fun y : a × n → 𝔸f E ↦ Ψ (matrixToVec ((c : 𝔸f E) • (vecToMatrix y)ᴴ)))
          (W.hom V').vacElem := by
  have h_apply (y : a × n → 𝔸f E) :
      (flipCoords (s := s) hc ht).finEquiv y = matrixToVec ((c : 𝔸f E) • (vecToMatrix y)ᴴ) := rfl
  have hA_star : (star ⁻¹' A).IsConjDisjoint := by
    simpa [Set.IsConjDisjoint, Set.preimage_preimage] using Disjoint.symm hA
  -- The finite part carries the part at the conjugate of a set of places to the part at that set.
  have h_idem (B : Set (FinPlace E)) (y : a × n → 𝔸f E) :
      (flipCoords (s := s) hc ht).finEquiv (idem (star ⁻¹' B) • y) =
        idem B • (flipCoords (s := s) hc ht).finEquiv y := by
    simp [h_apply, matrixToVec, vecToMatrix, _root_.funext_iff, mul_left_comm, star_idem]
  have h_conjClosure : (star ⁻¹' A).conjClosure = star ⁻¹' A.conjClosure := by
    simp [Set.conjClosure]
  refine map_schrodingerOp _ (h_idem A) (fun y ↦ ?_) hA hA_star
  rw [h_conjClosure, h_idem]

/-- The adjoint followed by a change of point. Let V, W be spaces of ranks |a| and |n|, let V' be a
space with the signs t′ = −t opposite to those of V, and let l in the group of V' satisfy
x_{V'} l = (1, conj(cα/ᾱ)) x_V on the points. For each character b there is a z of modulus one such
that θ^{W,V'}_{b⁻¹υ^|n|, a'⁻¹υ^|a|}(f^φ)(h, g') = z θ^{V,W}_{a',b}(f)(g, h)
for all characters a', data f, and g, h, g' where g' has the matrix l g. Here θ is `New.pairTheta`,
υ is `New.WeilData.upsilonU1` and f^φ is the transport of f by φ = `New.flipCoords`. -/
lemma exists_pairTheta_flip (l : G E t')
    (hl : (V'.x : Matrix a a (𝔸 E)) * l.adeleMatrix = star (flipIdele c 1 : 𝔸 E) • V.x)
      (b : AutChar E) :
    ∃ z : ℂ, ‖z‖ = 1 ∧
      ∀ (a' : AutChar E) (f : 𝒮 (V.hom W)) (g : G E t) (h : G E s) (g' : G E t'),
        g'.adeleMatrix = l.adeleMatrix * g.adeleMatrix →
        pairTheta W V' (b⁻¹ * upsilonU1 ^ card n) (a'⁻¹ * upsilonU1 ^ card a)
            ((flipCoords hc ht).map f) (h, g') =
          z * pairTheta V W a' b f (g, h) := by
  subst ht
  -- The space `V'.move l` has the point that the adjoint asks for.
  obtain ⟨z, hz, hθ⟩ := exists_theta_flipCoords_map_eq_mul hc rfl V W (V'.move l) hl
  let b' : AutChar E := b⁻¹ * upsilonU1 ^ card n
  refine ⟨b'.val l.det * z, by simp [Circle.norm_coe, hz], fun a' f g h g' hg' ↦ ?_⟩
  let a'' : AutChar E := a'⁻¹ * upsilonU1 ^ card a
  let f' : 𝒮 (W.hom V') := (flipCoords hc rfl).map f
  obtain rfl : g' = l * neg g := ext_adeleMatrix (by simpa using hg')
  have h_adjoint :
      pairTheta W (V'.move l) b' a'' f' (h, neg g) = z * pairTheta V W a' b f (g, h) := by
    unfold pairTheta
    rw [← hθ, flipCoords_map_pairWeil]
    rfl
  -- Move the point back by `l`.
  have hW : W.move 1 = W := by simp [Space.move]
  have h_move : pairTheta (W.move 1) (V'.move l) b' a'' f' (h, neg g) =
      (b'.val l.det : ℂ)⁻¹ * pairTheta W V' b' a'' f' (h, l * neg g) := by
    simpa using Space.pairTheta_move W V' b' a'' 1 h l (neg g) f'
  rw [hW] at h_move
  rw [mul_assoc, ← h_adjoint, h_move, mul_inv_cancel_left₀ (Circle.coe_ne_zero _)]

/-- The ℂ-algebra map on polynomials sending the variable X_(τ,i,j) to −s_i t_j X_(τ,j,i):
transposition with signs. -/
def flipPoly (t : a → ℤˣ) (s : n → ℤˣ) :
    MvPolynomial (InfinitePlace E × n × a) ℂ →ₐ[ℂ] MvPolynomial (InfinitePlace E × a × n) ℂ :=
  bind₁ fun p : InfinitePlace E × n × a ↦ (homSigns (-t) s p.2 : ℂ) • X (R := ℂ) (p.1, p.2.swap)

/-- The archimedean part `New.CoordChange.realMap` of `New.flipCoords` sends the Fock vector of a
polynomial `P` to the Fock vector of `New.flipPoly t' s P`. -/
lemma realMap_flipCoords_polyVector (hc : star (c : 𝔸f E) * c = -1) (ht : t' = -t)
    (P : MvPolynomial (InfinitePlace E × n × a) ℂ) :
    (flipCoords (s := s) hc ht).realMap (polyVector (realSigns E (homSigns t s)) P) =
      polyVector (realSigns E (homSigns s t')) (flipPoly t' s P) := by
  -- The real part of `flipCoords` fixes the Gaussian, so it suffices to compare the points at which
  -- `P` is evaluated: the coordinates `holomorphicCoord` are swapped and multiplied by signs.
  ext x
  have h_coord :
      holomorphicCoord (realSigns E (homSigns t s)) ((flipCoords (s := s) hc ht).realEquiv x) =
        fun i ↦ -(s i.2.1 * t' i.2.2 *
          holomorphicCoord (realSigns E (homSigns s t')) x (i.1, i.2.swap)) := by
    aesop (add simp [holomorphicCoord_eq, flipCoords, mul_comm, starCoordEquiv, pairSign,
      units_ne_iff_eq_neg])
  simp [realMap, ← aeval_eq_eval, aeval_bind₁, ↓vac_realEquiv, flipPoly, h_coord, pairSign]

end Flip

/-!
## Flipped and conjugate theta kernels modulo an ideal

A theta kernel `New.modKernel` S T a b 𝔪 D P g h is attached to spaces S, T, characters a, b of
[U(1)], a function D on matrices modulo 𝔪 and a polynomial P. A kernel of one pair is written as a
constant times a kernel of the reversed pair.

The idea: the indicator of a class modulo 𝔪 comes from a translate of the vacuum, and after the flip
this translate is the datum of an additive character modulo 𝔪. Throughout υ is
`New.WeilData.upsilonU1`, and a constant is controlled only through the square of its modulus.
-/

section KernelFlip

open NumberField Matrix ComplexConjugate WeilData Space Fintype G Gf CoordChange Weil Exchange

variable {E n m : Type} [Field E] [CMType E] [Fintype n] [DecidableEq n]
  [Fintype m] [DecidableEq m] {s : n → ℤˣ} {t : m → ℤˣ} [WeilData E]
  (𝔪 : Modulus E) (S : Space E n s) (T : Space E m t)

/-- The scalar matrix ū / u in the finite adelic unitary group `Gf E n` of rank n, where u is α
times the chosen idele generating 𝔪. The index type n defaults to `Unit`: a bare `𝔪.flipScalar`
is the rank-one case `𝔪.flipScalar Unit`. -/
noncomputable def Modulus.flipScalar (n := Unit) [Fintype n] [DecidableEq n] : Gf E n :=
  scalarFin n (divStar (star (𝔪.generator * α)))

/-- The Heisenberg translate of the vacuum of a space `X` by the finite vector with entries
−α w_i / 𝔪.generator at the places dividing 𝔪 and 0 at the other places (`New.finVec` multiplies
by α), for an integral vector `w`. -/
private def Modulus.vacTranslate {ι : Type} [Fintype ι] [DecidableEq ι] {r : ι → ℤˣ}
    (X : Space E ι r) (w : ι → Ô E) : 𝒮 X :=
  X.ϱ (finVec (idem 𝔪.places • -(↑𝔪.generator⁻¹ : 𝔸f E) • Subtype.val ∘ w)) X.vacElem

/-- The translate of the vacuum by a vector above 𝔪 is the operator named by the indicator of the
translated integral box, applied to the vacuum. -/
private lemma Modulus.vacTranslate_eq_schrodingerOp_boxIndicator {ι : Type} [Fintype ι]
    [DecidableEq ι] {r : ι → ℤˣ} (X : Space E ι r) (w : ι → Ô E) :
    𝔪.vacTranslate X w =
      X.schrodingerOp 𝔪.places
        (fun x : ι → 𝔸f E ↦
          boxIndicator ι 𝔪.places (x + -(↑𝔪.generator⁻¹ : 𝔸f E) • Subtype.val ∘ w))
        X.vacElem := by
  have h_idem : idem 𝔪.places.conjClosure * idem 𝔪.places = idem 𝔪.places := by
    grind [idem_mul_self, idem_mul_star, idem_conjClosure_eq_add_star, 𝔪.isConjDisjoint_places]
  rw [vacTranslate, ← isSchwartzBruhat_boxIndicator.schrodingerAct_idem 𝔪.isConjDisjoint_places,
    schrodingerOp_schrodingerAct_boxIndicator 𝔪.isConjDisjoint_places, projOn_vacElem,
    smul_smul _ (idem _), h_idem]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (𝔪 : Modulus E) in
/-- The module of the idele `𝔪.generator` is the inverse of the number N𝔪 of elements of O_E/𝔪. -/
lemma Modulus.finIdeleAbs_generator :
    finIdeleAbs 𝔪.generator = (card 𝔪.ResidueRing : ℝ)⁻¹ := by
  -- The idele generates the kernel of the reduction of `Ô E` onto `𝔪.ResidueRing`.
  have h_ker : Ideal.span {(⟨𝔪.generator.val, 𝔪.generator_mem⟩ : Ô E)} =
      RingHom.ker 𝔪.reduction := by
    ext x
    rw [RingHom.mem_ker, reduction_eq_zero_iff_generator_inv_mul_mem, Ideal.mem_span_singleton]
    exact ⟨fun ⟨y, hy⟩ ↦ by simp [hy], fun hx ↦ ⟨⟨_, hx⟩, Subtype.ext (by simp)⟩⟩
  have h_index : genIndex 𝔪.generator.val = card 𝔪.ResidueRing := by
    rw [genIndex_eq_card isOpen_Ô isCompact_Ô 𝔪.generator_mem (Units.isUnit _), h_ker,
      Nat.card_congr (RingHom.quotientKerEquivOfSurjective 𝔪.reduction_surjective).toEquiv,
      Nat.card_eq_fintype_card]
  rw [← h_index, genIndex_eq_inv_finIdeleAbs, inv_inv]

/-- Let u = ḡ / g for the generator g of 𝔪, as a scalar in the finite unitary group of rank m.
For a space V of rank m with signs −t, a space S of rank n and characters a, b there is one
constant C, with |C|² = N𝔪^(mn), such that ω_{a,b}(u, 1) sends the vacuum translate
(`New.Modulus.vacTranslate`) by every integral w to C times the operator named by the lift of the
point mass at the class of w modulo 𝔪, applied to the vacuum. Here ω_{a,b} is `New.pairWeil` of the
pair (V, S), and N𝔪 is the number of elements of O_E/𝔪. -/
private lemma Modulus.exists_pairWeil_vacTranslate (V : Space E m (-t)) (a b : AutChar E) :
    ∃ C : ℂ, ‖C‖ ^ 2 = card 𝔪.ResidueRing ^ (card m * card n) ∧ ∀ w : n × m → Ô E,
      pairWeil V S a b ((1, scalarFin m (divStar (star 𝔪.generator))), 1, 1)
          (𝔪.vacTranslate (V.hom S) w) =
        C • (V.hom S).schrodingerOp 𝔪.places (𝔪.liftFn (Pi.single (𝔪.reduction ∘ w) 1))
          (V.hom S).vacElem := by
  classical
  have h_disj : 𝔪.places.IsConjDisjoint := 𝔪.isConjDisjoint_places
  let u : Gf E m := scalarFin m (divStar (star 𝔪.generator))
  have hu : u ∈ supportedOn m 𝔪.places := by
    simp_all [u, atPlace, scalarFin, generator_spec, map_mul, Units.ext_iff, map_zero, coe_divStar]
  -- `C` is the factor in `pairWeil_schrodingerOp_of_mem_supportedOn`. Above `𝔪` the determinant of
  -- `u` is `g⁻¹ ^ m`, of module `N𝔪 ^ m`.
  let C : ℂ := (a.spaceChar (card m)).val (detOn 𝔪.places (1 : Gf E n).val) /
      (b.spaceChar (card n)).val (detOn 𝔪.places u.val) *
    √(ideleAbs (detOn 𝔪.places u.val)) ^ card n /
    √(ideleAbs (detOn 𝔪.places (1 : Gf E n).val)) ^ card m
  have h_det : detOn 𝔪.places u.val * finIdeleIncl (𝔪.generator ^ card m) = 1 := by
    ext w
    · simp
    · have h_ne : 𝔪.generator.val w ≠ 0 := (𝔪.generator.isUnit.map (evalAt w)).ne_zero
      rw [Units.val_mul, Prod.snd_mul, ← evalAt_apply, map_mul, evalAt_apply, detOn_apply]
      split_ifs with hw
      · simp [u, atPlace, scalarFin, coe_divStar, map_zero, map_mul, h_ne,
          𝔪.generator_apply_of_notMem (𝔪.not_le_star w hw)]
      · simp [𝔪.generator_apply_of_notMem hw]
  have h_abs : ideleAbs (detOn 𝔪.places u.val) = card 𝔪.ResidueRing ^ card m := by
    rw [eq_inv_of_mul_eq_one_left h_det, map_inv]
    change (finIdeleAbs (𝔪.generator ^ card m))⁻¹ = _
    rw [map_pow, finIdeleAbs_generator, inv_pow, inv_inv]
  have h_norm : ‖C‖ ^ 2 = card 𝔪.ResidueRing ^ (card m * card n) := by
    simp [C, h_abs, Circle.norm_coe, ← pow_mul, mul_comm _ 2, pow_mul _ 2]
  simp only [vacTranslate_eq_schrodingerOp_boxIndicator]
  -- `pairWeil_schrodingerOp_of_mem_supportedOn`: `u` acts on a named function by `x ↦ x u`, up to a
  -- constant; the congruence term leaves the equation of the two functions.
  refine ⟨C, h_norm, fun w ↦ (pairWeil_schrodingerOp_of_mem_supportedOn
    h_disj hu (one_mem _) _).trans congr(_ • schrodingerOp _ _ $(?_) _)⟩
  -- Above `𝔪` the scalar `u` is `𝔪.generator⁻¹`, so the box moved by `u` is the coset of `w`:
  -- after unfolding, both sides are indicators, of x u − w / 𝔪.generator and of
  -- (x − w) / 𝔪.generator being integral above 𝔪, and `generator_spec` matches the two conditions.
  rw [𝔪.liftFn_single]
  ext
  simp [u, boxIndicator, mem_integralBox, mem_Ô, vecToMatrix, scalarFin, idem_apply, coe_divStar,
    matrixToVec]
  congr! 6
  grind [generator_spec]

/-- Let c be a unit of Ô such that −c satisfies c̄c = −1 (the form in which the flip takes it), V a
space of rank m with signs −t, and v an integral n × m matrix. The flip φ = `New.flipCoords` for
the unit −c carries the vacuum translate by v (`New.Modulus.vacTranslate`) of Hom(V, S) to the
operator of Hom(S, T) named by the lift of the character ρ ↦ ψ(tr(ρ v)) modulo 𝔪, applied to the
vacuum; here ψ is `New.Modulus.primAddChar` shifted by −c̄. -/
private lemma Modulus.flipCoords_map_vacTranslate {c : (Ô E)ˣ}
    (hc_neg : star ((-c : (Ô E)ˣ) : 𝔸f E) * ((-c : (Ô E)ˣ) : 𝔸f E) = -1) (V : Space E m (-t))
    (v : Matrix n m (Ô E)) :
    (flipCoords (s := s) hc_neg (neg_neg t).symm).map (𝔪.vacTranslate (V.hom S) (matrixToVec v)) =
      (S.hom T).schrodingerOp 𝔪.places
        (𝔪.liftFn ((fun ρ : Matrix m n 𝔪.ResidueRing ↦
          𝔪.primAddChar.mulShift (𝔪.reduction (-star c))
          (ρ * of fun (i : n) (j : m) ↦ 𝔪.reduction (v i j)).trace) ∘ vecToMatrix))
        (S.hom T).vacElem := by
  -- The flipped translate is again a translate of the vacuum, by a vector at the conjugate places,
  -- and the character names it (`schrodingerOp_char_eq_translate_projOn`).
  have hc : star (c : 𝔸f E) * c = -1 := by simpa using hc_neg
  let y : m × n → Ô E := -star (c : Ô E) • matrixToVec v ∘ .swap
  have h_vec : idem 𝔪.places • -(↑𝔪.generator⁻¹ : 𝔸f E) • Subtype.val ∘ matrixToVec v =
      (flipCoords (s := s) hc_neg (neg_neg t).symm).finEquiv
        (star (idem 𝔪.places • (↑𝔪.generator⁻¹ : 𝔸f E) • Subtype.val ∘ y)) := by
    simp [y, flipCoords, starCoordEquiv, funext_iff, matrixToVec]
    grind
  rw [vacTranslate, h_vec, ← apply_finVec, map_rho, map_vacElem, ← projOn_vacElem (S := 𝔪.places),
    ← 𝔪.schrodingerOp_char_eq_translate_projOn, projOn_vacElem]
  congr with x
  simp [y, vecToMatrix, trace, mul_apply, dotProduct, sum_prod_type, mul_left_comm (x _),
    ← Finset.mul_sum, matrixToVec]

/-- Flip of a pair. Let c be a unit of Ô with c̄c = −1, T a space of rank m, V a space with the
opposite signs whose point is (1, c) times that of T (hypothesis `hV`), and S a space of rank n.
Thus T has the negated form of V and the point of V times (1, c⁻¹), where c⁻¹ = −c̄. For characters
a, b of [U(1)] there is a complex C such that (a) |C|² · N𝔪^(mn) = 1, N𝔪^(mn) being the number of
m × n matrices over O_E/𝔪, and (b) θ^{V,S}_{a,b}[D,P](g⁻,h) = C θ^{S,T}_{b⁻¹υⁿ,a⁻¹υᵐ}[D̂,P′](h,gu)
for all D, P, g, h. Here θ[D,P] is the kernel `New.modKernel` of the function D modulo 𝔪 and the
polynomial P, and g⁻ = `New.G.neg` g is g in the group of V. The character υ is the splitting
character restricted to the norm-one ideles. D̂(ρ) = ∑_v D(v)ψ(−c̄ tr ρv), where
ψ = `New.Modulus.primAddChar` is the primitive character of O_E/𝔪. P′ = `New.flipPoly` of P sends
X_(τ,i,j) to −s_i t_j X_(τ,j,i). u = `New.Modulus.flipScalar` of rank m is the scalar ū₀/u₀, with u₀
equal to α times the idele generating 𝔪, placed at the finite places. -/
lemma Modulus.exists_modKernel_flip (c : (Ô E)ˣ) (hc : star (c : 𝔸f E) * c = -1)
    (V : Space E m (-t)) (hV : ((1, c) : 𝔸 E) • (T.x : Matrix m m (𝔸 E)) = V.x) (a b : AutChar E) :
    ∃ C : ℂ,
      ‖C‖ ^ 2 * card 𝔪.ResidueRing ^ (card m * card n) = 1 ∧
      ∀ (D : Matrix n m 𝔪.ResidueRing → ℂ) (P : MvPolynomial (InfinitePlace E × n × m) ℂ)
        (g : G E t) (h : G E s),
        modKernel V S a b 𝔪 D P (G.neg g) h =
          C * modKernel S T (b⁻¹ * upsilonU1 ^ card n) (a⁻¹ * upsilonU1 ^ card m) 𝔪
            (matrixFourier (𝔪.primAddChar.mulShift (𝔪.reduction (-star c))) D) (flipPoly t s P) h
            (g * (1, 𝔪.flipScalar m)) := by
  classical
  -- By linearity take for `D` the indicator of one class `v`. The scalar `u` carries a translate
  -- of the vacuum to `C` times the datum of `D`; `exists_pairTheta_flip` flips the kernel of that
  -- translate, and the flipped translate is the datum of the character `ρ ↦ ψ (tr (ρ v))`.
  let u : Gf E m := scalarFin m (divStar (star 𝔪.generator))
  obtain ⟨C, hC_norm, hC⟩ := 𝔪.exists_pairWeil_vacTranslate S V a b
  -- The scalar `l = ᾱ / α` links the points of `T` and `V` as the flip requires.
  let l : G E t := (1, scalarFin m (divStar (star α)))
  have h_point : (T.x : Matrix m m (𝔸 E)) * l.adeleMatrix = star (flipIdele (-c) 1 : 𝔸 E) •
    V.x := by
    simp [l, ← hV, val_flipIdele, smul_smul, Prod.star_def, adeleMatrix_scalarFin, coe_divStar]
    grind
  have hc_neg : star ((-c : (Ô E)ˣ) : 𝔸f E) * ((-c : (Ô E)ˣ) : 𝔸f E) = -1 := by simpa using hc
  -- `exists_pairTheta_flip`: a number `z` of modulus one relates the theta function of `(V, S)` at
  -- `(g, h)` to that of `(S, T)` at `(h, l g)`, for the datum moved by `flipCoords`.
  obtain ⟨z, hz, h_flip⟩ := exists_pairTheta_flip hc_neg (neg_neg t).symm V S T l h_point b
  have h_norm : ‖(z * C)⁻¹‖ ^ 2 * card 𝔪.ResidueRing ^ (card m * card n) = 1 := by
    rw [norm_inv, norm_mul, hz, one_mul, inv_pow, hC_norm, inv_mul_cancel₀ (by positivity)]
  refine ⟨(z * C)⁻¹, h_norm, fun D P g h ↦ ?_⟩
  let ψ : AddChar 𝔪.ResidueRing ℂ := 𝔪.primAddChar.mulShift (𝔪.reduction (-star c))
  have h_single (v : Matrix n m 𝔪.ResidueRing) :
      z * C * modKernel V S a b 𝔪 (Pi.single v 1) P (.neg g) h =
        modKernel S T (b⁻¹ * upsilonU1 ^ card n) (a⁻¹ * upsilonU1 ^ card m) 𝔪
          (fun ρ ↦ ψ (ρ * v).trace) (flipPoly t s P) h (g * (1, 𝔪.flipScalar m)) := by
    obtain ⟨v, rfl⟩ := 𝔪.reduction_surjective.comp_left.comp_left v
    have h_mat : (g * (1, 𝔪.flipScalar m)).adeleMatrix = l.adeleMatrix *
      (G.neg g * (1, u)).adeleMatrix := by
      -- `-map_mul` keeps the image of a product whole, in the form that `grind` matches.
      simp [l, u, flipScalar, -map_mul, smul_smul, adeleMatrix_scalarFin, coe_divStar]
      grind
    -- Move `(1, u)` from the datum into the group argument (`hC`, `pairTheta_mul`), then flip.
    calc
      _ = z * pairTheta V S a b
            (integrated _ (Fock.polyVector _ P) (𝔪.vacTranslate (V.hom S) (matrixToVec v)))
            (G.neg g * (1, u), h) := by
        -- `erw`, `rfl`: `modKernel` and `modDatum` unfold, and `pairTheta` is linear in the datum,
        -- only up to definitional unfolding.
        erw [modKernel, modDatum, Pi.single_comp_equiv (.curry ..), mul_assoc, ← smul_eq_mul C,
          ← map_smul, ← map_smul, ← map_smul, ← hC, ← pairWeil_integrated_fin, ← pairTheta,
          ← pairTheta_mul, Prod.mk_mul_mk, mul_one h]
        rfl
      _ = _ := by
        -- `erw`, `rfl`: the flipped datum matches `pairTheta` and `modKernel` only after unfolding.
        erw [← h_flip _ _ _ _ _ h_mat, map_integrated, realMap_flipCoords_polyVector,
          𝔪.flipCoords_map_vacTranslate S T hc_neg V v]
        rfl
  -- Expand `D` in indicators of classes; both kernels are linear in their datum.
  have h_ft : matrixFourier ψ D = ∑ v, D v • fun ρ ↦ ψ (ρ * v).trace := (Finset.sum_fn ..).symm
  have hzC_ne : z * C ≠ 0 := fun h0 ↦ by simp [h0] at h_norm
  nth_rw 1 [eq_inv_mul_iff_mul_eq₀ hzC_ne, pi_eq_sum_univ' D, h_ft, ← modKernelBilin_apply,
    ← modKernelBilin_apply]
  simp [Finset.mul_sum, mul_left_comm _ (D _), h_single]

/-- Reversal of a pair. For spaces S, T of ranks n, m and characters a, b there is a complex c
such that (a) |c|² · N𝔪^(nm) = 1, with N𝔪 the number of elements of O_E/𝔪, and (b) for all
D, P, g, h the complex conjugate of θ^{S,T}_{a,b}[D,P](g,h) is c θ^{T,S}_{b,a}[D′,P′](h,gu).
Here D′ is the Fourier transform of D̄ for `New.Modulus.primAddChar`, P′ is the signed transpose
`New.flipPoly` of P̄ (the polynomial with conjugate coefficients) and u = `New.Modulus.flipScalar`,
placed at the finite places. -/
lemma Exchange.exists_conj_modKernel_eq_swap (a b : AutChar E) :
    ∃ c : ℂ,
      ‖c‖ ^ 2 * card 𝔪.ResidueRing ^ (card n * card m) = 1 ∧
      ∀ (D : Matrix m n 𝔪.ResidueRing → ℂ) (P : MvPolynomial (InfinitePlace E × m × n) ℂ)
        (g : G E s) (h : G E t),
        conj (modKernel S T a b 𝔪 D P g h) =
          c * modKernel T S b a 𝔪
            (matrixFourier 𝔪.primAddChar fun v : Matrix m n 𝔪.ResidueRing ↦ conj (D v))
            (flipPoly s t (P.map conj)) h (g * 𝔪.flipScalar n) := by
  -- Conjugation passes to `S.neg` (`exists_conj_modKernel_eq_mul_modKernel_neg`, at the cost of a
  -- phase `c` and of the factor `𝔪.normNegOne⁻¹` in `D`), and the flip comes back to `S` on the
  -- other side.
  obtain ⟨c, hc_norm, h_neg⟩ := exists_conj_modKernel_eq_mul_modKernel_neg S T
  -- `h_flip`: the flip of a pair for (S.neg, T) and the characters a⁻¹υⁿ, b⁻¹υᵐ, with the unit
  -- `normNegOne`.
  obtain ⟨C, hC_norm, h_flip⟩ :=
    𝔪.exists_modKernel_flip T S normNegOne star_normNegOne_mul_self S.neg rfl
      (a⁻¹ * upsilonU1 ^ card n) (b⁻¹ * upsilonU1 ^ card m)
  refine ⟨c * C, by simp [hc_norm, hC_norm], fun D P g h ↦ ?_⟩
  -- In the Fourier transform substitute `v ↦ 𝔪.normNegOne⁻¹ • v`; the inverse of `normNegOne` is
  -- `-star normNegOne`.
  have h_ft : matrixFourier (𝔪.primAddChar.mulShift (𝔪.reduction (-(star normNegOne : (Ô E)ˣ))))
      (fun v ↦ conj (D (𝔪.normNegOne⁻¹ • v))) = matrixFourier 𝔪.primAddChar fun v ↦ conj (D v) := by
    ext ρ
    apply sum_equiv (MulAction.toPerm 𝔪.normNegOne⁻¹)
    simp [-map_neg]
    -- Termwise the characters agree: `𝔪.normNegOne⁻¹` is the class of `-star normNegOne`.
    exact fun v ↦ Or.inl rfl
  rw [h_neg a b 𝔪, h_flip, h_ft, mul_assoc]
  simp [inv_mul_cancel_comm]

/-- Flip for lines. Let S have rank n, let ε = ±1 in ℤˣ, and let L, L′ be the standard lines
`New.signedSpace` of signs −ε and ε. For every modulus 𝔪, characters b, a′ and k in the finite
unitary group of rank one there are an additive character ψ of O_E/𝔪 and a nonzero c such that
(a) |c|² · N𝔪ⁿ = 1, N𝔪ⁿ being the number of columns of length n over O_E/𝔪, and
(b) θ^{L,S}_{1,b}[D,P](k,h) = c θ^{S,L′}_{a′,υ}[D̂,P′](h,kf) for all P, D, h.
Here θ[D,P] is `New.modKernel`, υ is `New.WeilData.upsilonU1`, D̂ is the Fourier transform
`New.Exchange.matrixFourier` of D for ψ, P′ is the signed transpose `New.flipPoly` of P,
f = `New.Modulus.flipScalar`, and k, kf are placed at the finite places. Any a′ is allowed since c
may depend on k. -/
lemma exists_modKernel_flip_line (ε : ℤˣ) (𝔪 : Modulus E) (b a' : AutChar E) (k : Gf E Unit) :
    ∃ ψ : AddChar 𝔪.ResidueRing ℂ, ∃ c : ℂˣ,
      ‖(c : ℂ)‖ ^ 2 * card (n → 𝔪.ResidueRing) = 1 ∧
      ∀ (P : MvPolynomial (InfinitePlace E × n × Unit) ℂ) (D : Matrix n Unit 𝔪.ResidueRing → ℂ)
        (h : G E s),
        modKernel (signedSpace E fun _ : Unit ↦ -ε) S 1 b 𝔪 D P (1, k) h =
          c * modKernel S (signedSpace E fun _ : Unit ↦ ε) a' upsilonU1 𝔪 (matrixFourier ψ D)
            (flipPoly (fun _ : Unit ↦ ε) s P) h (1, k * 𝔪.flipScalar Unit) := by
  -- The line of sign `-ε` is the flip of the line of sign `ε` for the unit `c₀ = normNegOne ^ ε`;
  -- passing to an arbitrary character `a'` costs a phase by `modKernel_twist`.
  let c₀ : (Ô E)ˣ := normNegOne ^ (ε : ℤ)
  have h_star_c₀ : star (c₀ : 𝔸f E) * c₀ = -1 := by
    fin_cases ε <;> simp [c₀, normNegOne_inv, mul_comm ((normNegOne : (Ô E)ˣ) : 𝔸f E)]
  have h_point :
      ((1, c₀) : 𝔸 E) • ((signedSpace E fun _ : Unit ↦ ε).x : Matrix Unit Unit (𝔸 E)) =
        (signedSpace E fun _ : Unit ↦ -ε).x := by
    fin_cases ε <;> simp [c₀, signedSpace, ← ext_iff, normNegOneIdele, normNegOne_inv]
  -- The flip of a pair, for T the line of sign `ε` and V the line of sign `-ε`.
  obtain ⟨C, hC, h_flip⟩ := 𝔪.exists_modKernel_flip S _ c₀ h_star_c₀ _ h_point 1 b
  have hC_ne : C ≠ 0 := fun hC_zero ↦ by simp [hC_zero] at hC
  let μ : AutChar E := b⁻¹ * upsilonU1 ^ card n / a'
  let g : G E fun _ : Unit ↦ ε := (1, k * 𝔪.flipScalar Unit)
  let c : ℂˣ := Units.mk0 C hC_ne * Circle.toUnits (μ.val g.det)
  refine ⟨𝔪.primAddChar.mulShift (𝔪.reduction (-star c₀)), c,
    by simpa [c, Circle.norm_coe] using hC, fun P D h ↦ (h_flip D P (1, k) h).trans ?_⟩
  rw [← mul_div_cancel a' (_ * _), inv_one, mul_comm 1, modKernel_twist]
  simp [c, μ, g, field]

end KernelFlip

end New

end
