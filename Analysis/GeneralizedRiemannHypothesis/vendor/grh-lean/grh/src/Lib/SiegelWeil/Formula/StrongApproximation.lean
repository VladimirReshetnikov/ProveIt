import Lib.SiegelWeil.Formula.LagrangianZeroTerms
import Lib.SiegelWeil.SingularForms.UnimodularCoefficients

/-!
# Strong approximation and constancy of automorphic functions in equal rank

This file proves that an automorphic function on a unitary group with a hyperbolic plane is constant
under level and torus hypotheses. This is the step that makes the period of a theta lift between
spaces of equal rank a constant. Strong approximation gives invariance under two opposite unipotent
radicals, Witt's theorem reaches the rational points of the Levi factor, and weak approximation
with the Iwasawa decomposition gives all points. `New.Exchange.IsAutFunction W D` says that `D` is
continuous on the adelic unitary group of `W` and left invariant under rational points, and
`H : W.Splitting W₀ Unit` splits off a hyperbolic plane.

## Main definitions and results

* `New.Exchange.IsAutFunction.apply_eq_apply_one`: an automorphic function on a unitary group with a
  hyperbolic plane is constant if it is right invariant under `Gf.supportedOn n S` for a nonempty
  set `S` of finite places, has level `stdLevel` away from `S`, and satisfies a hypothesis on the
  torus of the plane.
* `New.Exchange.exists_torus_mul_rational_fixes`: if `D` is left invariant under the radical
  elements of every splitting of a hyperbolic plane off `W` with complement `W₀`, then for each set
  `R` of finite places and each rational point `γ` of `W₀` it is left invariant under the components
  on `R ∪ R̄` (`closurePart R`) of a Levi element with `W₀`-block `γ`.

Notions from other files:
* `New.Space`: a hermitian space with a point, given by a matrix J over E and x in GL_n(𝔸) with xᴴJx
  equal to diag(s) at the infinite places and 1 at the finite places.
* `New.Space.Splitting.levi`: The homomorphism GL_p(𝔸) × G(V₀) → G(V) sending (m, g₀) to the element
  with k ↦ km, ι ↦ ιg₀, l ↦ l m*⁻¹.
* `New.Space.Splitting.radicalElement`: `P.radicalElement 0 b`, written `n(b)`, is the unipotent
  element with k ↦ k and l ↦ l − k(½ȷ⁻¹(b + b*)), where ȷ is the purely imaginary element of
  `WeilData E`.

## Relation to the literature

A weak substitute for strong approximation for special unitary groups. Only the constancy of a
continuous function `D` on the adelic points of the full unitary group is proved, under three
hypotheses. First, `D` is left invariant under the rational points. Second, for a nonempty set `S`
of finite places, `D` is right invariant under the points supported on `S` and the complex
conjugates of its places, and under the integral finite adelic points that are trivial on `S`.
Third, for a splitting of a hyperbolic plane: if `D` is left invariant under the unipotent radical
of the parabolic subgroup fixing the isotropic line, then the values of `D` on the Levi subgroup
`GL₁ × G(W₀)`, with `W₀` the complement of the plane, do not depend on the `GL₁` component.

Source: M. Kneser, Starke Approximation in algebraischen Gruppen I, J. reine angew. Math. 218
(1965); G. Shimura, Arithmetic of unitary groups, Ann. of Math. 79 (1964); survey A. Rapinchuk, MSRI
Publ. 61 (2013).
-/

section EqualRankConstant

open New Matrix WeilData Space Splitting G Gf MulAction Set

variable {E n m : Type} [Field E] [CMType E] [WeilData E] [Fintype n] [DecidableEq n] [Fintype m]
  [DecidableEq m] {s : n → ℤˣ} {s₀ : m → ℤˣ} {W : Space E n s} {W₀ : Space E m s₀}
  (H : W.Splitting W₀ Unit)

/-- Let `D` be left invariant under the radical elements `H'.radicalElement c z` of every splitting
`H'` of a hyperbolic plane off `W` with complement `W₀`, and let `R` be a set of finite places. For
each quasi-reflection `ρ` of `W₀`, given by a vector `v` and a unit `σ` with `σ + σ̄ = ⟨v, v⟩`,
there is a torus element `a` such that `D` is left invariant under the components on `R ∪ R̄`
(`closurePart R`) of the Levi element `H.levi (a, ρ)`. -/
lemma New.Exchange.exists_torus_mul_quasiReflection_fixes {D : G E s → ℂ}
    (h_rad : ∀ (H' : W.Splitting W₀ Unit) (c : Matrix m Unit (𝔸 E)) (z : Matrix Unit Unit (𝔸 E))
      (g : G E s), D (H'.radicalElement c z * g) = D g)
    (R : Set (FinPlace E)) (hJ : IsUnit W₀.J) (v : m → E) (σ : Eˣ)
    (hσ : σ + star (σ : E) = star v ⬝ᵥ W₀.J *ᵥ v) :
    ∃ a : GL Unit (𝔸 E), ∀ g : G E s,
      D (closurePart R (H.levi (a, W₀.ratEmbed (quasiReflection W₀.conjTranspose_J hJ v σ hσ))) * g)
        = D g := by
  -- A product of three radical points has such a Levi component.
  let ρ : U W₀.J := quasiReflection W₀.conjTranspose_J hJ v σ hσ
  let c : Matrix m Unit (𝔸 E) := W₀.x⁻¹.1 * (replicateCol Unit v).map toAdele
  have hc : cᴴ * (stdForm E s₀ * c) = toAdele (σ + star ↑σ : E) • 1 := by
    ext1
    simp [hσ, ← stdForm_vecAtPoint]; rfl
  -- `M x` lies in the opposite radical; `j` is the purely imaginary element of `WeilData E`.
  let M (x : E) : G E s := H.symm.radicalElement (toAdele x • c)
    (toAdele (-j * x * (j * σ + 1)) • 1)
  let u : G E s := M σ⁻¹ * H.radicalElement 0 1 * M j
  -- The product `u` keeps the isotropic line, acting on it by `-j * σ`.
  have h_line : H.ActsOnFrame u (toAdele (-j * σ : E) • 1) := by
    simp [u, M, radicalElement, hc, Matrix.mul_assoc, smul_smul, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_sub, Matrix.sub_mul]
    -- Compare coefficients; each is the image of an identity in `E`. The context is cleared
    -- because the local facts slow the automation down.
    clear * -
    match_scalars
    all_goals
      simp only [← map_mul, ← map_add, ← map_neg, ← map_sub, ← map_one toAdele]
      grind [σ.ne_zero, star_eq_zero]
  -- So it is a point of the radical of `H` times `H.levi (t, x)`, with `x` its `W₀`-block.
  obtain ⟨c', z', t, x, h_eq, -, hx⟩ := H.exists_eq_radicalElement_mul_levi h_line
  have h_reflection : (W₀.ratEmbed ρ).adeleMatrix = 1 - toAdele (σ : E)⁻¹ •
    (c * (cᴴ * stdForm E s₀)) := by
    simp [c, ρ, quasiReflection, Matrix.map_sub, map_smul', vecMulVec_eq Unit, W₀.map_J,
      replicateRow_vecMul, adeleMatrix_ratEmbed, Matrix.mul_assoc, Matrix.mul_sub, Matrix.sub_mul]
  -- That block is the quasi-reflection.
  have h_block : H.iCoord * (u.adeleMatrix * H.iAdelic) = (W₀.ratEmbed ρ).adeleMatrix := by
    simp [h_reflection, u, M, radicalElement, hc, Matrix.mul_assoc, smul_smul, Matrix.mul_add,
      Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul]
    match_scalars <;> grind
  obtain rfl : x = W₀.ratEmbed ρ := ext_adeleMatrix (hx.trans h_block)
  refine ⟨t, fun g ↦ ?_⟩
  -- Cut `h_eq` to `R`: cut points of the radicals are points of the radicals, which fix `D`.
  have h_fix : D (closurePart R u * g) = D g := by
    simp [u, M, closurePart_radicalElement, h_rad, mul_assoc]
  simpa [h_eq, closurePart_radicalElement, h_rad, ρ, mul_assoc] using h_fix

/-- Let `D` be left invariant under the radical elements of every splitting of a hyperbolic plane
off `W` with complement `W₀`. Then for each set `R` of finite places and each rational point `γ` of
`W₀` it is left invariant under the components on `R ∪ R̄` (`closurePart R`) of a Levi element with
`W₀`-block `γ`. -/
lemma New.Exchange.exists_torus_mul_rational_fixes {D : G E s → ℂ}
    (h_rad : ∀ (H' : W.Splitting W₀ Unit) (c : Matrix m Unit (𝔸 E)) (z : Matrix Unit Unit (𝔸 E))
      (g : G E s), D (H'.radicalElement c z * g) = D g)
    (R : Set (FinPlace E)) (γ : U W₀.J) :
    ∃ a : GL Unit (𝔸 E), ∀ g : G E s, D (closurePart R (H.levi (a, W₀.ratEmbed γ)) * g) = D g := by
  -- `Γ` is the group of all rational points of `W₀` with this property: those that lift to an
  -- element of the Levi group whose components on `R ∪ R̄` stabilise `D` under left translation.
  let fixing : Subgroup (GL Unit (𝔸 E) × G E s₀) :=
    ((stabilizer _ᵈᵐᵃ D).unop.comap (closurePart R)).comap H.levi
  let Γ : Subgroup (U W₀.J) := (fixing.map (MonoidHom.snd ..)).comap W₀.ratEmbed
  have mem_Γ (δ : U W₀.J) : δ ∈ Γ ↔ ∃ a : GL Unit (𝔸 E), ∀ g : G E s,
      D (closurePart R (H.levi (a, W₀.ratEmbed δ)) * g) = D g := by
    -- By definition, lying in the stabiliser means fixing `D` as a function.
    constructor
    · rintro ⟨⟨a, x⟩, ha, rfl : x = _⟩
      exact ⟨a, congr_fun ha⟩
    · rintro ⟨a, ha⟩
      exact ⟨(a, _), funext ha, rfl⟩
  -- It contains all quasi-reflections.
  have hΓ (v : m → E) (σ : Eˣ) (hσ : σ + star (σ : E) = star v ⬝ᵥ W₀.J *ᵥ v) :
      quasiReflection W₀.conjTranspose_J (by simp) v σ hσ ∈ Γ :=
    (mem_Γ _).2 (exists_torus_mul_quasiReflection_fixes H h_rad R _ v σ hσ)
  -- Witt's theorem for the frames `1` and `γ` gives `γ' ∈ Γ` with `γ' * 1 = γ`.
  obtain ⟨γ', hγ'Γ, hγ⟩ :=
    witt_of_quasiReflection_mem exists_isUnit_sub_star W₀.conjTranspose_J (by simp)
      (X := (1 : Matrix m m E)) (Y := γ.val.val) ⟨1, one_mul 1⟩ ⟨γ.val.inv, γ.val.inv_val⟩
      (by simp [mem_U.1]) Γ hΓ
  obtain rfl : γ = γ' := Subtype.ext (Units.ext (by simp [← hγ]))
  exact (mem_Γ γ).1 hγ'Γ

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.sum in
/-- Let `H` split a hyperbolic plane off `W` with complement `W₀`, and let `D` be continuous on the
adelic unitary group of `W` and left invariant under rational points (`IsAutFunction`). Let `S` be a
nonempty set of finite places, and let `D` be right invariant (`HasLevel`) under the points
supported on `S ∪ S̄` (`Gf.supportedOn n S`) and under the integral points (`stdLevel E n`) that are
trivial on `S` (`Gf.trivialOn n S`). If invariance under the radical of `H` makes `D` on the Levi
group independent of the torus, then `D` is constant.

A weak substitute for strong approximation for special unitary groups (Kneser, Platonov): only the
constancy of `D` is concluded, for isotropic `W` and under the hypothesis on the torus. The
approximation inputs of the proof are additive strong approximation in unipotent radicals and weak
approximation in unitary groups. -/
lemma New.Exchange.IsAutFunction.apply_eq_apply_one {S : Set (FinPlace E)}
    {D : G E s → ℂ} (hD : IsAutFunction W D) (hS : S.Nonempty)
    (h_on : HasLevel D (Gf.supportedOn n S)) (hK : HasLevel D (stdLevel E n ⊓ Gf.trivialOn n S))
    -- invariance under the radical implies invariance under the torus on the Levi subgroup
    (h_torus : (∀ (c : Matrix m Unit (𝔸 E)) (z : Matrix Unit Unit (𝔸 E)) (g : G E s),
        D (H.radicalElement c z * g) = D g) →
      ∃ F : G E s₀ → ℂ, ∀ (t : GL Unit (𝔸 E)) (g : G E s₀), D (H.levi (t, g)) = F g) :
    ∀ g : G E s, D g = D 1 := by
  -- Strong approximation makes `D` left invariant under both radicals. These generate, with the
  -- torus, the rational points of the Levi factor (Witt), also after cutting to a finite set `R` of
  -- places. Weak approximation and the Iwasawa decomposition reduce to such cut Levi elements.
  -- First, `D` takes the same value at points that agree off `S ∪ S̄`.
  have h_agree (a b : G E s) (hab : a.adeleMatrix =
      idemAdele S.conjClosure • a.adeleMatrix + (1 - idemAdele S.conjClosure) • b.adeleMatrix) :
        D a = D b := by
    rw [show a = b * closurePart S (b⁻¹ * a) from ext_adeleMatrix
      (by simpa [-map_mul, ← mul_assoc, ← adeleMatrix_mul b, Matrix.mul_add])]
    exact h_on _ componentOn_mem_supportedOn b
  -- In the radical of any splitting `H'` the parameters `(W₀.x⁻¹ Y + y, A + a)` are dense, with
  -- `Y`, `A` rational and `y`, `a` supported on `S ∪ S̄`; off `S ∪ S̄` such a point is rational.
  have h_rad (H' : W.Splitting W₀ Unit) (c : Matrix m Unit (𝔸 E)) (z : Matrix Unit Unit (𝔸 E))
      (g : G E s) : D (H'.radicalElement c z * g) = D g := by
    refine ((denseRange_rat_matrix_add (S := S.conjClosure) hS.inl W₀.x).prodMap
        (denseRange_rat_matrix_add (S := S.conjClosure) hS.inl 1)).eq
      (f := fun q ↦ D (H'.radicalElement q.1 q.2 * g)) (fun ⟨⟨Y, y⟩, A, a⟩ ↦ ?_)
      (hD.1.comp (by fun_prop)) continuous_const (c, z)
    refine (h_agree _ _ ?_).trans (hD.2 _ (H'.radicalElement_mem_Gamma Y ⟨A, rfl⟩) g)
    simp [radicalElement, smul_sub, mul_left_comm (idemAdele S.conjClosure), Matrix.mul_add,
      Matrix.add_mul, Matrix.mul_assoc, smul_smul, Matrix.sub_mul]
    module
  obtain ⟨F, hF⟩ := h_torus (h_rad H)
  have h_cut (R : Set (FinPlace E)) (t : GL Unit (𝔸 E)) (x : G E s₀) :
      closurePart R (H.levi (t, x)) =
        H.levi (cutGL (idemAdele_conjClosure_mul_self (S := R)) t, closurePart R x) :=
    ext_adeleMatrix <| by
      simp [Splitting.levi, cutGL, ← H.sum_frame_mul_coord_eq_one, -coe_units_inv, Matrix.mul_assoc,
        Matrix.add_mul, Matrix.mul_add]
      module
  -- Weak approximation in `W₀`: up to points trivial on `R`, the rational points are dense.
  have h_levi (R : Set (FinPlace E)) (hR : R.Finite) (t : GL Unit (𝔸 E)) (x : G E s₀) :
      D (closurePart R (H.levi (t, x))) = D 1 := by
    refine (W₀.weak_approximation hR).induction_on x (isClosed_singleton.preimage (hD.1.comp <| by
      simp [↓continuous_iff, Splitting.levi, Matrix.mul_assoc]; fun_prop))
      fun ⟨⟨_, γ, rfl⟩, k, hk⟩ ↦ ?_
    obtain ⟨a, ha⟩ := exists_torus_mul_rational_fixes H h_rad R γ
    have hk' : componentOn m R k = 1 := eq_of_supportedOn componentOn_mem_supportedOn (one_mem _)
      (by simp +contextual [mem_trivialOn.1 hk])
    -- Both sides of `ha 1` and of the goal are values of `F`, which ignores the torus.
    -- The pre-rule `↓h_cut` applies before `closurePart` is unfolded.
    simpa [hF, ↓h_cut, closurePart, hk', Prod.map] using ha 1
  -- Weak approximation in `W` leaves points `γ * (1, k)`; here `k` is integral on a cofinite `T`.
  refine (W.weak_approximation finite_empty).eq (fun ⟨γ, k, _⟩ ↦ ?_) hD.1
  -- Iwasawa: `(1, k) * κ = H.radicalElement c z * H.levi (t, x)` with `κ` in the maximal compact
  -- group.
  obtain ⟨κ, hκ, t, -, -, c, z, x, h_iw⟩ := H.iwasawa (1, k) (wt := 0)
  obtain ⟨T, hT, hk : ∀ w ∈ T, k.atPlace w ∈ localIntGL ..⟩ :=
    k.eventually_atPlace_mem_localIntGL.exists_mem
  -- This element has the components of `κ` on `Tᶜ.conjClosure` and those of `k⁻¹` elsewhere.
  have h_int : k⁻¹ * componentOn n Tᶜ (k * κ.2) ∈ stdLevel E n := by
    simp +contextual [mem_stdLevel_iff, ite_mem, mem_stdLevel_iff.1 hκ.2, hk]
  -- It is `a * b` with `a` supported on `S ∪ S̄` and `b` integral and trivial on `S`.
  obtain ⟨a, ha, b, hb, hab, h_ab⟩ :=
    exists_supportedOn_mul_trivialOn S (k⁻¹ * componentOn n Tᶜ (k * κ.2))
  calc D (γ.1 * (1, k)) = D (1, k) := hD.2 _ γ.2 _
    _ = D ((1, k) * (1, a) * (1, b)) := by rw [hK b ⟨(h_ab h_int).2, hb⟩, h_on a ha]
    _ = D (closurePart Tᶜ ((1, k) * κ)) := by simp [closurePart, mul_assoc, ← hab, Prod.map]
    _ = D (closurePart Tᶜ (H.levi (t, x))) := by
      rw [h_iw, map_mul, closurePart_radicalElement, h_rad]
    _ = D 1 := h_levi Tᶜ hT t x

end EqualRankConstant
