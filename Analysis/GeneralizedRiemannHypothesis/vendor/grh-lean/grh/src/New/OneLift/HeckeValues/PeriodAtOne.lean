import New.UpperBound.Kernels.DefiniteKernelSize

/-!
# The period of a determinant theta kernel (used in rank two for the L-value at z = 1)

The period of a theta kernel for the pair `(I_n, I_n)` of standard definite spaces (`New.stdSpace`),
with polynomial `∏ τ, det ^ c τ` and finite datum a character of the determinant modulo `𝔪`.

* `New.Rows.detKernel`, `New.Rows.detPeriod`: the kernel on the finite adelic group and its class
  sum.
* `New.Rows.detPeriod_eq_stdClassSum_sum`: the period is the class sum of the sums, over
  `GL_n(O/𝔪)`, of the kernel values for the indicator of the unit matrix.
* `New.Rows.detPeriod_insert`: if `α` has weight `-c` and tame part `ψ` trivial outside `𝔪`, adding
  a prime `v` to `𝔪` multiplies the period by `∏ l < card n, (1 - q ^ l X)`. Here `q` is the norm of
  `v` and `X` is the inverse of the scalar `α.frobValue n v` (`New.AutChar.frobValue`).

`New.stdClassSum K f` is the sum of `f g / #Aut g` over the classes of level `K`; `New.stdLevel` is
the stabiliser of the standard lattice; `α.HasWeight e ψ` says that `α` has weight `e` and tame part
`ψ`; `𝔪.places` is the set of primes of the modulus `𝔪` and `𝔪.charOfTamePart ψ` the character
modulo `𝔪` made of `ψ`.

Notions from other files:
* `New.Modulus`: a nonzero ideal of O_E prime to its complex conjugate, that is, never divisible by
  both w and w̄.
* `New.WeilData`: the fixed choices on the CM field E that define the Weil representations (a purely
  imaginary element, a self-dual finite idele and a splitting character).
* `α.frobValue n v`: the number χ(ϖ) q ^ (N/2), where N is the cardinality of `n`, χ is the Hecke
  character `α.spaceChar N`, ϖ a uniformiser at `v` and q the norm of `v`.

## Relation to the literature

See `New.Congruences.Selmer.ClassSums`.
-/

namespace New.Rows

open Matrix Finset Fintype RingHom Space SiegelWeil Set

attribute [local instance low] Fintype.ofFinite

variable {E : Type} {n : Type} [Field E] [CMType E] [WeilData E] [Fintype n] [DecidableEq n]
  {α : AutChar E} {c : NumberField.InfinitePlace E → ℕ} {𝔪 𝔪' : Modulus E}
  {ψ : (w : FinPlace E) → MulChar (ResField w) ℂ}

section Definitions

variable (n) (α : AutChar E) (c : NumberField.InfinitePlace E → ℕ) (𝔪 : Modulus E)
  (ψ : (w : FinPlace E) → MulChar (ResField w) ℂ)

/-- The theta kernel (`New.modKernelStdSpace`) of the pair (I_n, I_n) of standard definite spaces,
at the point (1, h) with h finite adelic. Both characters of the pair are α, the datum is the
function Ψ on matrices modulo 𝔪 and the polynomial is the product over τ of the c_τ-th powers of
the determinant of the matrix of variables at τ (`New.Rows.variableMinor τ id id`). The character α
twists the Weil action, so the factor α(det h) is part of the kernel. -/
noncomputable def detKernel (Ψ : Matrix n n 𝔪.ResidueRing → ℂ) : Gf E n → ℂ :=
  fun g ↦
    modKernelStdSpace (stdSpace E n) α α 𝔪 Ψ
      (∏ τ : NumberField.InfinitePlace E, variableMinor τ id id ^ c τ)
      1 g

/-- The period: the class sum, at the level of the standard lattice, of `New.Rows.detKernel` for the
datum `x ↦ χ (det x)`. Here `ψ` is a family of characters `ψ w` of the residue fields and `χ` is the
character modulo `𝔪` with local components `ψ w`. -/
noncomputable def detPeriod : ℂ :=
  stdClassSum (stdLevel E n) (detKernel n α c 𝔪 fun x ↦ 𝔪.charOfTamePart ψ (det x))

end Definitions

section

omit [WeilData E]

/-- For a square matrix `x` over the residue field at `v`, the product of `1 - q ^ l` over
`l < card n - x.rank`, with `q = v.q` the norm of `v`, is the value of the trivial character at
`det x`. So it is `1` if `x` is invertible and `0` otherwise. -/
lemma prod_range_corank_one_sub_q_pow (v : FinPlace E) (x : Matrix n n (ResField v)) :
    ∏ l ∈ .range (card n - x.rank), (1 - v.q ^ l : ℂ) = (1 : MulChar (ResField v) ℂ) x.det := by
  by_cases hx : IsUnit x
  · simp [rank_of_isUnit, hx, MulChar.one_apply ((isUnit_iff_isUnit_det x).1 hx)]
  · have h_corank : 0 < card n - x.rank := by
      simp [card_sub_rank_eq_finrank_ker, zero_lt_iff, coe_mulVecLin, LinearMap.ker_eq_bot, hx,
        mulVec_injective_iff_isUnit]
    rw [MulChar.map_nonunit _ (mt (isUnit_iff_isUnit_det x).2 hx)]
    -- the factor at `l = 0` vanishes
    exact prod_eq_zero (i := 0) (Finset.mem_range.2 h_corank) (by simp)

/-- Let `ψ` be a family of multiplicative characters `ψ w` of the residue fields of `E`, and let `χ`
be the character modulo a modulus `𝔫` with local components `ψ w`. The lift to finite adelic
matrices of `x ↦ χ (det x)` sends a matrix integral at all primes `w` of `𝔫` to the product of the
`ψ w (det (S w))`, with `S w` its reduction at `w`, and every other matrix to `0`. -/
lemma liftFn_charOfTamePart_det_eq_residueDatum {ψ : (w : FinPlace E) → MulChar (ResField w) ℂ}
    (𝔫 : Modulus E) :
    𝔫.liftFn ((fun x : Matrix n n 𝔫.ResidueRing ↦ 𝔫.charOfTamePart ψ x.det) ∘ vecToMatrix) =
      residueDatum Subtype.val fun S : (w : 𝔫.places) → Matrix n n (ResField w.1) ↦
        ∏ᶠ w : 𝔫.places, ψ w (S w).det := by
  simpa [← mapMatrix_apply, ← map_det] using!
    liftFn_eq_residueDatum (𝔪 := 𝔫) Subtype.range_coe.symm
      fun S ↦ ∏ᶠ w, ψ _ (det (n := n) (S w))

/-- Let `ψ` be a family of multiplicative characters `ψ w` of the residue fields of `E`. The residue
datum (`New.residueDatum`) of a function at some places is that function of the reductions of an
adelic matrix integral at these places, and `0` elsewhere. If the primes of `𝔪'` are those of `𝔪`
and one new prime `v`, the datum of `S ↦ ∏ ψ w (det (S w))` over the primes `w` of `𝔪'` is the
product of the datum of `ψ v ∘ det` at `v` and of the same datum over the primes of `𝔪`. -/
lemma residueDatum_singleton_mul {𝔪 𝔪' : Modulus E}
    {ψ : (w : FinPlace E) → MulChar (ResField w) ℂ} {v : FinPlace E} (hv : v ∉ 𝔪.places)
    (h_places : 𝔪'.places = insert v 𝔪.places) :
    (residueDatum (fun _ : Unit ↦ v) (fun S : Unit → Matrix n n (ResField v) ↦ ψ v (S ()).det) *
        residueDatum Subtype.val fun S : (w : 𝔪.places) → Matrix n n (ResField w.1) ↦
          ∏ᶠ w : 𝔪.places, ψ w (S w).det) =
      residueDatum Subtype.val fun S : (w : 𝔪'.places) → Matrix n n (ResField w.1) ↦
        ∏ᶠ w : 𝔪'.places, ψ w (S w).det := by
  classical
  ext x
  -- integral at the places of `𝔪'` means integral at those of `𝔪` and at `v`
  have h_int : (∀ (w : 𝔪'.places) (p : n × n), x p w ∈ LocInt w.1) ↔
      (Unit → ∀ p : n × n, x p v ∈ LocInt v) ∧
        ∀ (w : 𝔪.places) (p : n × n), x p w ∈ LocInt w.1 := by
    simp only [Subtype.forall, h_places, mem_insert_iff, forall_const]
    grind
  let ψDetAt (w : FinPlace E) : ℂ :=
    ψ w ((vecToMatrix x : Matrix n n (𝔸f E)).map (residueOrZero ∘ evalAt w)).det
  have h_prod : ∏ᶠ w : 𝔪'.places, ψDetAt w = ψDetAt v * ∏ᶠ w : 𝔪.places, ψDetAt w := by
    simp only [finprod_set_coe_eq_finprod_mem, h_places, finprod_mem_insert _ hv (Set.toFinite _)]
  simp only [Pi.mul_apply, residueDatum, ite_zero_mul_ite_zero]
  exact if_congr h_int.symm h_prod.symm rfl

end

/-- Let α have weight −c and tame part ψ. Then `detKernel n α c 𝔪 Ψ`, the theta kernel of the pair
(I_n, I_n) with datum Ψ modulo 𝔪 and polynomial ∏_τ det ^ c_τ, is, as a function on the finite
adelic points of U(I_n), invariant under left multiplication by rational points. -/
lemma detKernel_stdEmbFin_mul [hα : α.HasWeight (fun τ : NumberField.InfinitePlace E ↦ -c τ) ψ]
    (Ψ : Matrix n n 𝔪.ResidueRing → ℂ) (γ : U (stdSpace E n).J) (g : Gf E n) :
    detKernel n α c 𝔪 Ψ (stdEmbFin γ * g) = detKernel n α c 𝔪 Ψ g := by
  set Q := ∏ τ : NumberField.InfinitePlace E, variableMinor (n := n) (n' := n) τ id id ^ c τ with hQ
  -- Substituting `γ⁻¹` multiplies `Q = ∏ det ^ c` by `∏ (det γ ^ c)⁻¹`: this is
  -- `twoSidedSubst_stackedDetProd` for determinants without constant rows.
  have h_subst : twoSidedSubst (fun τ ↦ γ⁻¹.1.1.map (Φ τ)) 1 Q =
      (∏ τ, (Φ τ γ.1.1.det ^ c τ)⁻¹) • Q := by
    simpa [hQ, stackedDetProd, stackedDet, ← det_submatrix_equiv_self (.symm (.emptySum _ n)),
      ← map_det, ← mapMatrix_apply] using!
      twoSidedSubst_stackedDetProd (ι := fun τ ↦ Fin (c τ)) (.emptySum Empty n) 0
        (fun τ ↦ γ⁻¹.1.1.map (Φ τ)) 1
  -- Translating the kernel by `γ` gives the factor `∏ det γ ^ c`, which cancels it.
  have h_transl : modKernelStdSpace (stdSpace E n) α α 𝔪 Ψ Q 1 (stdEmbFin γ * g) =
      (∏ τ, Φ τ γ.1.1.det ^ c τ) *
        modKernelStdSpace (stdSpace E n) α α 𝔪 Ψ (twoSidedSubst (fun τ ↦ γ⁻¹.1.1.map (Φ τ)) 1 Q) 1
          g := by
    simpa [Prod.mk_one_one, ← Pi.one_def] using! modKernelStdSpace_embFin_mul hα hα 𝔪 Ψ Q 1 γ 1 g
  simp only [detKernel, ← hQ]
  rw [h_transl, h_subst]
  simp only [modKernelStdSpace, ← modKernelBilin_apply, map_smul, smul_eq_mul, prod_inv_distrib]
  exact mul_inv_cancel_left₀ (by simp [prod_ne_zero_iff, γ.1.det_ne_zero]) _

/-- Let `α` have weight `-c` and tame part `ψ` trivial outside the primes of `𝔪`. Write
`detKernel n α c 𝔪 Ψ` for the theta kernel of the pair `(I_n, I_n)` with characters `α`, datum `Ψ`
modulo `𝔪` and polynomial `∏ τ, det ^ c τ`, a function on the finite adelic points of `U(I_n)`.
The period `detPeriod n α c 𝔪 ψ` is its class sum, at the level of the standard lattice, for the
datum `χ ∘ det`, with `χ` the character modulo `𝔪` made of `ψ`. It equals the class sum of the
function sending `g` to the sum, over `y` in `GL_n(O/𝔪)`, of the values at `g * liftMod y` of the
kernel for the indicator of the unit matrix; `liftMod y` is a lift of `y` to the stabiliser of the
standard lattice. -/
lemma detPeriod_eq_stdClassSum_sum
    [hα : α.HasWeight (fun τ : NumberField.InfinitePlace E ↦ -c τ) ψ]
    (hψ : ∀ w : FinPlace E, w ∉ 𝔪.places → ψ w = 1) :
    detPeriod n α c 𝔪 ψ =
      stdClassSum (stdLevel E n) fun g : Gf E n ↦
        ∑ y : GL n 𝔪.ResidueRing, detKernel n α c 𝔪 (Pi.single 1 1) (g * liftMod y) := by
  -- The character of the determinant is a combination of indicators of invertible matrices.
  have h_expand : (fun x : Matrix n n 𝔪.ResidueRing ↦ 𝔪.charOfTamePart ψ (det x)) =
      ∑ y : GL n 𝔪.ResidueRing, 𝔪.charOfTamePart ψ y.1.det • fun x ↦ if y.1 = x then 1 else 0 := by
    rw [pi_eq_sum_univ fun x : Matrix n n 𝔪.ResidueRing ↦ 𝔪.charOfTamePart ψ (det x),
      ← sum_of_injective _ Units.val_injective _ _ _ (fun _ ↦ rfl)]
    -- outside the image of `GL_n` the determinant is no unit, so the character vanishes there
    simp +contextual [← IsUnit.eq_1, MulChar.map_nonunit, isUnit_iff_isUnit_det]
  -- Translation by `liftMod y` turns the indicator of `1` into that of `y`, times the character.
  have h_move (g : Gf E n) (y : GL n 𝔪.ResidueRing) :
      detKernel n α c 𝔪 (Pi.single 1 1) (g * liftMod y) =
        𝔪.charOfTamePart ψ y.1.det * detKernel n α c 𝔪 (fun x ↦ if y.1 = x then 1 else 0) g := by
    -- `↓`: the translation has to move to the datum before the kernel becomes bilinear in it
    simp +unfoldPartialApp [detKernel, ← modKernelBilin_apply, ↓modKernel_mul_stdLevel_right,
      hα.apply_det_eq_charOfTamePart hψ, -coe_units_inv, Pi.single_apply]
  -- The kernel is linear in the datum.
  simp only [detPeriod, h_expand, h_move]
  simp +unfoldPartialApp [detKernel, ← modKernelBilin_apply]

/-- Let `α` have weight `-c` and tame part `ψ` trivial outside the primes of `𝔪`. Write
`detKernel n α c 𝔪 Ψ` for the theta kernel of the pair `(I_n, I_n)` of standard definite spaces
with characters `α`, datum `Ψ` modulo `𝔪` and polynomial `∏ τ, det ^ c τ`, a function on the finite
adelic points of `U(I_n)`. For the datum `x ↦ χ (det x)`, with `χ` the character modulo `𝔪` made
of `ψ`, it is invariant under right translation by the stabiliser `stdLevel E n` of the standard
lattice. -/
lemma stdLevel_le_rightStabilizer_detKernel
    [hα : α.HasWeight (fun τ : NumberField.InfinitePlace E ↦ -c τ) ψ]
    (hψ : ∀ w : FinPlace E, w ∉ 𝔪.places → ψ w = 1) :
    stdLevel E n ≤ rightStabilizer
      (detKernel n α c 𝔪 fun x : Matrix n n 𝔪.ResidueRing ↦ 𝔪.charOfTamePart ψ x.det) := by
  intro k hk g
  -- Right translation by `k` replaces the datum by `y ↦ α (det k) χ (det (k⁻¹ y))`.
  have h_datum : (α.val (detFin 1 k) : ℂ) • (fun y : Matrix n n 𝔪.ResidueRing ↦
      𝔪.charOfTamePart ψ ((𝔪.reductionGL ⟨k, hk⟩)⁻¹.val * y).det) =
      fun y : Matrix n n 𝔪.ResidueRing ↦ 𝔪.charOfTamePart ψ y.det := by
    ext y
    simp [hα.apply_det_eq_charOfTamePart hψ ⟨k, hk⟩, ← map_mul, ← det_mul]
  simp only [detKernel, modKernelStdSpace]
  rw [modKernel_mul_stdLevel_right (k := ⟨k, hk⟩), h_datum]

/-- Let `α` have weight `-c` and tame part `ψ` trivial outside the primes of `𝔪`, and let the primes
of `𝔪'` be those of `𝔪` and one new split prime `v`. Translate the datum of `χ ∘ det` modulo `𝔪`,
with `χ` the character made of `ψ`, in the Weil representation `pairWeil` by the transposed Hecke
coset representative of a subspace `U` of `(O/v)^n`, placed at `v` in the unitary group by
`ofSplitPlace`. The sum over `U` of these translates, with coefficients
`heckePolyCoeff X U = (-X) ^ i * q ^ (i choose 2)` for `i = dim U`, `q` the norm of `v` and `X` the
inverse of `α.frobValue n v`, is the datum of `χ ∘ det` modulo `𝔪'`. -/
lemma sum_heckePolyCoeff_smul_modDatum_eq_modDatum
    [hα : α.HasWeight (fun τ : NumberField.InfinitePlace E ↦ -c τ) ψ]
    (hψ : ∀ w : FinPlace E, w ∉ 𝔪.places → ψ w = 1) {v : FinPlace E} (hv : v ∉ 𝔪.places)
    (h_places : 𝔪'.places = insert v 𝔪.places) (h_split : v.IsSplit)
    (P : Heisenberg.IsVacuum.Model (Fock.realHeisenberg (realSigns E (homSigns 1 1)))) :
    ∑ U : Submodule (ResField v) (n → ResField v),
        heckePolyCoeff (α.frobValue n v)⁻¹ U • pairWeil (stdSpace E n) (stdSpace E n) α α
          ((1, 1), 1, ofSplitPlace h_split (transposeGL (basicCosetRep U)))
          (modDatum (stdSpace E n) (stdSpace E n) 𝔪 (𝔪.charOfTamePart ψ ·.det) P) =
      modDatum (stdSpace E n) (stdSpace E n) 𝔪' (𝔪'.charOfTamePart ψ ·.det) P := by
  have h_conjDisjoint : (insert v 𝔪.places).IsConjDisjoint := by
    simpa [h_places] using 𝔪'.isConjDisjoint_places
  have h_unr : CharUnramifiedAt α.baseChange.finPart v :=
    hα.charUnramifiedAt (hψ v hv) (by simp_all)
  -- The datum for `𝔪` is the vacuum at `v`, which lies outside `𝔪.places` and its conjugate.
  set f := modDatum (stdSpace E n) (stdSpace E n) 𝔪 (𝔪.charOfTamePart ψ ·.det) P with hf
  have h_vac : ((stdSpace E n).hom (stdSpace E n)).projOn {v} f = f := by
    rw [hf, modDatum, projOn_integrated,
      projOn_schrodingerOp_vacElem _ (show Disjoint 𝔪.places.conjClosure {v} by grind)]
  -- Hence the sum puts in, at `v`, the product of `1 - q ^ l` over `l < corank`. This is the
  -- indicator of the invertible matrices, that is `ψ v ∘ det`, as `ψ v` is trivial.
  rw [(sum_heckePolyCoeff_smul_pairWeil h_unr h_unr h_split h_vac (α.frobValue n v)⁻¹).1]
  have hX : α.frobValue n v ≠ 0 := by simp [AutChar.frobValue, HeckeChar.atUniformizer]
  have h_local (x : Matrix n n (ResField v)) :
      ∏ l ∈ .range (card n - x.rank), (1 - v.q ^ l : ℂ) = ψ v x.det := by
    rw [hψ v hv, prod_range_corank_one_sub_q_pow]
  simp only [hf, modDatum, integrated_schrodingerOp, qPochhammer, inv_mul_cancel₀ hX, mul_one,
    h_local, liftFn_charOfTamePart_det_eq_residueDatum]
  -- The functions put in by `schrodingerOp` at `v` and at `𝔪.places` join to one function at
  -- `𝔪'.places = {v} ∪ 𝔪.places`.
  rw [← residueDatum_singleton_mul hv h_places, h_places, ← Set.singleton_union]
  have : IsSchwartzBruhat {v} (residueDatum (fun _ : Unit ↦ v)
      fun x : Unit → Matrix n n (ResField v) ↦ ψ v (x ()).det) := by
    simpa using isSchwartzBruhat_residueDatum (w := fun _ : Unit ↦ v)
      (fun x : Unit → Matrix n n (ResField v) ↦ ψ v (x ()).det) (by simpa)
  have : IsSchwartzBruhat 𝔪.places (residueDatum (Subtype.val : 𝔪.places → FinPlace E)
      fun S ↦ ∏ᶠ w : 𝔪.places, ψ w (S w : Matrix n n (ResField (w : FinPlace E))).det) :=
    by rw [← liftFn_charOfTamePart_det_eq_residueDatum (n := n) (ψ := ψ) 𝔪]; infer_instance
  exact (schrodingerOp_union (S := {v}) _ h_conjDisjoint (disjoint_singleton_left.2 hv) _).symm

/-- Let `α` have weight `-c` and tame part `ψ` trivial outside the primes of `𝔪`, and let the primes
of `𝔪'` be those of `𝔪` and one new prime `v`, of norm `q`. Let `X` be the inverse of
`α.frobValue n v`, which is the value at a uniformiser at `v` of the Hecke character `α.spaceChar N`
times `q ^ (N/2)`, where `N = card n`. Then the period for `𝔪'` is `∏ l < N, (1 - q ^ l X)`, which
is `qPochhammer q N X`, times the period for `𝔪`.

The factor is the sum, over the subspaces `U` of `(O/v)^n`, of the coefficients
`heckePolyCoeff X U`, evaluated by the q-binomial theorem. -/
lemma detPeriod_insert [h : α.HasWeight (fun τ : NumberField.InfinitePlace E ↦ -c τ) ψ]
    (hψ : ∀ w : FinPlace E, w ∉ 𝔪.places → ψ w = 1) (v : FinPlace E) (hv : v ∉ 𝔪.places)
    (h_places : 𝔪'.places = insert v 𝔪.places) :
    detPeriod n α c 𝔪' ψ =
      qPochhammer v.q (Fintype.card n) (α.frobValue n v)⁻¹ * detPeriod n α c 𝔪 ψ := by
  -- The datum for `𝔪'` is a combination of translates of that for `𝔪`, and a translate has the
  -- same period. The new prime `v` splits, as `𝔪'` is prime to its conjugate.
  have h_split : v.IsSplit := fun h_conj_eq ↦
    𝔪'.isConjDisjoint_places.notMem_of_mem_left (a := v) (by simp [h_places]) (by simp [*])
  -- `γ U` is the transpose of the Hecke coset representative at `v` attached to `U`.
  let γ (U : Submodule (ResField v) (n → ResField v)) : Gf E n :=
    ofSplitPlace h_split (transposeGL (basicCosetRep U))
  let X : ℂ := (α.frobValue n v)⁻¹
  -- Applying the theta functional to the identity of the data gives that of the kernels.
  have h_kernel (g : Gf E n) : detKernel n α c 𝔪' (𝔪'.charOfTamePart ψ ·.det) g =
      ∑ U, heckePolyCoeff X U * detKernel n α c 𝔪 (𝔪.charOfTamePart ψ ·.det) (g * γ U) := by
    simp only [detKernel, modKernelStdSpace, modKernel]
    rw [← sum_heckePolyCoeff_smul_modDatum_eq_modDatum (α := α) (c := c) hψ hv h_places h_split]
    simp [pairTheta, rep_apply_apply, Prod.mk_one_one, X, γ]
  -- The kernels have level `stdLevel`, so the class sums are integrals, which do not see
  -- translations.
  have h_level : stdLevel E n ≤ rightStabilizer (detKernel n α c 𝔪 (𝔪.charOfTamePart ψ ·.det)) :=
    stdLevel_le_rightStabilizer_detKernel hψ
  have h_level' : stdLevel E n ≤ rightStabilizer (detKernel n α c 𝔪' (𝔪'.charOfTamePart ψ ·.det)) :=
    stdLevel_le_rightStabilizer_detKernel fun w hw ↦ hψ w (by simp_all)
  have h_smooth :
      detKernel n α c 𝔪 (𝔪.charOfTamePart ψ ·.det) ∈ smoothInvariants (stdSpace E n).Γf :=
    ⟨forall_mem_range.2 (detKernel_stdEmbFin_mul _), Subgroup.isOpen_mono h_level isOpen_stdLevel⟩
  rw [detPeriod, stdClassSum, ← classIntegral_eq_classSum h_level',
    classIntegral_sum univ (fun U ↦ .mulLeft (heckePolyCoeff X U)) γ (fun _ ↦ h_smooth) h_kernel]
  -- The coefficients add up to the product by the `q`-binomial theorem.
  have h_coeff : ∑ U : Submodule (ResField v) (n → ResField v), heckePolyCoeff X U =
      qPochhammer v.q (card n) X := by
    simpa [← card_ResField] using q_binomial_submodule n (ResField v) ⊤ X
  simp [detPeriod, ← sum_mul, classIntegral_eq_classSum h_level, h_coeff, X]

end New.Rows
