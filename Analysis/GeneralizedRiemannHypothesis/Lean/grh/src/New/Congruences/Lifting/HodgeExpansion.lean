import Lib.General.LinearAlgebra.MatrixNormBounds
import New.Congruences.Lifting.ExponentLattices

/-!
# Exponents of lattice elements in a Hodge basis and the length of one step on a line

Let `L` be a crystalline lattice over a Kummer chart `k` with prime `p` and residue degree
`f = k.f`. A letter is a unit of the field with `p ^ f` elements; it singles out some of the
embeddings of the coefficients into `ℂ_p`, and `i.stepBack a` is the letter `j` with `j^(p^a) = i`.
Take an element `x` of `L.kisinLocAinf` lying in the letter `i`. Then `x ∈ L.withOrders i c` says
the following: for every level `a : ℕ` and every form `μ` of a type `u ∈ L.jumpSet j` at the letter
`j = i.stepBack a`, the value `valueAt a μ x = μ (φ^(-a) x)` lies in `t^(c a u) B_dR⁺`. The file
shows how exponents behave under coordinates and Frobenius. It then shows that among sufficiently
many elements with given exponents some primitive `ℤ_[p]`-combination gains a step: it splits into
parts with raised exponents. The line `u` of a system `c` of exponents is the family `a ↦ c a u`.

## Main definitions and results

* `New.Lift.KummerChart.JumpLattice.mem_withOrders_stdOrders_iff`: the standard exponents
  `New.Lift.KummerChart.stdOrders l` cut out, at the letter, the span
  `New.Lift.KummerChart.JumpLattice.frobKisinAinf l`, the image of `L.kisinAinf` under `φ^l`.
  On the line `u` these exponents are `0` below level `l` and `-u` from level `l` on.
* `New.Lift.KummerChart.JumpLattice.prod_frobEUnit_zpow_smul_mem_kisinLoc_and_withOrders_iff`:
  for a product `F` of integer powers of the `φ^a(E)`, the module `F` times the `S`-span of the
  image under `φ^l` of the Kisin module `L.kisinModule` is cut out in `L.kisinLoc`, at the letter,
  by the standard exponents raised by those of `F`.
* `New.Lift.KummerChart.JumpLattice.wittPairing_mem_withOrders`: exponents add under an
  equivariant bilinear map of lattices.
* `New.Lift.KummerChart.JumpLattice.raiseOrder`, `New.Lift.KummerChart.JumpLattice.raiseOrdersAt`:
  the system of exponents `o` with the single value `o a u`, or all values at the level `a`, raised
  by one.
* `New.Lift.KummerChart.JumpLattice.exists_sum_smul_mem_locKisinPart_sup`: let the chart be
  unramified and the jump `u` of multiplicity at most `n` at the letter `b` steps before `l`. Let
  `o b u < o b v` on the lines `v < u` in `L.jumpSet (l.stepBack b)`. Then any `k.f * n + 1`
  elements of `L.kisinLoc` with exponents `o` at the letter `l` have a `ℤ_[p]`-combination with one
  coefficient `1` that is the sum of two elements of `L.kisinLoc`: one with all exponents at level
  `0` raised by one, and one with the exponent at level `b` on the line `u` raised by one.

Notions from other files:
* `JumpLattice O`: a finite free `O`-module `L` with a crystalline action and, for each letter `i`,
  a finite set `L.jumpSet i` that holds its jumps. `L.Ambient` is `W(C^♭) ⊗ L`, and `L.Functional`
  is the type of `A_inf`-linear maps `L.Ambient → B_dR`.
* `L.forms`, `L.formsOfType i u`: the functionals that are `Γ'`-equivariant on `1 ⊗ L`, and those
  among them that send the letter-`i` projection of `1 ⊗ L` into `t^(-u) B_dR⁺`.
* `L.ainfLattice` is the `A_inf`-span of `1 ⊗ L`. `L.kisinAinf` consists of the `x` in
  `A_inf[1/τ] ⊗ L` with `μ (φ^n x) ∈ B_dR⁺` for all forms `μ` and all `n ≥ 1`, and
  `L.kisinLocAinf` is its saturation by the elements `k.frobE a = φ^a(E)`.
* `saturateBy M P`: the elements that some member of the submonoid `M` multiplies into `P`.

## Relation to the literature

See `New.Congruences.Lifting.SafeMoves` and `New.Congruences.Lifting.CupOrthogonalityBounds` for
related work. For sources see `Lib.PadicHodge.Kisin.PeriodMatrixFrame`.
-/

noncomputable section

namespace New.Lift.KummerChart.JumpLattice

/-! ## Standard exponents, Frobenius on exponents, and additivity of exponents -/

section HodgeExpansion

open Period Submodule Set FrobGroup Module Matrix

variable {p : ℕ} [ThePrime p] [Γ : GroupOverGp p] {k : KummerChart Γ} {O : Coeffs}
  {L A C : JumpLattice O}

section StandardExponents

variable {l a : ℕ} {i : k.Letter} {n : ℤ} {μ : L.Functional} {c : ℕ → ℤ → ℤ}
  {x : L.Ambient} {b : A.Carrier →ₗ[O] L.Carrier →ₗ[O] C.Carrier}

variable (b) in
/-- The `W(C^♭)`-bilinear extension `(W(C^♭) ⊗ A) × (W(C^♭) ⊗ L) → W(C^♭) ⊗ C` of an `O`-bilinear
map `b : A × L → C` of lattices. The tensor products are over `ℤ_p`. -/
abbrev wittPairing : A.Ambient →ₗ[WittCFlat] L.Ambient →ₗ[WittCFlat] C.Ambient :=
  DiagTensor.pair (b.restrictScalars₁₂ ℤ_[p] ℤ_[p])

variable (b) in
/-- The `O`-bilinear map `b : A × L → C` of lattices is equivariant: `b (g y, g x) = g b (y, x)` for
all `g` in `Γ`. -/
def IsEquivariantPairing : Prop :=
  ∀ (g : GroupOverGp.G) (y : A.Carrier) (x : L.Carrier), b (A.ρ g y) (L.ρ g x) = C.ρ g (b y x)

/-- The `W(C^♭)`-bilinear extension of an `O`-bilinear map `b` moves the projector `e_i` onto the
letter `i` from the first argument to the value: `b (e_i y, x) = e_i b (y, x)`. -/
lemma wittPairing_letterProj_left (x : L.Ambient) (y : A.Ambient) :
    wittPairing b (A.letterProj i y) x = C.letterProj i (wittPairing b y x) := by
  induction x using DiagTensor.induction with
  | h_add x x' hx hx' => simp [hx, hx']
  | h_mk a t =>
    induction y using DiagTensor.induction with
    | h_mk a' t' => simp [letterProj]
    | h_add y y' hy hy' => simp [hy, hy']

/-- If the pairing `wittPairing b` maps `s × t` into `Q`, it maps the saturations of `s` and `t` by
the submonoid `T` into the saturation of `Q` by `T`. -/
lemma wittPairing_mem_saturateBy {y : A.Ambient} {T : Submonoid Ainf}
    {s : Submodule Ainf A.Ambient} {t : Submodule Ainf L.Ambient} {Q : Submodule Ainf C.Ambient}
    (hy : y ∈ saturateBy T s) (hx : x ∈ saturateBy T t)
    (h_pair : ∀ {y' : A.Ambient} {x' : L.Ambient}, y' ∈ s → x' ∈ t → wittPairing b y' x' ∈ Q) :
    wittPairing b y x ∈ saturateBy T Q := by
  -- if `r • y ∈ s` and `r' • x ∈ t`, then `r * r'` multiplies the pairing into `Q`
  obtain ⟨r, hr, hry⟩ := hy
  obtain ⟨r', hr', hrx⟩ := hx
  exact ⟨r * r', mul_mem hr hr', by simpa [mul_smul] using h_pair hry hrx⟩

/-- The family of exponents `c` shifted by `l` levels: the value at `(a, u)` is `n` for `a < l` and
`c (a - l) u` for `a ≥ l`. -/
@[simp]
abbrev shiftedOrders (l : ℕ) (n : ℤ) (c : ℕ → ℤ → ℤ) (a : ℕ) (u : ℤ) : ℤ :=
  if a < l then n else c (a - l) u

/-- A `B_dR`-linear map `D` from functionals to `B_dR` shifts the Hodge filtration by `κ`:
`D μ ∈ t^(m + κ) B_dR⁺` whenever `μ (1 ⊗ L) ⊆ t^m B_dR⁺`. -/
abbrev ShiftsHodgeFil (D : L.Functional →ₗ[BdR] BdR) (κ : ℤ) : Prop :=
  ∀ (μ : L.Functional) (m : ℤ),
    (∀ t : Rep.of (overZp L.ρ), μ (DiagTensor.mk 1 t) ∈ hodgeFil m) → D μ ∈ hodgeFil (m + κ)

/-- A `B_dR`-linear map `D` from functionals to `B_dR` respects the action of `Γ'`:
`D μ₂ = g • D μ₁` whenever `μ₂ (1 ⊗ g t) = g • μ₁ (1 ⊗ t)` for all `t` in `L`. -/
abbrev RespectsGaloisAction (D : L.Functional →ₗ[BdR] BdR) : Prop :=
  ∀ (μ₁ μ₂ : L.Functional) (g : k.subgroup),
    (∀ t : L.Carrier, μ₂ (DiagTensor.mk 1 (L.ρ g t)) = toGp g • μ₁ (DiagTensor.mk 1 t)) →
      D μ₂ = toGp g • D μ₁

/-- Let `x` lie in `L.fracSpan` and let `μ` be any `A_inf`-linear functional `W(C^♭) ⊗ L → B_dR`. A
form of type `κ` at the letter `i` is a functional that is equivariant for `Γ' = k.subgroup` on
`1 ⊗ L` and sends the projection of `1 ⊗ L` to the letter `i` into `t^(-κ) B_dR⁺`. Then `μ x` lies
in `hodgeFil n = tⁿ B_dR⁺` provided `D μ * ν x` does for every integer `κ`, every form `ν` of type
`κ` at `i`, and every `B_dR`-linear map `D` from functionals to `B_dR` that shifts the Hodge
filtration by `κ` and respects the action of `Γ'`. -/
lemma apply_mem_hodgeFil_of_forall_formsOfType (hx : x ∈ L.fracSpan)
    (h_terms : ∀ κ : ℤ, ∀ ν ∈ L.formsOfType i κ, ∀ D : L.Functional →ₗ[BdR] BdR,
      ShiftsHodgeFil D κ → RespectsGaloisAction D → D μ * ν x ∈ hodgeFil n) :
    μ x ∈ hodgeFil n := by
  -- Take an invariant Hodge basis `hodgeUnit = P * diag (t ^ κ)`, with `P` invertible over
  -- `BdRPlus`, and the forms `ν m` dual to it. Expand `μ x = ∑ m, D m μ * ν m x` and apply the
  -- hypothesis to each term.
  let ι : Type := Fin (finrank ℤ_[p] L.Carrier)
  let e : Basis ι ℤ_[p] L.Carrier := finBasis ℤ_[p] L.Carrier
  obtain ⟨κ, -, -, -, -, P, (h_inv : ∀ g : GroupOverGp.G,
      (repMatrix L.ρ e g).map (algebraMap ℤ_[p] BdR) * toGp g • hodgeMatrix P.val κ =
        hodgeMatrix P.val κ)⟩ := L.inClass.isPotentiallyCrystalline.exists_hodge_basis e
  -- `hodgeUnit` is `hodgeMatrix P κ` as a unit.
  let hodgeUnit : (Matrix ι ι BdR)ˣ := P.map (algebraMap BdRPlus BdR).mapMatrix.toMonoidHom *
    (MulEquiv.piUnits.symm fun m ↦ tUnit ^ κ m).map (diagonalRingHom ι BdR).toMonoidHom
  have h_equivariant (g : GroupOverGp.G) (μ₁ μ₂ : L.Functional) :
      (∀ t : L.Carrier, μ₂ (DiagTensor.mk 1 (L.ρ g t)) = toGp g • μ₁ (DiagTensor.mk 1 t)) ↔
        basisValues μ₂ ᵥ* hodgeUnit.val = toGp g • basisValues μ₁ ᵥ* hodgeUnit.val :=
    equivariant_iff_basisValues hodgeUnit.isUnit (h_inv g)
  have h_extend (m : ι) : ∃ ν : L.Functional, ∀ t, ν (DiagTensor.mk 1 t) =
      (finBasis ℤ_[p] (Rep.of (overZp L.ρ))).constr ℕ (hodgeUnit.inv m) t :=
    L.exists_functional_extend _
  choose ν hν using h_extend
  have h_row (m : ι) : basisValues (ν m) = hodgeUnit.inv m :=
    funext (by simp [basisValues, hν])
  let D (m : ι) : L.Functional →ₗ[BdR] BdR :=
    .proj m ∘ₗ hodgeUnit.val.vecMulLinear ∘ₗ basisValues
  have h_expand : μ x = ∑ m, D m μ * ν m x := by
    simpa [D] using apply_eq_of_mem_fracSpan μ (∑ m, (basisValues μ ᵥ* hodgeUnit) m • ν m)
      (by simp [h_row, ← vecMul_eq_sum]) hx
  -- `ν m` is equivariant, as row `m` of `hodgeUnit⁻¹ * hodgeUnit` is fixed by `g`.
  have hν_inv (m : ι) : ν m ∈ L.forms := by
    refine fun t g ↦ (h_equivariant g (ν m) (ν m)).2 ?_ t
    simp [funext_iff, h_row, ← mul_apply_eq_vecMul, Matrix.one_apply]
  -- On the basis of the lattice the values of `ν m` are the entries of `t ^ (-κ m) P⁻¹`.
  have hν_fil (m : ι) : L.ainfLattice ≤ ((hodgeFil (-κ m)).restrictScalars Ainf).comap (ν m) := by
    simp [ainfLattice_eq_span_basis, span_le, range_subset_iff, hν, hodgeUnit, mem_hodgeFil,
      mul_comm]
  have hν_type (m : ι) : ν m ∈ L.formsOfType i (κ m) :=
    ⟨hν_inv m, fun t ↦ hν_fil m (letterProj_mk_mem_ainfLattice t)⟩
  -- `D m μ'` pairs the values of `μ'` with column `m` of `hodgeUnit`, which `t ^ κ m` divides.
  have hD_fil (m : ι) : ShiftsHodgeFil (D m) (κ m) := by
    intro μ' j hμ'
    have h_column (s : ι) : hodgeUnit.val s m ∈ hodgeFil (κ m) :=
      mem_hodgeFil.2 ⟨P.val s m, by simp [hodgeUnit]⟩
    change ∑ s, basisValues μ' s * hodgeUnit.val s m ∈ hodgeFil (j + κ m)
    exact sum_mem fun s _ ↦ mul_mem_hodgeFil (hμ' _) (h_column s)
  have hD_inv (m : ι) : RespectsGaloisAction (D m) :=
    fun μ₁ μ₂ g hg ↦ congrFun ((h_equivariant g μ₁ μ₂).1 hg) m
  rw [h_expand]
  exact sum_mem fun m _ ↦ h_terms (κ m) (ν m) (hν_type m) (D m) (hD_fil m) (hD_inv m)

/-- Let `μ` be a form, that is, a functional equivariant on `1 ⊗ L` for the subgroup
`Γ' = k.subgroup`. Let `y` lie in `L.kisinLocAinf`: some product of the `φ^j(E)` multiplies it into
`L.kisinAinf`. Let `v` lie in `valueField a`, the subfield of `B_dR` generated over the fixed field
of `Γ'` by the products of constants in `k.bicommutant` and images of `φ^(-a) S`, for `S = k.S`. If
the value `valueAt a μ y = μ (φ^(-a) y)` is congruent to `v` modulo `hodgeFil n = tⁿ B_dR⁺`, then so
is the value at `coordRetract y`. -/
lemma valueAt_coordRetract_sub_mem_hodgeFil (hμ : μ ∈ L.forms) (y : L.kisinLocAinf) {v : BdR}
    (hv : v ∈ valueField a) (hy : valueAt a μ y - v ∈ hodgeFil n) :
    valueAt a μ (coordRetract y) - v ∈ hodgeFil n := by
  -- Write `y = ∑ rᵢ wᵢ` with `wᵢ` in `L.kisinLoc`; then `coordRetract y = ∑ k.coord₀ rᵢ • wᵢ`. Both
  -- differences are sums over `Option` with the values `-v`, `valueAt a μ wᵢ` in `valueField a`:
  -- the first has the coefficients `1`, `rᵢ`, the second their images under `k.coord₀`. So
  -- `sum_phiInvToBdR_map_mul_mem_of_mem_valueField` applies.
  obtain ⟨m, r, w, hw⟩ : ∃ (m : ℕ) (r : Fin m → Ainf) (w : Fin m → L.kisinLoc),
      ∑ s, r s • (w s : L.Ambient) = y := mem_span_set'.1 (span_kisinLoc.ge y.property)
  let coeff : Option (Fin m) → Ainf := fun s ↦ s.elim 1 r
  let value : Option (Fin m) → BdR := fun s ↦ s.elim (-v) fun s ↦ valueAt a μ (w s)
  have h_value : ∀ s, value s ∈ valueField a :=
    Option.forall.2 ⟨neg_mem hv, fun s ↦ valueAt_mem_valueField hμ (w s).property⟩
  have h_sum : ∑ s, phiInvToBdR a (coeff s) * value s ∈ hodgeFil n := by
    simpa [coeff, value, ← hw, sub_eq_neg_add] using hy
  have h_sum_coord : ∑ s, phiInvToBdR a (k.coord₀ (coeff s)) * value s ∈ hodgeFil n :=
    sum_phiInvToBdR_map_mul_mem_of_mem_valueField k.coord₀ value coeff h_value h_sum
  rw [coordRetract_sum (fun s ↦ (w s).property) hw]
  simpa [coeff, value, smul_eq_val_smul, sub_eq_neg_add] using h_sum_coord

/-- If `μ` is a form and the value `valueAt a μ y = μ (φ^(-a) y)` at an element `y` of
`L.kisinLocAinf` lies in `hodgeFil n = tⁿ B_dR⁺`, so does the value at `coordRetract y`. -/
lemma valueAt_coordRetract_mem_hodgeFil (hμ : μ ∈ L.forms) (y : L.kisinLocAinf)
    (hy : valueAt a μ y ∈ hodgeFil n) : valueAt a μ (coordRetract y) ∈ hodgeFil n := by
  simpa using valueAt_coordRetract_sub_mem_hodgeFil (v := 0) hμ y (zero_mem _) (by simpa using hy)

/-- If `y` in `L.kisinLocAinf` has exponents `c` at the letter `i`, so does its image under the
coordinate retraction `coordRetract`, which sends `r • w` to `k.coord₀ r • w` for `r` in `A_inf` and
`w` in `L.kisinLoc`. -/
lemma coordRetract_mem_withOrders (y : L.kisinLocAinf) (hy : y.val ∈ L.withOrders i c) :
    (coordRetract y).val ∈ L.withOrders i c := by
  obtain ⟨⟨-, hy_letter⟩, hy_value⟩ := hy
  refine ⟨⟨(coordRetract y).property.1, mem_letterPart_iff_mulZeta.2 ?_⟩, fun a u hu μ hμ ↦ ?_⟩
  · -- `coordRetract` commutes with ζ, which acts on `y` as the scalar `k.letterTeich i`.
    simpa using mulZeta.wittMap_coordRetract y (k.letterTeich i • y)
      (mem_letterPart_iff_mulZeta.1 hy_letter)
  · exact valueAt_coordRetract_mem_hodgeFil hμ.1 y (hy_value a u hu μ hμ)

/-- Let `μ` be a form. Let `x` lie in `L.kisinLocAinf`, that is, a product of elements `φ^j(E)`
multiplies it into `L.kisinAinf`, the module of the `z` in `A_inf[1/τ] ⊗ L` with `ν (φ^j z) ∈ B_dR⁺`
for all forms `ν` and all `j ≥ 1`. Then `μ (φ ^ (m + 1) • x)` lies in `hodgeFil 0 = B_dR⁺`. -/
lemma apply_phi_pow_succ_smul_mem_hodgeFil_zero (hμ : μ ∈ L.forms) (hx : x ∈ L.kisinLocAinf)
    (m : ℕ) : μ (φ ^ (m + 1) • x) ∈ hodgeFil 0 := by
  -- True on `L.kisinAinf` by definition; it remains to cancel a factor `k.frobE j`.
  refine saturateBy_induction hx (fun y ⟨_, hy_int⟩ ↦ hy_int m μ hμ) fun j y hy ↦ ?_
  -- Frobenius turns the factor into `k.frobE (m + 1 + j)`, which `k.frobE 0` does not divide.
  have h_not_dvd : ¬(k.frobE 0 : Ainf) ∣ k.frobE (m + 1 + j) := not_frobE_dvd_frobE_of_ne (by lia)
  have h_factor : φ ^ (m + 1) • (k.frobE j).val • y =
      (k.frobE (m + 1 + j)).val • φ ^ (m + 1) • y := by
    simp [val_frobE, pow_add, mul_smul, frobGroup_smul_smul]
  have h_mul : phiInvToBdR 0 (k.frobE (m + 1 + j)).val * μ (φ ^ (m + 1) • y) ∈ hodgeFil 0 := by
    rwa [h_factor, ← valueAt_zero, map_smulₛₗ, valueAt_zero] at hy
  exact (mul_mem_hodgeFil_iff_of_not_frobE_dvd h_not_dvd 1).1 (by rwa [zpow_one])

/-- Frobenius shifts exponents. If `x` has exponents `c` at `i.stepBack l`, then `φ ^ l • x` has the
following exponents at `i`: `0` at levels `a < l`, and `c (a - l)` at levels `a ≥ l`. -/
lemma phi_pow_smul_mem_withOrders (hx : x ∈ L.withOrders (i.stepBack l) c) :
    φ ^ l • x ∈ L.withOrders i (shiftedOrders l 0 c) := by
  obtain ⟨⟨hx_loc, hx_letter⟩, hx_value⟩ := hx
  refine ⟨⟨span_kisinLoc.le <| mapsTo_span (f := semilinearAct (φ ^ l))
    (fun _ ↦ phi_pow_smul_mem_kisinLoc) (span_kisinLoc.ge hx_loc),
    phi_pow_smul_mem_letterPart_iff.2 hx_letter⟩, fun a u hu μ hμ ↦ ?_⟩
  -- The value of φ^l x at level a is μ(φ^{l-a} x).
  obtain ⟨m, rfl | rfl⟩ : ∃ m : ℕ, l = a + m + 1 ∨ a = l + m := ⟨max (l - a - 1) (a - l), by lia⟩
  · -- The value is μ(φ^{m+1} x), and the exponent is 0.
    simpa [valueAt, pow_add, mul_smul, Nat.lt_succ_iff] using
      apply_phi_pow_succ_smul_mem_hodgeFil_zero hμ.1 hx_loc m
  · -- The value is that of x at level m.
    rw [show i.stepBack (l + m) = (i.stepBack l).stepBack m by simp [pow_add]] at hu hμ
    simpa [valueAt, pow_add, mul_smul] using hx_value m u hu μ hμ

/-! ### The standard exponents -/

/-- Let `x` have the standard exponents `stdOrders l` at the letter `i`. Let `l ≤ a` and let `r` lie
in `A_inf`. If `r φ^a(E) x` lies in `L.ainfLattice`, the `A_inf`-span of `1 ⊗ L`, so does `r x`.
Here `E = k.E` is the distinguished element of the chart and `k.frobE a = φ^a(E)`. -/
lemma smul_mem_ainfLattice_of_frobE_smul_mem (hx : x ∈ L.withOrders i (stdOrders l))
    (hla : l ≤ a) {r : Ainf} (hr : r • (k.frobE a).val • x ∈ L.ainfLattice) :
    r • x ∈ L.ainfLattice := by
  -- Show that φ^a(E) divides every coordinate `coord s` of r φ^a(E) x in a basis `e` of `L`.
  let e := finBasis ℤ_[p] (Rep.of (overZp L.ρ))
  let ι : Type := Fin (finrank ℤ_[p] (Rep.of (overZp L.ρ)))
  have h_mem {z : L.Ambient} :
      z ∈ L.ainfLattice ↔ ∃ coord : ι → Ainf, ∑ s, coord s • DiagTensor.mk 1 (e s) = z := by
    simp [ainfLattice_eq_span_basis, mem_span_range_iff_exists_fun, e, ι]
  obtain ⟨coord, h_coord⟩ := h_mem.1 (by rwa [smul_comm] at hr)
  -- `μ s` extends the s-th coordinate functional of the basis.
  have h_extend (s : ι) : ∃ μ : L.Functional, ∀ t, μ (DiagTensor.mk 1 t) =
      algebraMap ℤ_[p] BdR (e.coord s t) := L.exists_functional_extend (Algebra.linearMap _ _ ∘ₗ _)
  choose μ hμ using h_extend
  have hx_frac : (φ ^ a)⁻¹ • x ∈ L.fracSpan :=
    smul_mem_fracSpan _ (kisinLocAinf_le_fracSpan (withOrders_le_kisinLocAinf hx))
  -- In a Hodge basis, a term of jump κ is a coefficient of order ≥ κ times a value of order ≥ -κ.
  have h_int (s : ι) : valueAt a (μ s) x ∈ hodgeFil 0 := by
    refine apply_mem_hodgeFil_of_forall_formsOfType (i := i.stepBack a) hx_frac fun κ ν hν D hD _ ↦
      ?_
    have h_coeff : D (μ s) ∈ hodgeFil (0 + κ) :=
      hD (μ s) 0 fun t ↦ by rw [hμ]; exact algebraMap_mem_hodgeFil_zero
    have h_val : ν ((φ ^ a)⁻¹ • x) ∈ hodgeFil (-κ) := valueAt_mem_of_hodgeFil_le _ hx hν
      fun v _ hv ↦ hodgeFil_anti (by simpa [stdOrders, hla.not_gt] using hv)
    simpa using mul_mem_hodgeFil h_coeff h_val
  -- So φ^{-a}(`coord s`) is φ^{-a}(φ^a(E) r) times an integral element; it lies in `hodgeFil 1`,
  -- which means divisibility by φ^a(E).
  have h_dvd (s : ι) : ∃ w : Ainf, coord s = (k.frobE a).val * w := by
    have h_eq : phiInvToBdR a (coord s) = phiInvToBdR a (k.frobE a * r) * valueAt a (μ s) x := by
      simpa [valueAt, hμ, smul_smul, Finsupp.single_apply] using
        congrArg (valueAt a (μ s)) h_coord
    have hE : phiInvToBdR a (k.frobE a * r) ∈ hodgeFil 1 :=
      phiInvToBdR_mem_hodgeFil_one_iff.2 ⟨r, rfl⟩
    exact phiInvToBdR_mem_hodgeFil_one_iff.1 (by simpa [h_eq] using mul_mem_hodgeFil hE (h_int s))
  choose w hw using h_dvd
  -- cancel φ^a(E) in `h_coord`
  exact h_mem.2 ⟨w, by simpa [hw, mul_smul, ← Finset.smul_sum] using h_coord⟩

/-- Let `x` have the standard exponents `stdOrders l` at the letter `i`, a unit of the field with
`p ^ k.f` elements. Then some power of `φ^l(τ)` multiplies `x` into `L.ainfLattice`, the
`A_inf`-span of `1 ⊗ L`. Here `τ = [ε^(1/p)] - 1`. -/
lemma mem_saturateBy_powers_of_mem_withOrders (hx : x ∈ L.withOrders i (stdOrders l)) :
    x ∈ saturateBy (Submonoid.powers (φ ^ l • tau)) L.ainfLattice := by
  -- Induct on the number of factors φ^a(E) that bring x into `L.kisinAinf`.
  have hx_loc : x ∈ L.kisinLocAinf := withOrders_le_kisinLocAinf hx
  revert hx
  refine saturateBy_induction hx_loc ?_ fun a y ih hy ↦ ?_
  · -- No factor: τⁿ x lies in `L.ainfLattice`, and τ divides φ^l(τ).
    rintro x ⟨⟨r, ⟨n, rfl⟩, hn⟩, -⟩ -
    refine mem_saturateBy_of_smul (pow_dvd_pow_of_dvd ?_ n) ⟨n, rfl⟩ (mem_saturateBy_of_mem hn)
    simp [phi_pow_smul, tau, sub_one_dvd_pow_sub_one]
  · -- One more factor: by induction, some power r of φ^l(τ) has r φ^a(E) y in `L.ainfLattice`.
    obtain ⟨r, hr, hry⟩ := ih (smul_mem _ _ hy)
    obtain h_lt | h_ge := lt_or_ge a l
    · -- For a < l, φ^a(E) divides φ^l(τ).
      exact mem_saturateBy_of_smul (frobE_dvd_phi_pow_tau h_lt) (by simp) ⟨r, hr, hry⟩
    · exact ⟨r, hr, smul_mem_ainfLattice_of_frobE_smul_mem hy h_ge hry⟩

/-- An element `x` has the standard exponents `stdOrders l` at the letter `i` if and only if it lies
in `L.letterPart i`, where `ζ` acts by the Teichmüller lift of `i`, and in `L.frobKisinAinf l`, the
image under `φ ^ l` of `L.kisinAinf`. -/
lemma mem_withOrders_stdOrders_iff :
    x ∈ L.withOrders i (stdOrders l) ↔ x ∈ L.frobKisinAinf l ∧ x ∈ L.letterPart i := by
  -- Write the element as φ^l x. The right side then says that x lies in `L.kisinAinf` and in the
  -- letter l steps before i.
  obtain ⟨x, rfl⟩ : ∃ x' : L.Ambient, φ ^ l • x' = x := MulAction.surjective (φ ^ l) x
  suffices φ ^ l • x ∈ L.withOrders i (stdOrders l) ↔
      x ∈ L.kisinAinf ∧ x ∈ L.letterPart (i.stepBack l) by
    simpa [frobKisinAinf, phi_pow_smul_mem_letterPart_iff]
  refine ⟨fun hx ↦ ⟨⟨?_, fun n μ hμ ↦ ?_⟩, ?_⟩, fun ⟨hx_kisin, hx_letter⟩ ↦ ?_⟩
  · -- Forward, the denominator: apply φ^{-l} to φ^l(τ)ⁿ φ^l x ∈ `L.ainfLattice`.
    obtain ⟨_, ⟨n, rfl⟩, hn⟩ := mem_saturateBy_powers_of_mem_withOrders hx
    have h_tau : (tau : Ainf) ^ n • x ∈ L.ainfLattice := by
      simpa [frobGroup_smul_smul] using smul_mem_ainfLattice (φ ^ l)⁻¹ hn
    exact ⟨tau ^ n, ⟨n, rfl⟩, h_tau⟩
  · -- Forward, integrality of the values: φ^{n+1} φ^l x has orders 0 at level l. In a Hodge basis
    -- the coefficients of the invariant form μ are fixed by Γ', hence integral, so μ(φ^{n+1} x) is
    -- integral.
    let i' : k.Letter := (k.letterFrob ^ (n + 1)) i
    let z : L.Ambient := φ ^ (n + 1) • φ ^ l • x
    have h_shift : z ∈ L.withOrders i' (shiftedOrders (n + 1) 0 (stdOrders l)) :=
      phi_pow_smul_mem_withOrders (by simpa [i'] using hx)
    have h_int : valueAt l μ z ∈ hodgeFil 0 := by
      refine apply_mem_hodgeFil_of_forall_formsOfType (i := i'.stepBack l)
        (smul_mem_fracSpan _ (kisinLocAinf_le_fracSpan (withOrders_le_kisinLocAinf h_shift)))
        fun κ ν hν D _ hD ↦ ?_
      have h_coeff : D μ ∈ hodgeFil 0 := (mem_hodgeFil_zero_and_mem_valueField_zero_of_fixed fun g ↦
        hD μ μ g fun t ↦ hμ t g).1
      have h_exp : ∀ v ∈ L.jumpSet (i'.stepBack l), v ≤ κ →
          hodgeFil (shiftedOrders (n + 1) 0 (stdOrders l) l v) ≤ hodgeFil 0 := by
        grind [hodgeFil_anti.imp]
      have h_value : ν ((φ ^ l)⁻¹ • z) ∈ hodgeFil 0 := valueAt_mem_of_hodgeFil_le _ h_shift hν h_exp
      simpa using mul_mem_hodgeFil h_coeff h_value
    simpa [z, valueAt, smul_smul, pow_mul_comm] using h_int
  · -- Forward, the letter.
    exact phi_pow_smul_mem_letterPart_iff.1 (withOrders_le_letterPart hx)
  · -- Conversely, x has exponents -u: τⁿ x lies in `L.ainfLattice`, and τ is prime to every φ^a(E).
    suffices hx : x ∈ L.withOrders (i.stepBack l) fun (_ : ℕ) (u : ℤ) ↦ -u by
      -- the exponents `-u` shifted by `l` levels are `stdOrders l` by definition
      change φ ^ l • x ∈ L.withOrders i (shiftedOrders l 0 fun (_ : ℕ) (u : ℤ) ↦ -u)
      exact phi_pow_smul_mem_withOrders hx
    refine ⟨⟨mem_saturateBy_of_mem hx_kisin, hx_letter⟩, fun a u _ μ hμ ↦ ?_⟩
    obtain ⟨_, ⟨n, rfl⟩, hn⟩ : x ∈ saturateBy (Submonoid.powers tau) L.ainfLattice := hx_kisin.1
    have hτ : ¬(k.frobE a : Ainf) ∣ tau := fun h_dvd ↦ not_frobE_dvd_zTau a (h_dvd.mul_right _)
    refine (mul_mem_hodgeFil_iff_of_not_frobE_dvd hτ n).1 ?_
    simpa using valueAt_mem_hodgeFil_of_mem_ainfLattice hμ hn (smul_mem _ _ hx_letter)

/-- An element `x` lies in `L.stdOrdersPart l i`, that is, in `L.kisinLoc` with the standard
exponents `stdOrders l` at the letter `i`, if and only if it lies in the letter `i` and in
`L.frobKisinAinf l`, the image of `L.kisinAinf` under `φ ^ l`, and all forms take values in the
field `valueField 0` on it. -/
lemma mem_stdOrdersPart_iff :
    x ∈ L.stdOrdersPart l i ↔
      x ∈ L.valueFieldPoints (L.frobKisinAinf l) ∧ x ∈ L.letterPart i := by
  refine ⟨fun ⟨⟨_, h_value⟩, h_std⟩ ↦ ?_, fun ⟨⟨h_frob, h_value⟩, h_letter⟩ ↦ ?_⟩
  · obtain ⟨h_frob, h_letter⟩ := mem_withOrders_stdOrders_iff.1 h_std
    exact ⟨⟨h_frob, h_value⟩, h_letter⟩
  · have h_std := mem_withOrders_stdOrders_iff.2 ⟨h_frob, h_letter⟩
    exact ⟨⟨withOrders_le_kisinLocAinf h_std, h_value⟩, h_std⟩

/-- Multiply `x` by the product of the powers `k.frobEUnit b ^ r b` over `b ∈ s`. The result lies in
`L.withOrders i` with orders `stdOrders l a u`, raised by `r a` at each level `a ∈ s`, if and only
if `x` lies in `L.letterPart i` and in `L.frobKisinAinf l`, the image of `L.kisinAinf` under
`φ ^ l`. -/
lemma prod_frobEUnit_zpow_smul_mem_withOrders_stdOrders_add_iff (s : Finset ℕ) (r : ℕ → ℤ) :
    (∏ b ∈ s, k.frobEUnit b ^ r b) • x ∈
        L.withOrders i (fun (a : ℕ) (u : ℤ) ↦ stdOrders l a u + if a ∈ s then r a else 0) ↔
      x ∈ L.frobKisinAinf l ∧ x ∈ L.letterPart i := by
  rw [prod_frobEUnit_zpow_smul_mem_withOrders_add_iff, mem_withOrders_stdOrders_iff]

/-- Let `F = ∏_{b ∈ s} p_b ^ r b` be a product of integer powers of the units `p_b = φ^b E`
(`k.frobEUnit b`), and put `r a = 0` for `a ∉ s`. Then `F • x` lies in `L.kisinLoc`, the Kisin
module with all `p_a` inverted, and has at the letter `i` the exponents `r a` at the levels `a < l`
and `r a - u` at the levels `a ≥ l`, if and only if `x` lies in `L.letterPart i` (where `ζ` acts by
the Teichmüller lift of `i`) and in the `k.S`-span of the image of the Kisin module `L.kisinModule`
under `φ ^ l`. To have exponents `c` at `i` means to lie in `L.kisinLocAinf` and `L.letterPart i`
and to be sent by `μ ∘ φ^(-a)` into `t^(c a u) B_dR⁺` for every level `a`, every `u` in
`L.jumpSet (i.stepBack a)` and every form `μ` of type `u` at `i.stepBack a`. -/
lemma prod_frobEUnit_zpow_smul_mem_kisinLoc_and_withOrders_iff (s : Finset ℕ) (r : ℕ → ℤ) :
    (∏ b ∈ s, k.frobEUnit b ^ r b) • x ∈ L.kisinLoc ∧
        (∏ b ∈ s, k.frobEUnit b ^ r b) • x ∈ L.withOrders i
          (fun (a : ℕ) (u : ℤ) ↦ stdOrders l a u + if a ∈ s then r a else 0) ↔
      x ∈ span k.S ((fun y : L.Ambient ↦ φ ^ l • y) '' (L.kisinModule : Set L.Ambient)) ∧
        x ∈ L.letterPart i := by
  rw [prod_frobEUnit_zpow_smul_mem_kisinLoc_iff, prod_frobEUnit_zpow_smul_mem_withOrders_add_iff,
    ← valueFieldPoints_frobKisinAinf_eq_span, ← mem_stdOrdersPart_iff, mem_inf,
    restrictScalars_mem]

/-- The projection to the letter `i` of an element of `L.frobKisinAinf l` has the standard
exponents `stdOrders l` at `i`. -/
lemma letterProj_mem_withOrders (hx : x ∈ L.frobKisinAinf l) :
    L.letterProj i x ∈ L.withOrders i (stdOrders l) := by
  -- `letterProj i x` is a multiple of a sum of powers of `letterOp i` applied to `x`, and ζ
  -- preserves `frobKisinAinf l`
  have h_iter (n : ℕ) : L.mulZeta.wittMap^[n] x ∈ L.frobKisinAinf l :=
    MapsTo.iterate (fun _ ↦ mulZeta.wittMap_mem_frobKisinAinf) n hx
  refine mem_withOrders_stdOrders_iff.2 ⟨?_, letterProj_mem_letterPart⟩
  simp [letterProj, letterOp, smul_pow, End.pow_apply, sum_mem, smul_of_tower_mem,
    smul_of_tower_mem _ _ (h_iter _)]

/-- Let `x` lie in `L.frobKisinAinf l`, and let all forms take values in the subfield
`valueField 0` of `B_dR` on `x` (this is membership in `L.valueFieldPoints _`). Then the projection
of `x` to the letter `i` lies in `L.stdOrdersPart l i`: it lies in `L.kisinLoc` and has the
standard exponents `stdOrders l` at `i`. -/
lemma letterProj_mem_stdOrdersPart (hx : x ∈ L.valueFieldPoints (L.frobKisinAinf l)) :
    L.letterProj i x ∈ L.stdOrdersPart l i := by
  obtain ⟨hx_mem, hx_value⟩ := hx
  have h_std : L.letterProj i x ∈ L.withOrders i (stdOrders l) :=
    letterProj_mem_withOrders hx_mem
  exact ⟨⟨withOrders_le_kisinLocAinf h_std,
    fun μ hμ ↦ hx_value _ (comp_letterProj_mem_forms hμ)⟩, h_std⟩

/-- If all members of the finite sets `L.jumpSet i`, which contain the Hodge–Tate jumps of `L` at
the letters `i`, are at most `n`, then `E ^ n` carries `L.kisinAinf` into `L.frobKisinAinf 1`. -/
lemma frobEUnit_pow_smul_mem_frobKisinAinf_one {n : ℕ}
    (h_bound : ∀ (i : Letter) (u : ℤ), u ∈ L.jumpSet i → u ≤ n) (hx : x ∈ L.kisinAinf) :
    k.frobEUnit 0 ^ (n : ℤ) • x ∈ L.frobKisinAinf 1 := by
  -- Split `x` into its letter parts. On each, multiplication by `E ^ n` raises the exponent at
  -- `E = k.frobE 0` on the lines of jump `u` from `-u` to `n - u`, which is at least `0`, the
  -- value of `stdOrders 1` there; at the other `k.frobE a` the exponents stay as they are.
  rw [← L.sum_letterProj x, Finset.smul_sum]
  refine sum_mem fun i _ ↦ ?_
  have h_raised : k.frobEUnit 0 ^ (n : ℤ) • L.letterProj i x ∈ withOrders i (stdOrders 1) := by
    have h_std : L.letterProj i x ∈ withOrders i (stdOrders 0) :=
      letterProj_mem_withOrders (by rwa [frobKisinAinf_zero])
    refine frobEUnit_zpow_smul_mem_withOrders 0 (n : ℤ) h_std fun a u hu ↦ ?_
    rcases a with _ | a
    · simpa [stdOrders] using h_bound _ u hu
    · simp [stdOrders]
  exact (mem_withOrders_stdOrders_iff.1 h_raised).1

end StandardExponents

/-! ### Exponents add -/

/-- Let `b : A × L → C` be an equivariant bilinear map of lattices, `y` any element of `W(C^♭) ⊗ A`,
and `x` an element of `W(C^♭) ⊗ L` that a non-zero element of `A_inf` multiplies into the span of
`1 ⊗ L`. A form is an `A_inf`-linear functional to `B_dR` that is `Γ'`-equivariant on the lattice;
it has type `κ` at the letter `j` if it sends the projection of the lattice to `j` into
`t^(-κ) B_dR⁺`. Let `η` be a form on `C`, `n` an integer and `m` in `FrobGroup Γ = ℤ × Γ`. Then
`η (m • b(y, x))` lies in `hodgeFil n = tⁿ B_dR⁺` if the products `σ (m • y) * ν (m • x)` do, for
every integer `κ`, every form `ν` on `L` of type `κ` at `j`, and every form `σ` on `A` that has type
`u - κ` at `j` in case `η` has type `u` at `j`. -/
lemma apply_smul_wittPairing_mem_hodgeFil {n : ℤ} {x : L.Ambient}
    {b : A.Carrier →ₗ[O] L.Carrier →ₗ[O] C.Carrier} {y : A.Ambient}
    (hb : IsEquivariantPairing b) {η : C.Functional}
    (hη : η ∈ C.forms) (hx : x ∈ L.fracSpan) (m : FrobGroup Γ) (j : k.Letter) (u : ℤ)
    (h_terms : ∀ κ : ℤ, ∀ ν ∈ L.formsOfType j κ, ∀ σ ∈ A.forms,
      (η ∈ C.formsOfType j u → σ ∈ A.formsOfType j (u - κ)) →
      σ (m • y) * ν (m • x) ∈ hodgeFil n) :
    η (m • wittPairing b y x) ∈ hodgeFil n := by
  -- Expand the second variable in a Hodge basis of `L`; a coefficient map `D` of the expansion
  -- gives the form `σ = D ∘ β` on `A`, where `β y x = η (b(y, x))`.
  have h_smul : wittPairing b (m • y) (m • x) = m • wittPairing b y x :=
    baseChangePairing_map _ (hb (FrobGroup.snd m)) y x (smul_mul' m)
  rw [← h_smul]
  let β : A.Ambient →ₗ[Ainf] L.Functional :=
    ((wittPairing b).restrictScalars₁₂ Ainf Ainf).compr₂ η
  refine apply_mem_hodgeFil_of_forall_formsOfType (i := j) (μ := β (m • y)) (smul_mem_fracSpan m hx)
    ?_
  intro κ ν hν D (h_fil : ShiftsHodgeFil D κ) (h_inv : RespectsGaloisAction D)
  let σ : A.Functional := D.restrictScalars Ainf ∘ₗ β
  have hσ : σ ∈ A.forms := by
    intro t g
    -- `b` and `η` are equivariant, so `β (1 ⊗ g t) (1 ⊗ g t') = g • β (1 ⊗ t) (1 ⊗ t')`
    have hβ (t' : L.Carrier) : β (.mk 1 (A.ρ g t)) (.mk 1 (L.ρ g t')) =
        toGp g.val • β (.mk 1 t) (.mk 1 t') := by
      simpa [β, hb g t t'] using hη (b t t') g
    exact h_inv (β (.mk 1 t)) (β (.mk 1 (A.ρ g t))) g hβ
  have hσ_type (hu : η ∈ C.formsOfType j u) : σ ∈ A.formsOfType j (u - κ) := by
    refine ⟨hσ, fun t ↦ ?_⟩
    -- `β (e_j (1 ⊗ t)) (1 ⊗ t') = η (e_j (1 ⊗ b (t, t')))`, and `η` has type `u`
    have hβ (t' : Rep.of (overZp L.ρ)) :
        β (A.letterProj j (.mk 1 t)) (.mk 1 t') ∈ hodgeFil (-u) := by
      simpa [β, wittPairing_letterProj_left] using hu.2 (b t t')
    exact hodgeFil_anti (by omega) (h_fil (β (A.letterProj j (.mk 1 t))) (-u) hβ)
  exact h_terms κ ν hν σ hσ hσ_type

/-- The extension `wittPairing b` of a bilinear map `b` of lattices maps
`A.ainfLattice × L.ainfLattice` into `C.ainfLattice`. -/
lemma wittPairing_mem_ainfLattice {x : L.Ambient}
    {b : A.Carrier →ₗ[O] L.Carrier →ₗ[O] C.Carrier} {y : A.Ambient}
    (hy : y ∈ A.ainfLattice) (hx : x ∈ L.ainfLattice) :
    wittPairing b y x ∈ C.ainfLattice :=
  LinearMap.BilinMap.apply_apply_mem_of_mem_span C.ainfLattice _ _
    ((wittPairing b).restrictScalars₁₂ Ainf Ainf) (by simp [mk_one_mem_ainfLattice]) y x hy hx

/-- The extension of an equivariant bilinear map `b` of lattices maps `A.kisinAinf × L.kisinAinf`
into `C.kisinAinf`. -/
lemma wittPairing_mem_kisinAinf {x : L.Ambient}
    {b : A.Carrier →ₗ[O] L.Carrier →ₗ[O] C.Carrier} {y : A.Ambient}
    (hb : IsEquivariantPairing b) (hy : y ∈ A.kisinAinf) (hx : x ∈ L.kisinAinf) :
    wittPairing b y x ∈ C.kisinAinf := by
  have hx_frac : x ∈ L.fracSpan := kisinAinf_le_fracSpan hx
  obtain ⟨hy_sat, hy_int⟩ := hy
  obtain ⟨hx_sat, hx_int⟩ := hx
  have h_sat : wittPairing b y x ∈ saturateBy (Submonoid.powers tau) C.ainfLattice :=
    wittPairing_mem_saturateBy hy_sat hx_sat wittPairing_mem_ainfLattice
  refine ⟨h_sat, fun n μ hμ ↦ ?_⟩
  show μ (φ ^ (n + 1) • wittPairing b y x) ∈ hodgeFil 0
  -- Products of values of forms are integral; letter and type play no role, any choice will do.
  refine apply_smul_wittPairing_mem_hodgeFil hb hμ hx_frac (φ ^ (n + 1))
    (Classical.arbitrary Letter) 0 fun κ ν hν σ hσ _ ↦ ?_
  simpa using mul_mem_hodgeFil (hy_int n σ hσ) (hx_int n ν hν.1)

/-- Let `b : A × L → C` be an `O`-bilinear equivariant map of crystalline lattices and
`wittPairing b` its `W(C^♭)`-bilinear extension. An element `x` of `L.kisinLocAinf` in the
eigenspace of the letter `i` has exponents `c` if `μ (φ^(-a) x) ∈ t^(c a u) B_dR⁺` for all levels
`a` and all forms `μ` of a type `u ∈ L.jumpSet j` at `j = i.stepBack a`, the letter whose `p^a`-th
power is `i`. If `y`, `x` have exponents `c'`, `c` at `i`, then `wittPairing b y x` has exponents
`c''` at `i`, provided `c'' a v ≤ c a u' + c' a u` for all `a` and all `u ∈ A.jumpSet j`,
`u' ∈ L.jumpSet j`, `v ∈ C.jumpSet j` with `u + u' ≤ v`. -/
lemma wittPairing_mem_withOrders {i : k.Letter} {c : ℕ → ℤ → ℤ} {x : L.Ambient}
    {b : A.Carrier →ₗ[O] L.Carrier →ₗ[O] C.Carrier} {y : A.Ambient} (hb : IsEquivariantPairing b)
    {c' c'' : ℕ → ℤ → ℤ} (hy : y ∈ A.withOrders i c') (hx : x ∈ L.withOrders i c)
    (h_exps : ∀ a : ℕ, ∀ u ∈ A.jumpSet (i.stepBack a), ∀ u' ∈ L.jumpSet (i.stepBack a),
      ∀ v ∈ C.jumpSet (i.stepBack a), u + u' ≤ v → c'' a v ≤ c a u' + c' a u) :
    wittPairing b y x ∈ C.withOrders i c'' := by
  have h_loc : wittPairing b y x ∈ C.kisinLocAinf :=
    wittPairing_mem_saturateBy (withOrders_le_kisinLocAinf hy) (withOrders_le_kisinLocAinf hx)
      (wittPairing_mem_kisinAinf hb)
  have h_letter : wittPairing b y x ∈ C.letterPart i := by
    rw [mem_letterPart_iff_letterProj, ← wittPairing_letterProj_left,
      mem_letterPart_iff_letterProj.1 (withOrders_le_letterPart hy)]
  refine ⟨⟨h_loc, h_letter⟩, fun a u hu μ hμ ↦ ?_⟩
  -- It suffices to bound products of values of forms whose types add up to `u`.
  refine apply_smul_wittPairing_mem_hodgeFil hb hμ.1
    (kisinLocAinf_le_fracSpan (withOrders_le_kisinLocAinf hx)) (φ ^ a)⁻¹
    (i.stepBack a) u fun κ ν (hν : ν ∈ L.formsOfType (i.stepBack a) κ) σ _ hσ_of ↦ ?_
  have hσ : σ ∈ A.formsOfType (i.stepBack a) (u - κ) := hσ_of hμ
  change valueAt a σ y * valueAt a ν x ∈ hodgeFil (c'' a u)
  -- `valueAt_mem_of_hodgeFil_le` replaces the first factor by any `z` of order `c' a w` with
  -- `w ≤ u - κ`, then the second by any `z'` of order `c a v` with `v ≤ κ`.
  have h_right (w : ℤ) (hw : w ∈ A.jumpSet (i.stepBack a)) (hw_le : w ≤ u - κ) (z : BdR)
      (hz : z ∈ hodgeFil (c' a w)) : z * valueAt a ν x ∈ hodgeFil (c'' a u) := by
    refine valueAt_mem_of_hodgeFil_le ((hodgeFil (c'' a u)).comap (.mulLeft BdRPlus z)) hx hν
      fun v hv hv_le z' hz' ↦ ?_
    have h_exp : c'' a u ≤ c a v + c' a w := h_exps a w hw v hv u hu (by omega)
    exact hodgeFil_anti (by omega) (mul_mem_hodgeFil hz hz')
  exact valueAt_mem_of_hodgeFil_le
    ((hodgeFil (c'' a u)).comap (.mulRight BdRPlus (valueAt a ν x))) hy hσ h_right

end HodgeExpansion

/-!
## The length of one step on one line of exponents

`New.Lift.KummerChart.JumpLattice.withOrders l o` is the module of elements at the letter `l`
with exponent at least `o a v` at every level `a` on every line `v`.
-/

section OneStepGain

open Period Submodule FrobGroup Module Finset IsDiscreteValuationRing Algebra

variable {p : ℕ} [ThePrime p] [Γ : GroupOverGp p]
  {k : KummerChart Γ} {O : Coeffs} {L : JumpLattice O}

/-- The system of exponents obtained from `o` by raising the single value `o a u` by 1. -/
@[grind]
def raiseOrder (o : ℕ → ℤ → ℤ) (a : ℕ) (u : ℤ) (b : ℕ) (v : ℤ) : ℤ :=
  o b v + if b = a ∧ v = u then 1 else 0

/-- The system of exponents obtained from `o` by raising all values `o a v` at level `a` by 1. -/
@[grind]
def raiseOrdersAt (o : ℕ → ℤ → ℤ) (a : ℕ) (b : ℕ) (v : ℤ) : ℤ :=
  o b v + if b = a then 1 else 0

omit [GroupOverGp p] in
/-- Let `t` be an `N × r` matrix over `B_dR⁺`. There are `d ≤ r` rows `s i` such that, modulo the
kernel of `θ : B_dR⁺ → ℂ_p`, every row of `t` is an `A_inf`-combination of the rows `s i`. -/
lemma exists_thetaBdR_sub_sum_smul_eq_zero {N r : ℕ} (t : Fin N → Fin r → BdRPlus) :
    ∃ d ≤ r, ∃ (s : Fin d → Fin N) (A : Fin N → Fin d → Ainf),
      ∀ (j : Fin N) (m : Fin r), thetaBdR (t j m - ∑ i : Fin d, A j i • t (s i) m) = 0 := by
  -- Auerbach's lemma for the column space `U` of the matrix `θ(t)`: a basis `z` with integral
  -- entries, whose coordinates are the entries at the rows `s i`
  let U : Submodule ℂ_[p] (Fin N → ℂ_[p]) := (Matrix.of fun j m ↦ thetaBdR (t j m)).toLin'.range
  let d : ℕ := finrank ℂ_[p] U
  let entry (j : Fin N) : Dual ℂ_[p] U := .proj j ∘ₗ U.subtype
  obtain ⟨s, z, h_coord, h_int⟩ : ∃ (s : Fin d → Fin N) (z : Basis (Fin d) ℂ_[p] U),
      (∀ i, z.coord i = entry (s i)) ∧ ∀ (j : Fin N) (i : Fin d), ‖(z i).val j‖ ≤ 1 :=
    exists_auerbach (finBasis ℂ_[p] U) entry (fun _ hv ↦ Subtype.ext (funext hv)) (RingHom.id ℂ_[p])
      fun _ ↦ continuous_of_discreteTopology
  have h_lift (j : Fin N) (i : Fin d) : ∃ a : Ainf, (theta a : ℂ_[p]) = (z i).val j :=
    (theta_surjective ⟨(z i).val j, by simpa using h_int j i⟩).imp fun a ha ↦ by rw [ha]
  choose A hA using h_lift
  have h_rank : finrank ℂ_[p] U ≤ r := by grw [LinearMap.finrank_range_le, finrank_fin_fun]
  refine ⟨d, h_rank, s, A, fun j m ↦ ?_⟩
  -- expand column `m` in the basis `z` and read the entry in row `j`
  let col : U := ⟨fun i ↦ thetaBdR (t i m), Pi.single m 1, by ext; simp⟩
  have h_expand : col.val j = (∑ i, z.repr col i • z i : U).val j := by rw [z.sum_repr]
  simpa [smul_def', ← z.coord_apply, mul_comm, h_coord, entry, hA, sub_eq_zero, col] using h_expand

/-- Let `o` be a system of exponents. Let `i = l.stepBack b` and assume `o b u < o b v` for all
`v < u` in `L.jumpSet i`. Among points `x j` with exponents `o` at `l` there are `d` points
`x (s m)`, with `d` at most the multiplicity `L.jumpMultiplicity i u` of the jump `u` at `i`. Every
`x j` is an `A_inf`-combination of them modulo an element with exponents `raiseOrder o b u`. -/
lemma exists_sub_sum_smul_mem_withOrders_raiseOrder (o : ℕ → ℤ → ℤ) {u : ℤ} {b N : ℕ} {l : k.Letter}
    (h_lt_lower : ∀ v ∈ L.jumpSet (l.stepBack b), v < u → o b u < o b v) (x : Fin N → L.Ambient)
    (hx : ∀ j : Fin N, x j ∈ L.withOrders l o) :
    ∃ d ≤ L.jumpMultiplicity (l.stepBack b) u, ∃ (s : Fin d → Fin N) (A : Fin N → Fin d → Ainf),
      ∀ j : Fin N, x j - ∑ m : Fin d, A j m • x (s m) ∈
        L.withOrders l (raiseOrder o b u) := by
  -- Modulo type `u - 1` the forms of type `u` are spanned by forms `ν m`. The leading terms of
  -- their values at all `x j` are integral combinations of those at a few points `x (s m)`.
  obtain ⟨r, hr, ν, h_red⟩ := exists_span_formsOfType_mod_pred (L := L) (l.stepBack b) u
  have h_jump_le : ∀ v ∈ L.jumpSet (l.stepBack b), v ≤ u → hodgeFil (o b v) ≤ hodgeFil (o b u) := by
    grind [hodgeFil_anti.imp]
  have h_lead (j : Fin N) (m : Fin r) :
      ∃ t : BdRPlus, algebraMap BdRPlus BdR t * (tUnit ^ o b u).val = valueAt b (ν m).val (x j) :=
    mem_hodgeFil.1 (valueAt_mem_of_hodgeFil_le _ (hx j) (ν m).property h_jump_le)
  choose t ht using h_lead
  obtain ⟨d, hd, s, A, (h_theta : ∀ j m, thetaBdR (t j m - ∑ i, A j i • t (s i) m) = 0)⟩ :=
    exists_thetaBdR_sub_sum_smul_eq_zero t
  refine ⟨d, hd.trans hr, s, fun j m ↦ φ ^ b • A j m, fun j ↦ ?_⟩
  let x' : L.Ambient := x j - ∑ m : Fin d, (φ ^ b • A j m) • x (s m)
  have hx' : x' ∈ L.withOrders l o := sub_mem (hx j) (sum_smul_mem _ _ fun m _ ↦ hx (s m))
  refine mem_withOrders_of_mem_hodgeFil hx' fun a v _ h_lt μ hμ ↦ ?_
  obtain ⟨rfl, rfl⟩ : b = a ∧ u = v := by simpa [raiseOrder, eq_comm] using h_lt.ne
  rw [show raiseOrder o b u b u = 1 + o b u by simp [raiseOrder, add_comm]]
  -- the leading terms of the `ν m` cancel on `x'`
  have h_coeff (a : Ainf) (y : BdR) : phiInvToBdR b (φ ^ b • a) * y = a • y := by
    simp [phiInvToBdR, Algebra.smul_def]
  have h_gen (m : Fin r) : valueAt b (ν m).val x' ∈ hodgeFil (1 + o b u) := by
    have h_eq : valueAt b (ν m).val x' = algebraMap BdRPlus BdR
        (t j m - ∑ i : Fin d, A j i • t (s i) m) * (tUnit ^ o b u).val := by
      simp [x', ← ht, algebraMap.smul, sub_mul, sum_mul, h_coeff, -Units.val_zpow_eq_zpow_val]
    rw [h_eq]
    exact mul_mem_hodgeFil (algebraMap_mem_hodgeFil_one_iff.2 (h_theta j m)) (subset_span rfl)
  -- forms of type `u - 1` have larger exponents, so the `ν m` suffice
  obtain ⟨κ, hκ⟩ : ∃ κ : Fin r → PadicAlgCl p,
      μ - ∑ m : Fin r, κ m • (ν m).val ∈ L.formsOfType (l.stepBack b) (u - 1) := h_red μ hμ
  have h_lower : ∀ v ∈ L.jumpSet (l.stepBack b), v ≤ u - 1 →
      hodgeFil (o b v) ≤ hodgeFil (1 + o b u) := by
    grind [hodgeFil_anti.imp]
  have h_rest : valueAt b μ x' - ∑ m : Fin r, κ m • valueAt b (ν m).val x' ∈
      hodgeFil (1 + o b u) := by
    simpa [valueAt] using valueAt_mem_of_hodgeFil_le _ hx' hκ h_lower
  have h_sum : ∑ m : Fin r, κ m • valueAt b (ν m).val x' ∈ hodgeFil (1 + o b u) :=
    sum_mem fun m _ ↦ smul_of_tower_mem _ (κ m) (h_gen m)
  exact (sub_mem_iff_left _ h_sum).1 h_rest

/-- Let `WittFq k.f = W(𝔽_q)`, `q = p ^ k.f`, be the ring of constants of the chart `k`; it has rank
`k.f` over `ℤ_p`. For `d ≤ n`, any `k.f * n + 1` vectors in `W(𝔽_q)^d` satisfy a `ℤ_p`-linear
relation in which one coefficient is `1`. -/
lemma exists_eq_one_and_sum_smul_eq_zero {d n : ℕ} (hd : d ≤ n)
    (w : Fin (k.f * n + 1) → Fin d → WittFq k.f) :
    ∃ (c : Fin (k.f * n + 1) → ℤ_[p]) (j₀ : Fin (k.f * n + 1)),
      c j₀ = 1 ∧ ∀ m : Fin d, ∑ j : Fin (k.f * n + 1), c j • w j m = 0 := by
  have h_dep : ¬LinearIndependent ℤ_[p] w := fun h_indep ↦ by
    have h_card : k.f * n + 1 ≤ d * k.f := by
      simpa [finrank_wittFq, finrank_pi_fintype] using h_indep.fintype_card_le_finrank
    nlinarith
  obtain ⟨a, h_rel, j₁, hj₁⟩ := Fintype.not_linearIndependent_iff.1 h_dep
  -- divide the relation by its coefficient `a j₀` of least valuation
  obtain ⟨j₀, h_dvd⟩ : ∃ j₀, ∀ j, ∃ c : ℤ_[p], a j = a j₀ * c := by
    simpa [addVal_le_iff_dvd, dvd_def] using Finite.exists_min (addVal ℤ_[p] ∘ a)
  choose c hc using h_dvd
  have ha₀ : a j₀ ≠ 0 := fun h_zero ↦ hj₁ (by rw [hc j₁, h_zero, zero_mul])
  refine ⟨c, j₀, by simpa [ha₀] using hc j₀, fun m ↦ ?_⟩
  have h_smul : a j₀ • ∑ j, c j • w j m = 0 := by
    simpa [smul_sum, ← mul_smul, ← hc] using congrFun h_rel m
  simpa [ha₀] using h_smul

/-- If the Kummer chart `k` is unramified (`h_unram`), every `r` in `k.S` is congruent modulo `k.E`
to a constant: there are `w` in `WittFq k.f` and `y` in `k.S` with `r - w • 1 = k.E * y`. -/
lemma exists_sub_smul_one_eq_E_mul (h_unram : k.IsUnramified) (r : k.S) :
    ∃ (w : WittFq k.f) (y : k.S), r - w • 1 = k.E * y := by
  obtain ⟨-, h_e, -⟩ := h_unram
  obtain ⟨w, y, hy⟩ : ∃ w : Fin 1 → WittFq k.f, k.frobE 0 ∣ r - ∑ i, w i • k.z ^ i.val :=
    k.exists_dvd_sub_sum_z_pow 0 (by simp [h_e]) r
  exact ⟨w 0, y, by simpa [Chart.frobE] using hy⟩

/-- Let `L` be a lattice over an unramified Kummer chart `k` with constants `W(𝔽_q)`, `q = p ^ k.f`.
Let `i = l.stepBack b` have at most `n` Hodge–Tate jumps equal to `u`, counted with multiplicity,
and let `o b u < o b v` for all `v < u` in `L.jumpSet i`, the finite set that contains the jumps at
`i`. Among `k.f * n + 1` points of `L.kisinLoc` (the Kisin module with all `φ^a E` inverted) with
exponents `o` at `l`, some combination over `ℤ_p` with one coefficient equal to `1` is the sum of
two points of `L.kisinLoc`: one with all exponents `o 0 v` at level `0` raised by one
(`raiseOrdersAt o 0`), and one with `o b u` raised by one (`raiseOrder o b u`). -/
lemma exists_sum_smul_mem_locKisinPart_sup (o : ℕ → ℤ → ℤ) (h_unram : k.IsUnramified) {u : ℤ}
    {n : ℕ} (b : ℕ) (l : k.Letter) (hn : L.jumpMultiplicity (l.stepBack b) u ≤ n)
    (h_lt_lower : ∀ v ∈ L.jumpSet (l.stepBack b), v < u → o b u < o b v)
    (x : Fin (k.f * n + 1) → L.kisinLoc)
    (hx : ∀ j : Fin (k.f * n + 1), (x j : L.Ambient) ∈ L.withOrders l o) :
    ∃ (c : Fin (k.f * n + 1) → ℤ_[p]) (j₀ : Fin (k.f * n + 1)),
      -- (a) the combination is primitive: one coefficient is `1`
      c j₀ = 1 ∧
      -- (b) it gains a step, partly on all lines at level `0`, partly on line `u` at level `b`
      ∑ j : Fin (k.f * n + 1), c j • x j ∈
        locKisinPart (L.withOrders l (raiseOrdersAt o 0)) ⊔
          locKisinPart (L.withOrders l (raiseOrder o b u)) := by
  -- Up to a raised exponent, each `x j` is a combination of `d ≤ n` points `x (s m)`. Modulo `E`
  -- the coefficients lie in `WittFq k.f`, of rank `f` over `ℤ_p`, so the `f n + 1` coefficient
  -- vectors satisfy a relation, which gives `c`.
  obtain ⟨d, hd, s, A, (h_up : ∀ j : Fin (k.f * n + 1),
      (x j : L.Ambient) - ∑ m : Fin d, A j m • (x (s m) : L.Ambient) ∈
        L.withOrders l (raiseOrder o b u))⟩ :=
    exists_sub_sum_smul_mem_withOrders_raiseOrder o h_lt_lower (fun j ↦ x j) hx
  -- division of the coefficients by `E`, with remainders `w j m`
  have h_rem (j : Fin (k.f * n + 1)) (m : Fin d) :
      ∃ (w : WittFq k.f) (y : k.S), k.coord₀ (A j m) - w • 1 = k.E * y :=
    exists_sub_smul_one_eq_E_mul h_unram (k.coord₀ (A j m))
  choose w y hw using h_rem
  obtain ⟨c, j₀, hc_one, (hc_rel : ∀ m : Fin d, ∑ j, c j • w j m = 0)⟩ :=
    exists_eq_one_and_sum_smul_eq_zero (hd.trans hn) w
  refine ⟨c, j₀, hc_one, ?_⟩
  have h_comb (a : Fin d → Ainf) : ∑ m, a m • (x (s m) : L.Ambient) ∈ L.withOrders l o :=
    sum_smul_mem _ a fun m _ ↦ hx (s m)
  let point (j : Fin (k.f * n + 1)) : L.kisinLocAinf :=
    ⟨x j, withOrders_le_kisinLocAinf (hx j)⟩
  let comb (a : Fin d → Ainf) : L.kisinLocAinf :=
    ⟨∑ m, a m • x (s m), withOrders_le_kisinLocAinf (h_comb a)⟩
  have h_point (j : Fin (k.f * n + 1)) : coordRetract (point j) = x j := by
    ext; simp [point, coordRetract_of_mem_kisinLoc]
  have h_ret (a : Fin d → Ainf) : coordRetract (comb a) = ∑ m, k.coord₀ (a m) • x (s m) :=
    Subtype.ext (by simpa using coordRetract_sum (fun m ↦ (x (s m)).property) rfl)
  -- `x j` is `E • ∑ m, y j m • x (s m)`, plus the image under `coordRetract` of the element of
  -- `h_up`, plus `∑ m, w j m • x (s m)`; the last terms cancel in the combination by `hc_rel`
  have h_term (j : Fin (k.f * n + 1)) :
      k.E • ∑ m, y j m • x (s m) + coordRetract (point j - comb (A j)) =
        x j - ∑ m, (w j m • (1 : k.S)) • x (s m) := by
    simp only [map_sub, h_point, h_ret, smul_sum, smul_smul, ← hw, sub_smul, sum_sub_distrib]
    abel
  have h_cancel : ∑ j, c j • ∑ m, (w j m • (1 : k.S)) • x (s m) = 0 := by
    calc
      _ = ∑ m, ((∑ j, c j • w j m) • (1 : k.S)) • x (s m) := by
        simp only [smul_sum, sum_smul, ← smul_assoc]
        exact sum_comm
      _ = 0 := by simp [hc_rel]
  have h_sum : ∑ j, c j • x j =
      ∑ j, c j • (k.E • ∑ m, y j m • x (s m) + coordRetract (point j - comb (A j))) := by
    simp only [h_term, smul_sub, sum_sub_distrib, h_cancel, sub_zero]
  rw [h_sum]
  refine sum_smul_mem _ c fun j _ ↦
    add_mem_sup ?_ (coordRetract_mem_withOrders (point j - comb (A j)) (h_up j))
  -- multiplication by `E` raises all exponents at level `0`
  have h_E : k.frobEUnit 0 ^ (1 : ℤ) • ∑ m, (y j m : Ainf) • (x (s m) : L.Ambient) ∈
      L.withOrders l (raiseOrdersAt o 0) :=
    frobEUnit_zpow_smul_mem_withOrders 0 1 (h_comb _) fun a v _ ↦ by simp [raiseOrdersAt, eq_comm]
  simpa [smul_eq_val_smul, Chart.frobE] using h_E

end OneStepGain

end New.Lift.KummerChart.JumpLattice

end
