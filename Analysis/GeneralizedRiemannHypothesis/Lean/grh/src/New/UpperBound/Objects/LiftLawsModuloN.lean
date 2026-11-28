import Lib.ClassField.HeckeCharacter.SplitTameCharacters
import Lib.General.LinearAlgebra.TensorChains

/-!
# Direct and mirror data modulo `N`, and the operator `Up`

Let `P` contain one place of each conjugate pair above the split prime `N` of the CM field `E`. A
marked lattice at `P` is a lattice `L` with a vector `ε` of `L / N L` that is non-zero at every
place. Everything here is written in a basis of `L` whose last vector lifts `ε`, at all places of
`P` at once:
* the stabiliser of `(L, ε)` is `mirabolic`, and `diagNInv` takes `L` to `L⁺ = L + 𝒪 ε / N`;
* the direct datum `1[S L ⊆ L', S ε = ε']` is `directDatum`; in bases of `L⁺` and `L'⁺` it is
  `lastRowDatum`;
* the mirror datum `1[S L ⊆ L'⁺] ψ_N (u' (S ε))`, where `u'` is the linear form on `L'⁺` with kernel
  `L'` and `u' (ε' / N) = 1`, is `mirrorDatum` in bases of `L` and `L'⁺`;
* the operator `Up`, which replaces `L` by `L⁺` and sums against `ψ_N` over the primitive vectors
  with unit last entry, is `upOperator`.

A `LiftLaw` records how a lift depends on its datum. On ramified vectors the following hold. A
mirror lift, moved by `diagNInv`, is `Up` after a direct lift, and `Up` moves through a direct lift
up to the factor `γ` of its law. A glued double lift is the number of primitive vectors times a
mirror lift after a direct lift; hence, moved by `diagNInv`, it is a scalar times two direct lifts
after `Up`. So a chain of glued double lifts is a scalar times a chain of direct lifts after a power
of `Up`.

Notions from other files:
* `FinPlace E` is the set of finite places of `E`, `star w` the conjugate place, `LocField w` the
  completion `E_w` with valuation `v` (integral means `v x ≤ 1`) and `ResField w` its residue field.
* `LocProd P` is the product of the `E_w` over `w ∈ P`, and `O` is its ring of integers.
* `stdLattice.selfDualAddChar E` is the additive character of the finite adeles `𝔸f E` fixed by the
  Weil data.
* `liftIntegralFn r f` is `S ↦ f (r S)` on integral matrices `S` and zero elsewhere.
* `compUpTo f j` is the composite `f (j - 1) ∘ ⋯ ∘ f 0` of a chain of linear maps.
-/

noncomputable section

namespace New

open Matrix Finset Function MulAction GeneralLinearGroup Exchange SemilocalField Valued WithZero

section

variable {E n n' n'' : Type} [Field E] [CMType E]
  {P S : Finset (FinPlace E)} {N : ℕ} [Fact N.Prime] [Fintype n] [DecidableEq n] [Fintype n']
  [DecidableEq n'] [Fintype n'']

/-- `P` consists of one place of each pair `w, w̄` above `N`; these places are unramified of degree
one. -/
class IsSplitLevel (P : Finset (FinPlace E)) (N : outParam ℕ) : Prop where
  /-- The conjugate of a place in `P` is not in `P`; in particular the places in `P` are split. -/
  star_notMem : ∀ w ∈ P, star w ∉ P
  /-- The residue field at each place in `P` has `N` elements. -/
  q_eq : ∀ w ∈ P, w.q = N
  /-- `N` is a uniformiser at each place in `P`. -/
  protected v_natCast : ∀ w ∈ P, v (N : LocField w) = exp (-1)
  /-- The places above `N` are those in `P` and their conjugates. -/
  natCast_mem_iff (w : FinPlace E) : ↑N ∈ w.1 ↔ w ∈ P ∨ star w ∈ P

/-- The finite adele that is `y w / N` at `w ∈ P`, with `y w` read in `[0, N)`, and `0`
elsewhere. -/
def residueOverN {E : Type} [Field E] [NumberField E] {P : Finset (FinPlace E)}
    (y : P → ZMod N) : 𝔸f E := adeleOfLocal P fun w : P ↦ (y w).val / N

open scoped Classical in
omit [Fact N.Prime] in
@[simp] lemma residueOverN_apply (y : P → ZMod N) (w : FinPlace E) :
    residueOverN y w = if h : w ∈ P then ((y ⟨w, h⟩).val / N : LocField w) else 0 := rfl

/-- The adele `residueOverN y` is supported on `P`, so the idempotent `idem P` (which is `1` at the
places of `P` and `0` elsewhere) fixes it. -/
lemma idem_mul_residueOverN (y : P → ZMod N) : idem P * residueOverN y = residueOverN y := by
  refine DFunLike.ext _ _ fun w ↦ ?_
  by_cases hw : w ∈ P <;> simp [hw]

variable [WeilData E]

namespace IsSplitLevel

open scoped Classical in
variable (n S) in
/-- The matrix `diag (1, …, 1, N)` at the places of `P` that lie in `S`, and `1` at the others. -/
def diagN [_Λ : IsSplitLevel P N] : GL (n ⊕ Unit) (LocProd P) :=
  diagGL fun i : n ⊕ Unit ↦ if i.isLeft then 1 else
    MulEquiv.piUnits.symm fun w : P ↦ if ↑w ∈ S then .mk0 N NeZero.out else 1

variable [Λ : IsSplitLevel P N] (π : Rep ℂ (GL (n ⊕ Unit) (LocProd P)))
  (π' : Rep ℂ (GL (n' ⊕ Unit) (LocProd P)))

/-- The residue field at a place of `P` is `ℤ / N`. -/
def residueEquiv (w : P) : ResField w.1 ≃+* ZMod N :=
  letI : Fintype (ResField w.1) := Fintype.ofFinite (ResField w.1)
  (ZMod.ringEquivOfPrime (ResField w.1) Fact.out (by simp [← card_ResField, ← Λ.q_eq w])).symm

/-- Reduction modulo `N` of the integers at `P`. -/
def reduction : O (F := LocProd P) →+* (P → ZMod N) :=
  RingHom.pi fun w : P ↦ (Λ.residueEquiv w).toRingHom.comp (residueAt w)

section

omit [WeilData E]

/-- An integer `x` at `P` reduces to `c` modulo `N` exactly if `(x - c) / N` is integral at each
place `w` of `P`, where `c w` is read in `[0, N)`. -/
lemma reduction_eq_iff {x : O (F := LocProd P)} {c : P → ZMod N} :
    Λ.reduction x = c ↔ ∀ w : P, v (((x : LocProd P) w - (c w).val) / N) ≤ 1 := by
  -- At each place, `x - c` has residue `0` exactly if its valuation is below `1`, that is, at most
  -- the valuation of the uniformiser `N`.
  refine funext_iff.trans (forall_congr' fun w ↦ ?_)
  calc Λ.reduction x w = c w
      ↔ Λ.residueEquiv w (residueAt w (x - (c w).val)) = 0 := by
        simp only [map_sub, map_natCast, ZMod.natCast_zmod_val, sub_eq_zero]
        rfl
    _ ↔ v ((x : LocProd P) w - (c w).val) < 1 :=
        (residueEquiv w).map_eq_zero_iff.trans (residueAt_eq_zero w)
    _ ↔ v (((x : LocProd P) w - (c w).val) / N) ≤ 1 := by
        simp [Λ.v_natCast, div_le_iff₀, ← lt_mul_exp_iff_le, ← exp_add]

instance : IsLocalHom Λ.reduction := ⟨by simp [reduction, Pi.isUnit_iff]⟩

lemma reduction_surjective : Surjective Λ.reduction := by
  intro y
  have h_int : (fun w : P ↦ ((y w).val : LocField w.1)) ∈ O (F := LocProd P) :=
    mem_O_locProd.2 fun w ↦ (v.mem_integer_iff _).1 (natCast_mem v.integer (y w).val)
  exact ⟨⟨_, h_int⟩, by simp [reduction_eq_iff]⟩

/-- The inclusion of the integral invertible matrices into all invertible matrices at `P`. -/
abbrev inclGL {E : Type} [Field E] [NumberField E] {P : Finset (FinPlace E)} :
    GL n (O (F := LocProd P)) →* GL n (LocProd P) := map (O (F := LocProd P)).subtype

/-- Reduction modulo `N` of integral invertible matrices. -/
abbrev reductionGL : GL n (O (F := LocProd P)) →* GL n (P → ZMod N) := map Λ.reduction

/-- A section of `reductionGL`. -/
abbrev liftGL : GL n (P → ZMod N) → GL n (O (F := LocProd P)) :=
  surjInv (GL_map_surjective Λ.reduction reduction_surjective)

lemma reductionGL_liftGL (k : GL n (P → ZMod N)) : reductionGL (Λ.liftGL k) = k := surjInv_eq _ k

end

/-- The matrix `diag (1, …, 1, N⁻¹)` at all places of `P`. -/
abbrev diagNInv : GL (n ⊕ Unit) (LocProd P) := (Λ.diagN n P)⁻¹

/-- The character `ψ_N (y) = ψ (-y / N)` of the residues at `P`, where `ψ` is the additive character
`stdLattice.selfDualAddChar E` of the finite adeles and `y / N` is the adele `residueOverN y`. -/
def psiN (y : P → ZMod N) : ℂ := stdLattice.selfDualAddChar E (-residueOverN y)

/-- The last basis vector modulo `N`. -/
abbrev lastBasisVector : n ⊕ Unit → P → ZMod N := Pi.single (.inr ()) 1

/-- A vector whose last entry is a unit is both the last column and the last row of an invertible
matrix. -/
lemma exists_GL_last_col_and_row {R : Type*} [CommRing R] :
    ∃ k : (n ⊕ Unit → R) → GL (n ⊕ Unit) R, ∀ y : n ⊕ Unit → R, IsUnit (y (.inr ())) →
      (k y).val.col (.inr ()) = y ∧ (k y).val.row (.inr ()) = y := by
  classical
  -- For `y` with unit last entry `u`, multiply the identity with last column `y` by the identity
  -- with last row `u⁻¹ • y`; the determinants are `u` and `1`.
  have det_unit (y : n ⊕ Unit → R) (h : IsUnit (y (.inr ()))) :
      IsUnit (updateCol 1 (Sum.inr ()) y * updateRow 1 (Sum.inr ()) (h.unit⁻¹.val • y)).det := by
    simp [← cramer_apply, ← cramer_transpose_apply, h]
  refine ⟨fun y ↦ if h : IsUnit (y (.inr ())) then mk'' _ (det_unit y h) else 1, fun y h ↦ ?_⟩
  -- The second factor has the last basis vector as its last column, and the last row of the first
  -- factor is `u` times that vector.
  constructor <;> ext a <;> simp [h, mul_apply, ← mul_assoc]

/-- For `y` with unit last entry, an integral invertible matrix whose last column and last row are
both `y` modulo `N`. -/
def lastRowColGL (y : n ⊕ Unit → P → ZMod N) : GL (n ⊕ Unit) (O (F := LocProd P)) :=
  Λ.liftGL (exists_GL_last_col_and_row.choose y)

section

omit [WeilData E]

/-- If the last entry of `y` is a unit, then `y` is both the last column and the last row of
`lastRowColGL y` modulo `N`. -/
lemma lastRowColGL_col_and_row {y : n ⊕ Unit → P → ZMod N} (hy : IsUnit (y (.inr ()))) :
    (reductionGL (Λ.lastRowColGL y)).val.col (.inr ()) = y ∧
      (reductionGL (Λ.lastRowColGL y)).val.row (.inr ()) = y := by
  simpa only [lastRowColGL, reductionGL_liftGL] using exists_GL_last_col_and_row.choose_spec y hy

/-- If the last entry of `y` is a unit, then `lastRowColGL y` takes the last basis vector to `y`
modulo `N`. -/
lemma lastRowColGL_smul_lastBasisVector {y : n ⊕ Unit → P → ZMod N} (hy : IsUnit (y (.inr ()))) :
    reductionGL (Λ.lastRowColGL y) • lastBasisVector = y := by
  simpa [Units.smul_def] using (lastRowColGL_col_and_row hy).left

/-- If the last entry of `y` is a unit, then `lastRowColGL y`, acting on row vectors, takes the last
basis vector to `y` modulo `N`. -/
lemma lastBasisVector_vecMul_lastRowColGL {y : n ⊕ Unit → P → ZMod N} (hy : IsUnit (y (.inr ()))) :
    lastBasisVector ᵥ* (reductionGL (Λ.lastRowColGL y)).val = y := by
  simpa using (lastRowColGL_col_and_row hy).right

open scoped Classical in
/-- The operator `Up = π (D) ∑ y, ψ_N (y_last) π (lastRowColGL y)`, where `D = diagNInv` and `y`
runs over the vectors modulo `N` whose last entry `y_last` is a unit. The matrix `D` replaces the
standard lattice by the lattice enlarged by the last basis vector divided by `N`. -/
def upOperator : Module.End ℂ π :=
  π.ρ diagNInv * ∑ y : n ⊕ Unit → P → ZMod N with IsUnit (y (.inr ())),
    psiN (y (.inr ())) • π.ρ (inclGL (lastRowColGL y))

/-- The integral invertible matrices whose last column is the last basis vector modulo `N`: the
stabiliser of the standard lattice marked with that vector. -/
def mirabolic : Subgroup (GL (n ⊕ Unit) (LocProd P)) :=
  ((stabilizer (GL (n ⊕ Unit) (P → ZMod N)) (lastBasisVector : n ⊕ Unit → P → ZMod N)).comap
    Λ.reductionGL).map inclGL

/-- An integral invertible matrix that fixes the last basis vector modulo `N` lies in `mirabolic`,
and every element of `mirabolic` has this form. -/
lemma mem_mirabolic {g : GL (n ⊕ Unit) (LocProd P)} :
    g ∈ Λ.mirabolic ↔ ∃ k : GL (n ⊕ Unit) (O (F := LocProd P)),
      Λ.reductionGL k • (lastBasisVector : n ⊕ Unit → P → ZMod N) = lastBasisVector ∧
      inclGL k = g :=
  Iff.rfl

/-- A vector is ramified if at each place `w` of `P` it has the form `ψ - x ψ` for an integral unit
scalar `x` that is `1` modulo `N` at the other places. A vector that is fixed by the scalars
congruent to `1` modulo `N` has this form if its mean over the unit scalars at each `w` is zero.
The lift laws use only this form. -/
def ramified : Set π :=
  {φ : π | ∀ w : P, ∃ x : (O (F := LocProd P))ˣ, (∀ w' : P, w' ≠ w → Λ.reduction x w' = 1) ∧
    φ ∈ (1 - π.ρ (inclGL (scalar (n ⊕ Unit) x))).range}

/-- A function of matrices modulo `N`, as a function of integral matrices at `P`, extended by
zero. -/
@[simps! -isSimp] abbrev liftFn :
    (Matrix n' n (P → ZMod N) → ℂ) →ₗ[ℂ] Matrix n' n (LocProd P) → ℂ :=
  liftIntegralFn Λ.reduction

/-- Applying `liftFn` to `T ↦ f (reductionGL b * T * reductionGL a)` gives
`T ↦ liftFn f (inclGL b * T * inclGL a)`, for integral invertible matrices `a`, `b`. -/
lemma liftFn_comp_mul (f : Matrix n' n (P → ZMod N) → ℂ) (a : GL n (O (F := LocProd P)))
    (b : GL n' (O (F := LocProd P))) :
    (Λ.liftFn fun T : Matrix n' n (P → ZMod N) ↦
        f ((reductionGL b).val * T * (reductionGL a).val)) =
      fun T : Matrix n' n (LocProd P) ↦ Λ.liftFn f ((inclGL b).val * T * (inclGL a).val) :=
  funext fun _ ↦ (liftIntegralFn_mul Λ.reduction f a b).symm

/-- At an integral invertible matrix `k`, `liftFn f` (the function `f` of matrices modulo `N`, read
on matrices at `P`) takes the value of `f` at `reductionGL k`, i.e. `k` modulo `N`. -/
lemma liftFn_inclGL (f : Matrix n n (P → ZMod N) → ℂ) (k : GL n (O (F := LocProd P))) :
    Λ.liftFn f (inclGL k).val = f (reductionGL k).val :=
  dite_eq_left fun i j ↦ (k.val i j).property

end

/-- The indicator of the integral matrices whose last row is the last basis vector modulo `N`. -/
def lastRowDatum : Matrix (n' ⊕ Unit) (n ⊕ Unit) (LocProd P) → ℂ :=
  Λ.liftFn fun T : Matrix (n' ⊕ Unit) (n ⊕ Unit) (P → ZMod N) ↦
    if T (.inr ()) = lastBasisVector then 1 else 0

/-- The indicator of the integral matrices whose last column is `y` modulo `N`. -/
def lastColDatum (y : n' → P → ZMod N) : Matrix n' (n ⊕ Unit) (LocProd P) → ℂ :=
  Λ.liftFn fun T : Matrix n' (n ⊕ Unit) (P → ZMod N) ↦ if Tᵀ (.inr ()) = y then 1 else 0

/-- On integral matrices, `ψ_N` of the last row paired with `y`. -/
def charDatum (y : n → P → ZMod N) : Matrix (n' ⊕ Unit) n (LocProd P) → ℂ :=
  Λ.liftFn fun T : Matrix (n' ⊕ Unit) n (P → ZMod N) ↦ psiN (T (.inr ()) ⬝ᵥ y)

/-- The direct datum: the indicator of the integral matrices whose last column is the last basis
vector modulo `N`. For marked lattices `(L, ε)`, `(L', ε')` it is `1[S L ⊆ L', S ε = ε']`. -/
abbrev directDatum : Matrix (n' ⊕ Unit) (n ⊕ Unit) (LocProd P) → ℂ :=
  Λ.lastColDatum lastBasisVector

/-- The mirror datum: `ψ_N` of the corner entry modulo `N` on integral matrices, zero elsewhere. For
marked lattices `(L, ε)`, `(L', ε')` it is `1[S L ⊆ L'⁺] ψ_N (u' (S ε))` in bases of `L` and
`L'⁺ = L' + 𝒪 ε' / N`, where `u'` is the last coordinate on `L'⁺` modulo `N`. -/
abbrev mirrorDatum : Matrix (n' ⊕ Unit) (n ⊕ Unit) (LocProd P) → ℂ :=
  Λ.charDatum lastBasisVector

/-- The glued datum of a double lift: on pairs of integral matrices, `ψ_N` of the corner entry of
the product `R T`. -/
def gluedDatum (T : Matrix n' (n ⊕ Unit) (LocProd P))
    (R : Matrix (n'' ⊕ Unit) n' (LocProd P)) : ℂ :=
  Λ.liftFn (fun T' : Matrix n' (n ⊕ Unit) (P → ZMod N) ↦ Λ.charDatum (T'ᵀ (.inr ())) R) T

open scoped Classical in
omit [DecidableEq n] in
/-- The glued datum, sorted by the last column `y` of the first matrix modulo `N`: it is the sum of
the indicator `lastColDatum y` at `T` times the character `charDatum y` at `R`. -/
lemma gluedDatum_eq_sum (T : Matrix n' (n ⊕ Unit) (LocProd P))
    (R : Matrix (n'' ⊕ Unit) n' (LocProd P)) :
    Λ.gluedDatum T R = ∑ y : n' → P → ZMod N, Λ.lastColDatum y T * Λ.charDatum y R := by
  simp only [gluedDatum, lastColDatum, liftFn_apply]
  split_ifs <;> simp

open scoped Classical in
/-- The vectors modulo `N` that are non-zero at every place of `P`. -/
abbrev primitiveVectors (n : Type) [Fintype n] [DecidableEq n] : Finset (n → P → ZMod N) :=
  {y : n → P → ZMod N | ∀ w : P, ∃ a : n, IsUnit (y a w)}

/-- The rules for a lift `L Ψ` from `π` to `π'` that is linear in its datum `Ψ`, a function on
matrices at `P`; the constant `γ` is the cost of the change of lattices `diagNInv`. -/
structure LiftLaw (L : (Matrix (n' ⊕ Unit) (n ⊕ Unit) (LocProd P) → ℂ) →ₗ[ℂ] π →ₗ[ℂ] π') (γ : ℂ) :
    Prop where
  /-- Integral invertible matrices move between the datum and the two representations with no
  factor. -/
  integral_equivariant (a : GL (n ⊕ Unit) (O (F := LocProd P)))
    (b : GL (n' ⊕ Unit) (O (F := LocProd P)))
    (f : Matrix (n' ⊕ Unit) (n ⊕ Unit) (P → ZMod N) → ℂ) (φ : π) :
    π'.ρ (inclGL b) (L (liftFn fun T : Matrix (n' ⊕ Unit) (n ⊕ Unit) (P → ZMod N) ↦
      f ((reductionGL b).val * T * (reductionGL a).val)) (π.ρ (inclGL a) φ)) = L (liftFn f) φ
  /-- Passing in the direct datum from bases of the enlarged lattices (`lastRowDatum`) to bases of
  the original lattices (`directDatum`) costs the factor `γ`. -/
  diagNInv_lastRowDatum (φ : π) :
    π'.ρ diagNInv (L lastRowDatum φ) = γ • L directDatum (π.ρ diagNInv φ)

variable {π π'} {φ : π}
  {L : (Matrix (n' ⊕ Unit) (n ⊕ Unit) (LocProd P) → ℂ) →ₗ[ℂ] π →ₗ[ℂ] π'} {γ : ℂ}

/-! ## The direct datum in terms of valuations -/

omit [WeilData E] in
/-- An integer at `P` reduces to zero modulo `N` exactly if `N` divides it at every place. -/
lemma reduction_eq_zero_iff {x : O (F := LocProd P)} :
    Λ.reduction x = 0 ↔ ∀ w : P, v ((x : LocProd P) w) ≤ exp (-1) := by
  simp [reduction_eq_iff, Λ.v_natCast, div_le_one₀]

omit [WeilData E] in
/-- An integer `x` at `P` reduces to one modulo `N` exactly if `N` divides `x - 1` at every
place. -/
lemma reduction_eq_one_iff {x : O (F := LocProd P)} :
    Λ.reduction x = 1 ↔ ∀ w : P, v ((x : LocProd P) w - 1) ≤ exp (-1) := by
  simp [reduction_eq_iff, Λ.v_natCast, div_le_one₀, ZMod.val_one]

omit [Fintype n] [WeilData E] in
/-- An integral vector is the last basis vector modulo `N` exactly if, at every place of `P`, `N`
divides its entries other than the last and the last entry minus one. -/
lemma reduction_comp_eq_lastBasisVector_iff {x : n ⊕ Unit → O (F := LocProd P)} :
    (fun j : n ⊕ Unit ↦ Λ.reduction (x j)) = lastBasisVector ↔
      (∀ (j : n) (w : P), v ((x (.inl j) : LocProd P) w) ≤ exp (-1)) ∧
        ∀ w : P, v ((x (.inr ()) : LocProd P) w - 1) ≤ exp (-1) := by
  simp [funext_iff (α := n ⊕ Unit), reduction_eq_zero_iff, reduction_eq_one_iff,
    Unique.forall_iff]

omit [DecidableEq n] [DecidableEq n'] [WeilData E] in
/-- Let `p` be a condition on matrices modulo `N`, and let `Q` be equivalent, when `T` is integral,
to `p` for the reduction of `T`. Then the lift of the indicator of `p` is `1` at `T` if `T` is
integral and `Q` holds, and `0` otherwise. -/
lemma liftFn_indicator_apply {p : Matrix n' n (P → ZMod N) → Prop} [DecidablePred p] {Q : Prop}
    [Decidable Q] (T : Matrix n' n (LocProd P))
    (hQ : ∀ hT : ∀ (i : n') (j : n), T i j ∈ O (F := LocProd P),
      p (of fun (i : n') (j : n) ↦ Λ.reduction ⟨T i j, hT i j⟩) ↔ Q) :
    Λ.liftFn (fun T' : Matrix n' n (P → ZMod N) ↦ if p T' then 1 else 0) T =
      if (∀ (i : n') (j : n) (w : P), v (T i j w) ≤ 1) ∧ Q then 1 else 0 := by
  classical
  simp only [liftFn_apply]
  by_cases h_int : ∀ (i : n') (j : n), T i j ∈ O (F := LocProd P)
  · simp [h_int, hQ h_int, fun i j ↦ mem_O_locProd.1 (h_int i j)]
  · rw [dite_eq_right h_int, ite_eq_right fun h ↦ h_int fun i j ↦ mem_O_locProd.2 (h.1 i j)]

open scoped Classical in
omit [DecidableEq n'] [WeilData E] in
/-- `lastRowDatum` in terms of valuations: it is the indicator of the matrices `T` with integral
entries whose last row is congruent to the last basis vector modulo the uniformiser `N`. -/
lemma lastRowDatum_apply (T : Matrix (n' ⊕ Unit) (n ⊕ Unit) (LocProd P)) :
    Λ.lastRowDatum T =
      if (∀ (i : n' ⊕ Unit) (j : n ⊕ Unit) (w : P), v (T i j w) ≤ 1) ∧
        (∀ (j : n) (w : P), v (T (.inr ()) (.inl j) w) ≤ exp (-1)) ∧
        ∀ w : P, v (T (.inr ()) (.inr ()) w - 1) ≤ exp (-1) then 1 else 0 :=
  liftFn_indicator_apply T fun _ ↦ reduction_comp_eq_lastBasisVector_iff

open scoped Classical in
omit [DecidableEq n] [WeilData E] in
/-- `directDatum` in terms of valuations: it is the indicator of the matrices `T` with integral
entries whose last column is congruent to the last basis vector modulo the uniformiser `N`. -/
lemma directDatum_apply (T : Matrix (n' ⊕ Unit) (n ⊕ Unit) (LocProd P)) :
    Λ.directDatum T =
      if (∀ (i : n' ⊕ Unit) (j : n ⊕ Unit) (w : P), v (T i j w) ≤ 1) ∧
        (∀ (i : n') (w : P), v (T (.inl i) (.inr ()) w) ≤ exp (-1)) ∧
        ∀ w : P, v (T (.inr ()) (.inr ()) w - 1) ≤ exp (-1) then 1 else 0 :=
  liftFn_indicator_apply T fun _ ↦ reduction_comp_eq_lastBasisVector_iff

omit [WeilData E] in
/-- The two descriptions of the direct datum agree. Let `D = diagNInv = diag (1, …, 1, N⁻¹)`. Then
`D⁻¹ T D` is integral with last row the last basis vector modulo `N` (`lastRowDatum`) exactly if
`T` is integral with last column the last basis vector modulo `N` (`directDatum`). -/
lemma lastRowDatum_conj_diagNInv (T : Matrix (n' ⊕ Unit) (n ⊕ Unit) (LocProd P)) :
    lastRowDatum ((Λ.diagNInv (n := n'))⁻¹.val * T * (Λ.diagNInv (n := n)).val) =
      directDatum T := by
  -- Conjugation multiplies the last row of `T` by `N` and the last column by `N⁻¹`, off the corner.
  set C := (Λ.diagNInv (n := n'))⁻¹.val * T * (Λ.diagNInv (n := n)).val with hC
  have h_block (i : n') (j : n) : C (.inl i) (.inl j) = T (.inl i) (.inl j) := by
    simp [hC, diagNInv, diagN, ← map_inv]
  have h_corner : C (.inr ()) (.inr ()) = T (.inr ()) (.inr ()) := by
    ext w : 1
    simp [hC, diagNInv, diagN, ← map_inv, ← div_eq_mul_inv,
      (NeZero.out : (N : LocField w.1) ≠ 0)]
  have h_row (j : n) (w : P) :
      v (C (.inr ()) (.inl j) w) = v (T (.inr ()) (.inl j) w) * exp (-1) := by
    simp [hC, diagNInv, diagN, ← map_inv, Λ.v_natCast, mul_comm]
  have h_col (i : n') (w : P) :
      v (C (.inl i) (.inr ()) w) ≤ 1 ↔ v (T (.inl i) (.inr ()) w) ≤ exp (-1) := by
    simp [hC, diagNInv, diagN, ← map_inv, Λ.v_natCast, ← div_eq_mul_inv, div_le_one₀]
  have hN : exp (-1 : ℤ) ≤ 1 := exp_le_exp.2 (by norm_num)
  simp only [lastRowDatum_apply, directDatum_apply, Sum.forall, Unique.forall_iff,
    PUnit.default_eq_unit, h_block, h_corner, h_row, h_col, exp_pos, mul_le_iff_le_one_left]
  -- Both sides say: `T` is integral, `N` divides its last column off the corner, and the corner is
  -- `1` modulo `N`. The remaining conditions follow from these because `N` is integral.
  grind [mul_le_one']

/-! ## The stabilisers fix the direct and the mirror datum -/

omit [WeilData E] in
/-- Let `liftFn f` be the extension by zero of `f` from integral matrices modulo `N`. If it is
non-zero at `g` and at `g⁻¹`, then `g` comes from an integral invertible matrix `k` (`inclGL k = g`)
and `f` is non-zero at the reduction of `k`. -/
lemma exists_inclGL_eq {f : Matrix n n (P → ZMod N) → ℂ} {g : GL n (LocProd P)}
    (hg : Λ.liftFn f g ≠ 0) (hg_inv : Λ.liftFn f ↑g⁻¹ ≠ 0) :
    ∃ k : GL n (O (F := LocProd P)), f (reductionGL k).val ≠ 0 ∧ inclGL k = g := by
  have h_int {T : Matrix n n (LocProd P)} (hT : Λ.liftFn f T ≠ 0) : ∀ i j : n, T i j ∈ O := by
    by_contra h
    simp [liftFn_apply, h] at hT
  obtain ⟨k, rfl⟩ : g ∈ intGL n O := mem_intGL.2 ⟨h_int hg, h_int hg_inv⟩
  exact ⟨k, by rwa [liftFn_inclGL] at hg, rfl⟩

omit [WeilData E] in
/-- The direct datum does not vanish on `mirabolic`, the integral invertible matrices whose last
column is the last basis vector modulo `N`. -/
lemma directDatum_ne_zero_of_mem_mirabolic {g : GL (n ⊕ Unit) (LocProd P)} (hg : g ∈ Λ.mirabolic) :
    directDatum g.val ≠ 0 := by
  obtain ⟨k, hk, rfl⟩ := mem_mirabolic.1 hg
  have h_col : (reductionGL k).valᵀ (.inr ()) = lastBasisVector := by
    rwa [Units.smul_def, smul_eq_mulVec, mulVec_single_one] at hk
  rw [directDatum, lastColDatum, liftFn_inclGL, ite_eq_left h_col]
  exact one_ne_zero

omit [WeilData E] in
/-- Let `g` lie in `mirabolic`, that is, `g` is integral invertible with last column the last basis
vector modulo `N`. Then its conjugate `D⁻¹ g D` by `D = diagNInv = diag (1, …, 1, N⁻¹)` is an
integral invertible matrix whose last row is the last basis vector modulo `N`. -/
lemma exists_inclGL_eq_conj_diagNInv {g : GL (n ⊕ Unit) (LocProd P)} (hg : g ∈ Λ.mirabolic) :
    ∃ k : GL (n ⊕ Unit) (O (F := LocProd P)),
      (Λ.reductionGL k).val (.inr ()) = lastBasisVector ∧
      inclGL k = Λ.diagNInv⁻¹ * g * Λ.diagNInv := by
  classical
  have h_conj {a : GL (n ⊕ Unit) (LocProd P)} (ha : a ∈ mirabolic) :
      lastRowDatum (Λ.diagNInv⁻¹ * a * Λ.diagNInv).val ≠ 0 := by
    rw [Units.val_mul, Units.val_mul, lastRowDatum_conj_diagNInv]
    exact directDatum_ne_zero_of_mem_mirabolic ha
  have h_conj_inv : lastRowDatum (Λ.diagNInv⁻¹ * g * Λ.diagNInv)⁻¹.val ≠ 0 := by
    simpa [mul_assoc] using h_conj (inv_mem hg)
  obtain ⟨k, hk_row, hk⟩ := exists_inclGL_eq
    (f := fun T ↦ if T (.inr ()) = lastBasisVector then 1 else 0) (h_conj hg) h_conj_inv
  exact ⟨k, by simpa using hk_row, hk⟩

omit [WeilData E] in
/-- Let `g` and `h` lie in `mirabolic`. Then `directDatum`, the indicator of the integral matrices
whose last column is the last basis vector modulo `N`, is invariant under `T ↦ h⁻¹ T g`. -/
lemma directDatum_mul_mul_of_mem_mirabolic {g : GL (n ⊕ Unit) (LocProd P)}
    {h : GL (n' ⊕ Unit) (LocProd P)}
    (hg : g ∈ Λ.mirabolic) (hh : h ∈ Λ.mirabolic)
    (T : Matrix (n' ⊕ Unit) (n ⊕ Unit) (LocProd P)) :
    Λ.directDatum (h⁻¹.val * T * g.val) = Λ.directDatum T := by
  obtain ⟨a, ha_fix, rfl⟩ := mem_mirabolic.1 hg
  obtain ⟨b, hb_fix, hb⟩ := mem_mirabolic.1 (inv_mem hh)
  -- Write `g = a` and `h⁻¹ = b` with integral `a`, `b`. As these fix the last basis vector,
  -- `b T' a` has it as last column exactly if `T'` does.
  have h_col (T' : Matrix (n' ⊕ Unit) (n ⊕ Unit) (P → ZMod N)) :
      ((Λ.reductionGL b).val * T' * (Λ.reductionGL a).val)ᵀ (.inr ()) = lastBasisVector ↔
        T'ᵀ (.inr ()) = lastBasisVector := by
    have h_last : ((Λ.reductionGL b).val * T' * (Λ.reductionGL a).val)ᵀ (.inr ()) =
        Λ.reductionGL b • (T' *ᵥ Λ.reductionGL a • lastBasisVector) := by
      simp only [Units.smul_def, smul_eq_mulVec, mulVec_mulVec, mulVec_single_one]
      rfl
    rw [h_last, ha_fix, mulVec_single_one]
    exact (MulAction.injective (Λ.reductionGL b)).eq_iff' hb_fix
  -- So the datum of `b T' a` modulo `N` is that of `T'`.
  rw [← hb]
  calc Λ.directDatum ((inclGL b).val * T * (inclGL a).val)
      = Λ.liftFn (fun T' : Matrix (n' ⊕ Unit) (n ⊕ Unit) (P → ZMod N) ↦
          if ((reductionGL b).val * T' * (reductionGL a).val)ᵀ (.inr ()) = lastBasisVector
          then 1 else 0) T := (congrFun (liftFn_comp_mul _ a b) T).symm
    _ = Λ.directDatum T := by simp only [h_col, directDatum, lastColDatum]

/-- Let `g` and `h` lie in `mirabolic`, that is, they are integral invertible matrices at `P` whose
last column is the last basis vector modulo `N`, and let `D = diagNInv = diag (1, …, 1, N⁻¹)`. Then
`T ↦ mirrorDatum (D⁻¹ T)` is invariant under `T ↦ h⁻¹ T g`. -/
lemma mirrorDatum_mul_mul_of_mem_mirabolic {g : GL (n ⊕ Unit) (LocProd P)}
    {h : GL (n' ⊕ Unit) (LocProd P)}
    (hg : g ∈ Λ.mirabolic) (hh : h ∈ Λ.mirabolic)
    (T : Matrix (n' ⊕ Unit) (n ⊕ Unit) (LocProd P)) :
    Λ.mirrorDatum ((Λ.diagNInv (n := n'))⁻¹.val * (h⁻¹.val * T * g.val)) =
      Λ.mirrorDatum ((Λ.diagNInv (n := n'))⁻¹.val * T) := by
  obtain ⟨a, ha_fix, rfl⟩ := mem_mirabolic.1 hg
  -- In a basis of the enlarged target lattice, that is, after conjugation by `diagNInv`, the matrix
  -- `h⁻¹` is integral and fixes the last-coordinate form modulo `N`.
  obtain ⟨b, hb_row, hb⟩ : ∃ b : GL (n' ⊕ Unit) (O (F := LocProd P)),
      (Λ.reductionGL b).val (.inr ()) = lastBasisVector ∧
        inclGL b = Λ.diagNInv⁻¹ * h⁻¹ * Λ.diagNInv :=
    exists_inclGL_eq_conj_diagNInv (inv_mem hh)
  have h_corner (T' : Matrix (n' ⊕ Unit) (n ⊕ Unit) (P → ZMod N)) :
      ((Λ.reductionGL b).val * T' * (Λ.reductionGL a).val) (.inr ()) ⬝ᵥ lastBasisVector =
        T' (.inr ()) ⬝ᵥ lastBasisVector := by
    rw [Units.smul_def, smul_eq_mulVec] at ha_fix
    rw [mul_apply_eq_vecMul, mul_apply_eq_vecMul, ← dotProduct_mulVec, ha_fix, hb_row,
      single_one_vecMul, row_def]
  have h_move : (Λ.diagNInv (n := n'))⁻¹.val * (h⁻¹.val * T * (inclGL a).val) =
      (inclGL b).val * ((Λ.diagNInv (n := n'))⁻¹.val * T) * (inclGL a).val := by
    simp [hb, Matrix.mul_assoc]
  rw [h_move]
  refine (congrFun (liftFn_comp_mul _ a b) _).symm.trans ?_
  simp only [h_corner, mirrorDatum, charDatum]

/-! ## The operator `Up` -/

/-- `Up` preserves the vectors fixed by `mirabolic`, the group of integral invertible matrices at
`P` whose last column is the last basis vector modulo `N`. -/
lemma mirabolic_fix_upOperator
    (hφ : ∀ a : GL (n ⊕ Unit) (LocProd P), a ∈ Λ.mirabolic → π.ρ a φ = φ)
    {g : GL (n ⊕ Unit) (LocProd P)} (hg : g ∈ Λ.mirabolic) :
    π.ρ g (upOperator π φ) = upOperator π φ := by
  classical
  -- `k = diagNInv⁻¹ g diagNInv` is integral, and its last row is the last basis vector modulo `N`.
  obtain ⟨k, h_row, hk⟩ := exists_inclGL_eq_conj_diagNInv hg
  have h_last (y : n ⊕ Unit → P → ZMod N) : (reductionGL k • y) (.inr ()) = y (.inr ()) := by
    change (Λ.reductionGL k).val (.inr ()) ⬝ᵥ y = y (.inr ())
    rw [h_row, single_one_dotProduct]
  -- Both `k * lastRowColGL y` and `lastRowColGL (k y)` have last column `k y` modulo `N`, so they
  -- differ by an element of `mirabolic`.
  have h_term (y : n ⊕ Unit → P → ZMod N) (hy : IsUnit (y (.inr ()))) :
      π.ρ g (π.ρ (diagNInv * inclGL (lastRowColGL y)) φ) =
        π.ρ (diagNInv * inclGL (lastRowColGL (reductionGL k • y))) φ := by
    have h_mem : (diagNInv * inclGL (lastRowColGL (reductionGL k • y)))⁻¹ * g *
        (diagNInv * inclGL (lastRowColGL y)) ∈ Λ.mirabolic := by
      refine mem_mirabolic.2
        ⟨(lastRowColGL (reductionGL k • y))⁻¹ * k * lastRowColGL y, ?_, by simp [hk, mul_assoc]⟩
      rw [map_mul, map_mul, map_inv, mul_smul, mul_smul, inv_smul_eq_iff,
        lastRowColGL_smul_lastBasisVector hy,
        lastRowColGL_smul_lastBasisVector (by rwa [h_last])]
    rw [← π.ρ.inv_apply_eq_iff, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul,
      ← map_mul]
    exact hφ _ h_mem
  -- So `g` permutes the terms of the sum that defines `Up`, by `y ↦ k y`.
  simp only [upOperator, mul_sum, mul_smul_comm, ← map_mul, LinearMap.sum_apply,
    LinearMap.smul_apply, map_sum, map_smul]
  refine sum_equiv (toPerm (reductionGL k)) (by simp [h_last]) fun y hy ↦ ?_
  rw [h_term y (mem_filter.1 hy).2, toPerm_apply, h_last]

/-- An endomorphism of `π` that commutes with the action of all matrices at `P` commutes with `Up`
(`upOperator`). -/
lemma commute_upOperator {T : Module.End ℂ π}
    (hT : ∀ g : GL (n ⊕ Unit) (LocProd P), Commute T (π.ρ g)) : Commute T (upOperator π) :=
  (hT _).mul_right (Commute.sum_right _ _ _ fun _ _ ↦ (hT _).smul_right _)

lemma scalar_commute_upOperator (x : (O (F := LocProd P))ˣ) :
    Commute (π.ρ (inclGL (scalar (n ⊕ Unit) x))) (upOperator π) := by
  simp [upOperator, commute_iff_eq, mul_sum, sum_mul, ← map_mul, map_scalar,
    GeneralLinearGroup.scalar_commute]

omit [WeilData E] in
/-- A linear map `T` from `π` to `π'` that commutes with integral unit scalars sends ramified
vectors to ramified vectors. -/
lemma map_mem_ramified (T : π →ₗ[ℂ] π')
    (hT : ∀ (x : (O (F := LocProd P))ˣ) (ψ : π),
      π'.ρ (inclGL (scalar (n' ⊕ Unit) x)) (T ψ) = T (π.ρ (inclGL (scalar (n ⊕ Unit) x)) ψ))
    (hφ : φ ∈ ramified π) : T φ ∈ ramified π' := by
  intro w
  obtain ⟨x, hx_one, ψ, rfl⟩ := hφ w
  exact ⟨x, hx_one, T ψ, by simp [hT]⟩

/-- `Up` (`upOperator`) commutes with integral unit scalars, so it preserves ramified vectors. -/
lemma upOperator_mem_ramified (hφ : φ ∈ ramified π) : upOperator π φ ∈ ramified π :=
  map_mem_ramified _ (fun x ψ ↦ LinearMap.congr_fun (scalar_commute_upOperator x).eq ψ) hφ

/-- The powers of `Up` (`upOperator`) preserve ramified vectors. -/
lemma upOperator_pow_mem_ramified (hφ : φ ∈ ramified π) (q : ℕ) :
    (upOperator π ^ q) φ ∈ ramified π := by
  induction q with
  | zero => exact hφ
  | succ q ih => simpa [pow_succ'] using upOperator_mem_ramified ih

/-! ## Cutting a datum into pieces, and consequences of the lift law -/

omit [WeilData E] in
/-- Let `L` be linear in its datum. If the datum is `g (r T)` for a function `r` of the matrix `T`
modulo `N` with finitely many values, then the lift is the sum over the values `y` of `g y` times
the lift by the indicator of `r T = y`. -/
lemma liftFn_comp_eq_sum_smul {ι : Type} [Fintype ι] [DecidableEq ι]
    (r : Matrix (n' ⊕ Unit) (n ⊕ Unit) (P → ZMod N) → ι) (g : ι → ℂ) :
    L (liftFn fun T : Matrix (n' ⊕ Unit) (n ⊕ Unit) (P → ZMod N) ↦ g (r T)) φ =
      ∑ y : ι, g y • L (liftFn fun T : Matrix (n' ⊕ Unit) (n ⊕ Unit) (P → ZMod N) ↦
        if r T = y then 1 else 0) φ := by
  have h_sort : (fun T ↦ g (r T)) = ∑ y : ι, g y • fun T ↦ if r T = y then 1 else 0 := by ext; simp
  simp only [h_sort, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]

omit [CMType E] [WeilData E] [IsSplitLevel P N] in
/-- A vector modulo `N` that is non-zero at every place of `P` is the image of the last basis
vector under an invertible matrix modulo `N`. -/
lemma exists_GL_smul_lastBasisVector {y : n ⊕ Unit → P → ZMod N}
    (hy : ∀ w : P, ∃ a : n ⊕ Unit, IsUnit (y a w)) :
    ∃ k : GL (n ⊕ Unit) (P → ZMod N), k • lastBasisVector = y := by
  -- Choose such a matrix at each place and assemble them.
  choose g hg using fun w : P ↦ exists_GL_smul_single (hy w) (Sum.inr ())
  obtain ⟨k, hk⟩ : IsUnit (piRingEquiv.symm fun w : P ↦ (g w).val) :=
    (Pi.isUnit_iff.2 fun w ↦ (g w).isUnit).map piRingEquiv.symm
  refine ⟨k, funext₂ fun a w ↦ ?_⟩
  simpa [Units.smul_def, hk] using congrFun (hg w) a

namespace LiftLaw

section

omit [WeilData E]

/-- Let the lift `L Ψ : π → π'`, linear in its datum `Ψ`, obey the lift law. Then the lift by any
function `f` of matrices modulo `N`, extended by zero off the integral matrices (`liftFn f`),
preserves ramified vectors, because scalars pass through it. -/
lemma mem_ramified (H : LiftLaw π π' L γ) (f : Matrix (n' ⊕ Unit) (n ⊕ Unit) (P → ZMod N) → ℂ)
    (hφ : φ ∈ ramified π) : L (liftFn f) φ ∈ ramified π' := by
  refine map_mem_ramified _ (fun x ψ ↦ ?_) hφ
  rw [← H.integral_equivariant (scalar (n ⊕ Unit) x)⁻¹ (scalar (n' ⊕ Unit) x) f
    (π.ρ (inclGL (scalar (n ⊕ Unit) x)) ψ)]
  simp [← smul_eq_diagonal_mul, smul_eq_mul_diagonal, Matrix.mul_assoc]

/-- Let the lift `L Ψ : π → π'`, linear in its datum `Ψ`, obey the lift law, and let the function
`f` of matrices modulo `N` be invariant under the unit scalars that are `1` away from the place `w`.
Then the lift by `f`, extended by zero off the integral matrices (`liftFn f`), annihilates ramified
vectors: such a vector is `ψ - x ψ` for an integral unit scalar `x` that is `1` modulo `N` away from
`w`. -/
lemma apply_liftFn_eq_zero_of_smul_invariant (H : LiftLaw π π' L γ) (hφ : φ ∈ ramified π) (w : P)
    {f : Matrix (n' ⊕ Unit) (n ⊕ Unit) (P → ZMod N) → ℂ}
    (hf : ∀ c : P → ZMod N, IsUnit c → (∀ w' : P, w' ≠ w → c w' = 1) →
      ∀ T : Matrix (n' ⊕ Unit) (n ⊕ Unit) (P → ZMod N), f (c • T) = f T) :
    L (liftFn f) φ = 0 := by
  obtain ⟨x, hx_one, ψ, rfl⟩ := hφ w
  have h_fix : L (liftFn f) (π.ρ (inclGL (scalar (n ⊕ Unit) x)) ψ) = L (liftFn f) ψ := by
    simp [← smul_eq_mul_diagonal, ← H.integral_equivariant (scalar (n ⊕ Unit) x) 1 f ψ,
      hf _ (x.isUnit.map reduction) hx_one]
  simp [h_fix]

/-- Let the lift `L Ψ : π → π'` be linear in its datum `Ψ`, a function on matrices at `P`, and obey
the lift law; in particular integral invertible matrices move freely between the datum and the two
representations. Let `φ` be ramified: at each place `w` of `P` it is `ψ - x ψ` for an integral unit
scalar `x` that is `1` modulo `N` away from `w`. Let `r` map matrices modulo `N` to vectors modulo
`N` and commute with scalars, and let the vector `y` vanish at some place `w`. Then `φ` is
annihilated by the lift whose datum is the indicator of the integral matrices with reduction `T`
satisfying `r T = y`. -/
lemma apply_liftFn_indicator_eq_zero (H : LiftLaw π π' L γ) (hφ : φ ∈ ramified π) {ι : Type}
    [DecidableEq (ι → P → ZMod N)] (r : Matrix (n' ⊕ Unit) (n ⊕ Unit) (P → ZMod N) → ι → P → ZMod N)
    (hr : ∀ (c : P → ZMod N) (T : Matrix (n' ⊕ Unit) (n ⊕ Unit) (P → ZMod N)), r (c • T) = c • r T)
    {y : ι → P → ZMod N} {w : P} (hy : ∀ a : ι, y a w = 0) :
    L (liftFn fun T : Matrix (n' ⊕ Unit) (n ⊕ Unit) (P → ZMod N) ↦ if r T = y then 1 else 0) φ =
      0 := by
  refine H.apply_liftFn_eq_zero_of_smul_invariant hφ w fun c hc hc_one T ↦ ?_
  have h_fix : c • y = y := funext₂ fun a w' ↦ by
    by_cases hw : w' = w <;> simp [*]
  have h_iff : c • r T = y ↔ r T = y := by rw [← hc.smul_left_cancel (x := r T), h_fix]
  simp only [hr, h_iff]

/-- Let the lift `L Ψ : π → π'` be linear in its datum `Ψ` and obey the lift law `H`; in particular
integral invertible matrices move freely between the datum and the two representations. Let `k` be
an integral invertible matrix at `P`, and let `lastColDatum y` be the indicator of the integral
matrices with last column `y` modulo `N`. For every vector `φ` of `π`, the action of `inclGL k` on
`π'` takes the lift of `φ` by `lastColDatum y` to the lift of `φ` by
`lastColDatum (reductionGL k • y)`. -/
lemma inclGL_lastColDatum (H : LiftLaw π π' L γ) (k : GL (n' ⊕ Unit) (O (F := LocProd P)))
    (y : n' ⊕ Unit → P → ZMod N) :
    π'.ρ (inclGL k) (L (lastColDatum y) φ) = L (lastColDatum (reductionGL k • y)) φ := by
  -- The last column of `k T` is `k y` exactly if that of `T` is `y`.
  have h_col (T : Matrix (n' ⊕ Unit) (n ⊕ Unit) (P → ZMod N)) :
      ((reductionGL k).val * T)ᵀ (.inr ()) = reductionGL k • y ↔ Tᵀ (.inr ()) = y := by
    change reductionGL k • Tᵀ (.inr ()) = reductionGL k • y ↔ _
    rw [smul_left_cancel_iff]
  refine .trans ?_ (H.integral_equivariant 1 k _ φ)
  simp only [lastColDatum, map_one, Units.val_one, Matrix.mul_one, h_col, Module.End.one_apply]

end

/-- Let the lift `L Ψ : π → π'` be linear in its datum `Ψ` and obey the lift law `H`; in particular
integral invertible matrices move freely between the datum and the two representations. Let `k` be
an integral invertible matrix at `P`, with reduction `reductionGL k` modulo `N` and image `inclGL k`
among all invertible matrices. Let `charDatum y` be `ψ_N` of the last row paired with `y` modulo `N`
on integral matrices and zero elsewhere. For every vector `φ` of `π`, the lift of `π.ρ (inclGL k) φ`
by `charDatum (reductionGL k • y)` is the lift of `φ` by `charDatum y`. -/
lemma charDatum_inclGL (H : LiftLaw π π' L γ) (k : GL (n ⊕ Unit) (O (F := LocProd P)))
    (y : n ⊕ Unit → P → ZMod N) :
    L (charDatum (reductionGL k • y)) (π.ρ (inclGL k) φ) = L (charDatum y) φ := by
  have h_pair (T : Matrix (n' ⊕ Unit) (n ⊕ Unit) (P → ZMod N)) :
      (T * (reductionGL k).val) (.inr ()) ⬝ᵥ y = T (.inr ()) ⬝ᵥ reductionGL k • y :=
    (dotProduct_mulVec (T (.inr ())) (reductionGL k).val y).symm
  refine .trans ?_ (H.integral_equivariant k 1 _ φ)
  simp only [charDatum, map_one, Units.val_one, Matrix.one_mul, h_pair, Module.End.one_apply]

open scoped Classical in
/-- Let the lift `L Ψ : π → π'` be linear in its datum `Ψ` and obey the lift law; in particular
integral invertible matrices move freely between the datum and the two representations. Let `φ` be
ramified: at each place `w` of `P` it is `ψ - x ψ` for an integral unit scalar `x` that is `1`
modulo `N` away from `w`. Then the lift of `φ` does not change if `mirrorDatum` is restricted to the
matrices whose corner entry is a unit modulo `N`. -/
lemma mirrorDatum_eq_unitCorner (H : LiftLaw π π' L γ) (hφ : φ ∈ ramified π) :
    L mirrorDatum φ = L (liftFn fun T : Matrix (n' ⊕ Unit) (n ⊕ Unit) (P → ZMod N) ↦
      if IsUnit (T (.inr ()) (.inr ())) then psiN (T (.inr ()) (.inr ())) else 0) φ := by
  -- The datum is `ψ_N` of the corner entry `t`; sort both sides by `t`.
  simp only [mirrorDatum, charDatum, dotProduct_single_one]
  rw [liftFn_comp_eq_sum_smul _ psiN,
    liftFn_comp_eq_sum_smul _ fun t ↦ if IsUnit t then psiN t else 0]
  refine sum_congr rfl fun t _ ↦ ?_
  split_ifs with ht
  · rfl
  obtain ⟨w, hw⟩ : ∃ w : P, t w = 0 := by simpa [Pi.isUnit_iff] using ht
  suffices h_zero : L (liftFn fun T ↦ if T (.inr ()) (.inr ()) = t then 1 else 0) φ = 0 by
    simp [h_zero]
  simpa [funext_iff (α := Unit)] using H.apply_liftFn_indicator_eq_zero hφ
    (fun T _ ↦ T (.inr ()) (.inr ())) (fun _ _ ↦ rfl) (y := fun _ : Unit ↦ t) fun _ ↦ hw

/-- **Mirror data through direct data, on the target.** Let the lift `L Ψ : π → π'` be linear in its
datum `Ψ` and obey the lift law; in particular integral invertible matrices move freely between the
datum and the two representations. Let `φ` be ramified: at each place `w` of `P` it is `ψ - x ψ` for
an integral unit scalar `x` that is `1` modulo `N` away from `w`. Then the mirror lift of `φ`, moved
by `D = diagNInv = diag (1, …, 1, N⁻¹)`, is `Up` of the direct lift of `φ`. -/
lemma mirror_eq_upOperator_direct (H : LiftLaw π π' L γ) (hφ : φ ∈ ramified π) :
    π'.ρ Λ.diagNInv (L mirrorDatum φ) = upOperator π' (L directDatum φ) := by
  classical
  -- Sort by the last column `y`; its term is the translate of the direct lift by `lastRowColGL y`.
  have h_term (y : n' ⊕ Unit → P → ZMod N) (hy : IsUnit (y (.inr ()))) :
      L (lastColDatum y) φ = π'.ρ (inclGL (lastRowColGL y)) (L directDatum φ) := by
    rw [H.inclGL_lastColDatum, lastRowColGL_smul_lastBasisVector hy]
  have h_sort : L mirrorDatum φ = ∑ y : n' ⊕ Unit → P → ZMod N,
      (if IsUnit (y (.inr ())) then psiN (y (.inr ())) else 0) • L (lastColDatum y) φ :=
    (H.mirrorDatum_eq_unitCorner hφ).trans (liftFn_comp_eq_sum_smul (fun T ↦ Tᵀ (.inr ()))
      fun y ↦ if IsUnit (y (.inr ())) then psiN (y (.inr ())) else 0)
  rw [h_sort, upOperator, Module.End.mul_apply]
  congr 1
  simp only [ite_smul, zero_smul, ← sum_filter, LinearMap.sum_apply, LinearMap.smul_apply]
  exact sum_congr rfl fun y hy ↦ by rw [h_term y (mem_filter.1 hy).2]

/-- **Mirror data through direct data, on the source.** Let `π`, `π'` be representations (action
`ρ`) of `GL (n ⊕ Unit)`, `GL (n' ⊕ Unit)` over `LocProd P`. Let the lift `L Ψ : π → π'` be linear in
its datum `Ψ` and obey the lift law `H : LiftLaw`. Also, `D = diagNInv = diag (1, …, 1, N⁻¹)` moves
from `π'` to `π` at the cost `γ`, turning `lastRowDatum` into `directDatum`. Let `φ` be ramified: at
each place `w` of `P` it is `ψ - x ψ` for an integral unit scalar `x` that is `1` modulo `N` away
from `w`. Then the lift of `φ` by `mirrorDatum`, moved by `D`, is `γ` times the direct lift
`L directDatum` of `Up φ`. -/
lemma mirror_eq_direct_upOperator (H : LiftLaw π π' L γ) (hφ : φ ∈ ramified π) :
    π'.ρ Λ.diagNInv (L mirrorDatum φ) = γ • L directDatum (upOperator π φ) := by
  classical
  -- Sort by the last row `y`; its term is the lift by `lastRowDatum` after `lastRowColGL y`.
  have h_term (y : n ⊕ Unit → P → ZMod N) (hy : IsUnit (y (.inr ()))) :
      L (liftFn fun T ↦ if T (.inr ()) = y then 1 else 0) φ =
        L lastRowDatum (π.ρ (inclGL (lastRowColGL y)) φ) := by
    have h_row (T : Matrix (n' ⊕ Unit) (n ⊕ Unit) (P → ZMod N)) :
        (T * (reductionGL (lastRowColGL y)).val) (.inr ()) = y ↔ T (.inr ()) = lastBasisVector :=
      (vecMul_injective_of_isUnit (reductionGL (lastRowColGL y)).isUnit).eq_iff'
        (lastBasisVector_vecMul_lastRowColGL hy)
    rw [← H.integral_equivariant (lastRowColGL y) 1]
    simp only [lastRowDatum, map_one, Units.val_one, Matrix.one_mul, h_row, Module.End.one_apply]
  have h_sort : L mirrorDatum φ = ∑ y : n ⊕ Unit → P → ZMod N,
      (if IsUnit (y (.inr ())) then psiN (y (.inr ())) else 0) •
        L (liftFn fun T ↦ if T (.inr ()) = y then 1 else 0) φ :=
    (H.mirrorDatum_eq_unitCorner hφ).trans (liftFn_comp_eq_sum_smul (fun T ↦ T (.inr ()))
      fun y ↦ if IsUnit (y (.inr ())) then psiN (y (.inr ())) else 0)
  rw [h_sort, upOperator, Module.End.mul_apply, ← H.diagNInv_lastRowDatum]
  congr 1
  simp only [ite_smul, zero_smul, ← sum_filter, LinearMap.sum_apply, LinearMap.smul_apply,
    map_sum, map_smul]
  exact sum_congr rfl fun y hy ↦ by rw [h_term y (mem_filter.1 hy).2]

/-- Let the lift `L Ψ : π → π'`, linear in its datum `Ψ`, obey the lift law with factor `γ`, and let
`φ` be ramified: at each place `w` of `P` it is `ψ - x ψ` for an integral unit scalar `x` that is
`1` modulo `N` away from `w`. Then `Up` (`upOperator`) moves through the lift by `directDatum`, the
indicator of the integral matrices whose last column is the last basis vector modulo `N`, at the
cost of the factor `γ`. -/
lemma upOperator_direct (H : LiftLaw π π' L γ) (hφ : φ ∈ ramified π) :
    upOperator π' (L directDatum φ) = γ • L directDatum (upOperator π φ) :=
  (H.mirror_eq_upOperator_direct hφ).symm.trans (H.mirror_eq_direct_upOperator hφ)

open scoped Classical in
/-- Let the lifts `L Ψ : π → π'` and `L' Ψ : π' → π''` be linear in their data and obey the lift
law; in particular integral invertible matrices move freely between the datum and the two
representations. Let `φ` be ramified: at each place `w` of `P` it is `ψ - x ψ` for an integral unit
scalar `x` that is `1` modulo `N` away from `w`. Then the sum over `y` of
`L' (charDatum y) (L (lastColDatum y) φ)` equals the number of primitive vectors times
`L' mirrorDatum (L directDatum φ)`. -/
lemma sum_charDatum_lastColDatum (H : LiftLaw π π' L γ) [DecidableEq n'']
    {π'' : Rep ℂ (GL (n'' ⊕ Unit) (LocProd P))}
    {L' : (Matrix (n'' ⊕ Unit) (n' ⊕ Unit) (LocProd P) → ℂ) →ₗ[ℂ] π' →ₗ[ℂ] π''} {γ' : ℂ}
    (H' : LiftLaw π' π'' L' γ') (hφ : φ ∈ ramified π) :
    ∑ y : n' ⊕ Unit → P → ZMod N, L' (charDatum y) (L (lastColDatum y) φ) =
      #(primitiveVectors (P := P) (N := N) (n' ⊕ Unit)) • L' mirrorDatum (L directDatum φ) := by
  -- A term whose `y` vanishes at some place is zero.
  have h_support (y : n' ⊕ Unit → P → ZMod N)
      (hy : L' (charDatum y) (L (lastColDatum y) φ) ≠ 0) (w : P) :
      ∃ a : n' ⊕ Unit, IsUnit (y a w) := by
    by_contra! h_nonunit
    refine hy ?_
    rw [lastColDatum, H.apply_liftFn_indicator_eq_zero hφ (fun T ↦ Tᵀ (.inr ())) (fun _ _ ↦ rfl)
      (fun a ↦ by simpa using h_nonunit a), map_zero]
  -- The integral invertible matrices permute the primitive vectors transitively and cancel between
  -- the two lifts.
  have h_term (y : n' ⊕ Unit → P → ZMod N) (hy : y ∈ primitiveVectors (n' ⊕ Unit)) :
      L' (charDatum y) (L (lastColDatum y) φ) = L' mirrorDatum (L directDatum φ) := by
    obtain ⟨k, rfl⟩ := exists_GL_smul_lastBasisVector (mem_filter.1 hy).2
    rw [← reductionGL_liftGL k, ← H.inclGL_lastColDatum, H'.charDatum_inclGL]
  rw [← sum_eq_card_nsmul h_term, sum_filter_of_ne fun y _ ↦ h_support y]

open scoped Classical in
/-- Let the lifts `L Ψ : π → π'` and `L' Ψ : π' → π''` be linear in their data and obey the lift law
with factors `γ`, `γ'`: integral invertible matrices move freely between the datum and the two
representations, and `D = diagNInv = diag (1, …, 1, N⁻¹)` moves from target to source at the cost of
the factor, turning `lastRowDatum` into `directDatum`. Let `φ` be ramified: at each place `w` of `P`
it is `ψ - x ψ` for an integral unit scalar `x` that is `1` modulo `N` away from `w`. Then the
double lift of `φ` by `∑ y, lastColDatum y ⊗ charDatum y`, moved by `D`, is a scalar times the two
direct lifts of `Up φ` (`upOperator`). The scalar is `γ' γ` times the number of primitive
vectors. -/
lemma glued_eq_direct_direct_upOperator (H : LiftLaw π π' L γ) [DecidableEq n'']
    {π'' : Rep ℂ (GL (n'' ⊕ Unit) (LocProd P))}
    {L' : (Matrix (n'' ⊕ Unit) (n' ⊕ Unit) (LocProd P) → ℂ) →ₗ[ℂ] π' →ₗ[ℂ] π''} {γ' : ℂ}
    (H' : LiftLaw π' π'' L' γ') (hφ : φ ∈ ramified π) :
    π''.ρ Λ.diagNInv (∑ y : n' ⊕ Unit → P → ZMod N, L' (charDatum y) (L (lastColDatum y) φ)) =
      (#(primitiveVectors (P := P) (N := N) (n' ⊕ Unit)) • (γ' * γ)) •
        L' directDatum (L directDatum (upOperator π φ)) := by
  -- Separate into a mirror lift after a direct lift, replace the mirror lift by a direct lift after
  -- `Up`, and move `Up` through the first lift.
  let c : ℕ := #(primitiveVectors (P := P) (N := N) (n' ⊕ Unit))
  have h_ramified : L directDatum φ ∈ ramified π' := H.mem_ramified _ hφ
  calc π''.ρ Λ.diagNInv (∑ y : n' ⊕ Unit → P → ZMod N, L' (charDatum y) (L (lastColDatum y) φ))
      = c • π''.ρ Λ.diagNInv (L' mirrorDatum (L directDatum φ)) := by
        rw [H.sum_charDatum_lastColDatum H' hφ, map_nsmul]
    _ = c • γ' • L' directDatum (γ • L directDatum (upOperator π φ)) := by
        rw [H'.mirror_eq_direct_upOperator h_ramified, H.upOperator_direct hφ]
    _ = (c • (γ' * γ)) • L' directDatum (L directDatum (upOperator π φ)) := by
        rw [map_smul, smul_smul γ' γ, smul_assoc]

end LiftLaw

end IsSplitLevel

end

/-! ## Chains of lifts -/

namespace IsSplitLevel

variable {E : Type} [Field E] [CMType E] [WeilData E] {P : Finset (FinPlace E)}
  {N : ℕ} [Fact N.Prime] [Λ : IsSplitLevel P N]

-- A chain: `L j` is a lift from `π j` to `π (j + 1)`, with factor `γ j` in its lift law.
variable {X : ℕ → Type} [∀ j : ℕ, Fintype (X j)] [∀ j : ℕ, DecidableEq (X j)]
  (π : ∀ j : ℕ, Rep ℂ (GL (X j ⊕ Unit) (LocProd P)))
  {L : ∀ j : ℕ,
    (Matrix (X (j + 1) ⊕ Unit) (X j ⊕ Unit) (LocProd P) → ℂ) →ₗ[ℂ] π j →ₗ[ℂ] π (j + 1)}
  {γ : ℕ → ℂ}

omit [WeilData E] in
/-- If each `L j`, a lift from `π j` to `π (j + 1)` for places `P` above the split prime `N`, obeys
the lift law, then the composite of the first `j` direct lifts preserves ramified vectors. -/
lemma compUpTo_direct_mem_ramified (law : ∀ j : ℕ, LiftLaw (π j) (π (j + 1)) (L j) (γ j))
    {φ : π 0} (hφ : φ ∈ ramified (π 0)) (j : ℕ) :
    compUpTo (fun l : ℕ ↦ L l directDatum) j φ ∈ ramified (π j) := by
  induction j with
  | zero => exact hφ
  | succ j ih => exact (law j).mem_ramified _ ih

/-- Let each lift `L j Ψ : π j → π (j + 1)` obey the lift law with factor `γ j`. On ramified vectors
`Up` (`upOperator`) moves through the composite `L (j - 1) Ψ ∘ ⋯ ∘ L 0 Ψ` of the first `j` lifts by
`Ψ = directDatum` at the cost of `∏ l < j, γ l`. -/
lemma upOperator_compUpTo_direct (law : ∀ j : ℕ, LiftLaw (π j) (π (j + 1)) (L j) (γ j))
    {φ : π 0} (hφ : φ ∈ ramified (π 0)) (j : ℕ) :
    upOperator (π j) (compUpTo (fun l : ℕ ↦ L l directDatum) j φ) =
      (∏ l ∈ range j, γ l) •
        compUpTo (fun l : ℕ ↦ L l directDatum) j (upOperator (π 0) φ) := by
  induction j with
  | zero => simp [compUpTo]
  | succ j ih =>
    simp only [compUpTo, LinearMap.comp_apply]
    rw [(law j).upOperator_direct (compUpTo_direct_mem_ramified π law hφ j), ih, map_smul,
      smul_smul, prod_range_succ_comm]

/-- The `i`-th glued double lift of a chain of lifts `L j` between representations `π j`: it is
`d i` times the sum over the vectors `y` modulo `N` of the lift `L (2 i + 1)` by `charDatum y` after
the lift `L (2 i)` by `lastColDatum y`, moved by `diagNInv`. -/
abbrev gluedLift
    (L : ∀ j : ℕ,
      (Matrix (X (j + 1) ⊕ Unit) (X j ⊕ Unit) (LocProd P) → ℂ) →ₗ[ℂ] π j →ₗ[ℂ] π (j + 1))
    (d : ℕ → ℂ) (i : ℕ) : π (2 * i) →ₗ[ℂ] π (2 * (i + 1)) :=
  open scoped Classical in
  d i • (π (2 * i + 1 + 1)).ρ diagNInv ∘ₗ
    ∑ y : X (2 * i + 1) ⊕ Unit → P → ZMod N,
      L (2 * i + 1) (charDatum y) ∘ₗ L (2 * i) (lastColDatum y)

open scoped Classical in
/-- **All lifts become direct.** Let each lift `L j Ψ : π j → π (j + 1)` be linear in its datum `Ψ`
and obey the lift law with factor `γ j`: integral invertible matrices move freely between the datum
and the two representations, and `D = diagNInv = diag (1, …, 1, N⁻¹)` moves from target to source at
the cost `γ j`, turning `lastRowDatum` into `directDatum`. The glued double lift
`gluedLift π L d i : π (2 i) → π (2 i + 2)` is `d i` times `D` after `∑ y, L (2 i + 1) (charDatum y)
∘ L (2 i) (lastColDatum y)`, and `compUpTo f j` is `f (j - 1) ∘ ⋯ ∘ f 0`. Let `φ` be ramified: at
each place `w` of `P` it is `ψ - x ψ` for an integral unit scalar `x` that is `1` modulo `N` away
from `w`. Then the composite of the first `p` glued double lifts takes `φ` to a scalar times the
composite of `2 p` direct lifts of `Up ^ p φ`. The scalar is the product over `i < p` of `d i`, the
number of primitive vectors in the middle and `∏ l < 2 i + 2, γ l`. -/
lemma compUpTo_gluedLift_eq_smul (law : ∀ j : ℕ, LiftLaw (π j) (π (j + 1)) (L j) (γ j)) {φ : π 0}
    {d : ℕ → ℂ} (hφ : φ ∈ ramified (π 0)) (p : ℕ) :
    compUpTo (M := fun i : ℕ ↦ π (2 * i)) (gluedLift π L d) p φ =
    (∏ i ∈ range p, d i * #(primitiveVectors (P := P) (N := N) (X (2 * i + 1) ⊕ Unit)) •
        ∏ l ∈ range (2 * i + 2), γ l) •
      compUpTo (fun l : ℕ ↦ L l directDatum) (2 * p) ((upOperator (π 0) ^ p) φ) := by
  induction p with
  | zero => simp [compUpTo]
  | succ q ih =>
    let directLifts (j : ℕ) : π j :=
      compUpTo (fun l ↦ L l directDatum) j ((upOperator (π 0) ^ q) φ)
    have h_ramified (j : ℕ) : directLifts j ∈ ramified (π j) :=
      compUpTo_direct_mem_ramified π law (upOperator_pow_mem_ramified hφ q) j
    -- Move the `Up` of the last double lift through the earlier lifts to the source.
    have h_up : upOperator (π (2 * q)) (directLifts (2 * q)) = (∏ l ∈ range (2 * q), γ l) •
        compUpTo (fun l ↦ L l directDatum) (2 * q) ((upOperator (π 0) ^ (q + 1)) φ) := by
      rw [pow_succ', Module.End.mul_apply]
      exact upOperator_compUpTo_direct π law (upOperator_pow_mem_ramified hφ q) (2 * q)
    -- The scalar of the last double lift, with the cost of moving its `Up` to the source.
    have h_scalar : (d q * #(primitiveVectors (P := P) (N := N) (X (2 * q + 1) ⊕ Unit)) •
          (γ (2 * q + 1) * γ (2 * q))) * ∏ l ∈ range (2 * q), γ l =
        d q * #(primitiveVectors (P := P) (N := N) (X (2 * q + 1) ⊕ Unit)) •
          ∏ l ∈ range (2 * q + 2), γ l := by
      simp only [prod_range_succ, nsmul_eq_mul]
      ring
    -- Separate the last double lift into two direct lifts after `Up`.
    have h_pair : gluedLift π L d q (directLifts (2 * q)) =
        (d q * #(primitiveVectors (P := P) (N := N) (X (2 * q + 1) ⊕ Unit)) •
          ∏ l ∈ range (2 * q + 2), γ l) •
          compUpTo (fun l ↦ L l directDatum) (2 * (q + 1)) ((upOperator (π 0) ^ (q + 1)) φ) := by
      simp only [gluedLift, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.sum_apply]
      rw [(law (2 * q)).glued_eq_direct_direct_upOperator (law (2 * q + 1))
        (h_ramified (2 * q)), smul_smul (d q), h_up, map_smul, map_smul, smul_smul, h_scalar]
      -- The composite of `2 (q + 1)` lifts is by definition two lifts after the first `2 q`.
      rfl
    rw [compUpTo, LinearMap.comp_apply, ih, map_smul, prod_range_succ, mul_smul, h_pair]

end IsSplitLevel

end New

end
