import Lib.ClassField.Avatar.HeckeBaseChange
import Lib.ClassField.HeckeCharacter.TameModulus
import Lib.GLn.Branching.IntegralMap
import Lib.General.Algebra.LevelModulus
import New.UpperBound.Objects.LiftChains
import New.UpperBound.Objects.Weights
import New.UpperBound.Seesaw.AdmissibleCombinations

/-!
# Levels of the chain, chain data, and the composite lift

The map `New.Data.compositeLift` on source forms is built from chains of `m` theta lifts
`X_0 → X_1 → ⋯ → X_m` between definite unitary groups, followed by restriction to the block `Y_m` of
one rank less. Here `X_j` is an index set of `𝗇_j = k + j(t + 1)` elements. The weight at stage `j`
is given by the column numbers `New.Data.columnCount` and the determinant exponents
`New.Data.lastEntry`. This file defines the levels and spaces of forms of the stages, the
restriction from `X_m` to `Y_m`, the kernels of the lifts, the glued datum at `N` in the
Schrödinger model, and chain data.

## Main definitions and results

* `New.Data.restrictedChain`: ∑_x Ψ(x) · (chain with the data of x), then `New.Data.restrictToY`.
* `New.Data.IsChainDatum`, `New.Data.compositeLift`: chain data, and the same map for the data glued
  above `N` in each double lift.

Notions from other files:
* `New.classAut`: `classAut Γ K g` is Γ ∩ gKg⁻¹, the stabiliser in Γ of the coset gK; here
  Γ = `stdRatPoints` is the rational unitary group of the standard definite space `New.stdSpace`,
  inside the finite adelic group.
* `New.Data.n`: The rank 𝗇_j = k + j(t + 1) of X_j.
* `New.Data.columnCount`: The number of columns of height h < 𝗇_j at the infinite place τ in the
  weight on X_j; it does not depend on j. For h = 1 it is `D.a` at the places in `New.Data.aPlaces`
  and 0 elsewhere; for h = k ≠ 1 it is κ_1(τ) − ⌊𝗇_1 / 2⌋, with κ_j = `D.liftWeight j`; for h > k
  with h ≡ k mod t + 1 it is `D.gap` − (t + 1); otherwise it is 0.
* `New.chain` (in `New.UpperBound.Objects.LiftChains`): the composite of the first `j` theta lifts.
* `New.Data.chosenLevel` (in `New.UpperBound.Objects.LiftChains`): the integral elements that
  reduce to `1` at every chosen place, that is, at every prime divisor of `D.piM`.

## Relation to the literature

This file sets up the objects of the upper bound. Related work is listed with the results on them,
in `New.UpperBound.Divisibility.LocalDivisibility`, `New.UpperBound.Seesaw.SeesawIdentity` and
`New.UpperBound.Divisibility.ValuationAtLevel`.
-/

noncomputable section

/-!
## The glued datum at `N` in the Schrödinger model

For a set `P` with one place of each conjugate pair above `N`, functions of matrices at `P` define
operators on finite data (`IsSplitLevel.schrodingerOpAt`). For a double lift, the seesaw produces
the sum of translates `doubleLiftGluing`; read in the model at any such `P`, this sum is the glued
datum, with no constant.
-/

namespace New

open Matrix GeneralLinearGroup Fintype WeilData Exchange Finset Gf stdLattice Space Seesaw
  SemilocalField
open scoped TensorProduct

variable {E n n' : Type} [Field E] [CMType E] [WeilData E] [Fintype n]
  [DecidableEq n] [Fintype n'] [DecidableEq n'] {P S : Finset (FinPlace E)} {N : ℕ} [Fact N.Prime]
  {m : Type} [Fintype m] [DecidableEq m]

omit [WeilData E] in
/-- The component at a finite place `w` of the scalar element `ν` is the scalar matrix `ν w`. -/
@[simp] lemma scalarFin_atPlace (ν : unitary (𝔸f E)) (w : FinPlace E) :
    ((scalarFin n ν).atPlace w).1 = diagonal fun _ : n ↦ ν.1 w :=
  diagonal_map rfl

/-- Let `ν`, `ν'` be finite adeles of norm one. The Weil action with characters `a`, `b` of the pair
of scalar matrices `(ν, ν')` on the finite part for the standard spaces on `n` and `n'` is the value
of the character `pairChar a b`, `(g, h) ↦ a (det h) * (b (det g))⁻¹`, at this pair, times the
action with trivial characters of the pair of scalar matrices `(1, ν' / ν)`. -/
lemma Seesaw.pairWeilFinite_scalarFin (a b : AutChar E) (ν ν' : unitary (𝔸f E)) :
    pairWeilFinite (stdSpace E n) (stdSpace E n') a b (scalarFin n ν, scalarFin n' ν') =
      pairChar (s := 1) (s' := 1) a b ((1, scalarFin n ν), 1, scalarFin n' ν') •
        pairWeilFinite (stdSpace E n) (stdSpace E n') 1 1 (1, scalarFin n' (ν' / ν)) := by
  -- The characters factor out, and on `Hom` both pairs of scalars act by the scalar `ν' / ν`.
  have h_onHom : G.onHom (s := 1) (s' := 1) ((1, scalarFin n ν), 1, scalarFin n' ν') =
      G.onHom (s := 1) (s' := 1) ((1, (1 : Gf E n)), 1, scalarFin n' (ν' / ν)) := by
    rw [← map_one (scalarFin n), G.onHom_scalarFin, G.onHom_scalarFin, div_one]
  ext v x
  simp [pairWeil, h_onHom]

variable {E n : Type} [Field E] [NumberField E] {P : Finset (FinPlace E)} in
variable (n) in
/-- The finite adelic matrix whose last column is `-y / N` at the places of `P` and zero at the
other places, and whose other columns are zero. -/
abbrev Seesaw.poleColumn (y : n' → P → ZMod N) : n' × (n ⊕ Unit) → 𝔸f E :=
  fun p ↦ if p.2.isRight then -residueOverN (y p.1) else 0

variable (m) in
/-- The finite adelic matrix whose last row is the conjugate of `-y / N`, supported at the
conjugates of the places of `P`, and whose other rows are zero. -/
abbrev Seesaw.poleRow (y : n' → P → ZMod N) : (m ⊕ Unit) × n' → 𝔸f E :=
  fun p ↦ if p.1.isRight then -star (residueOverN (y p.2)) else 0

omit [WeilData E] [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fact N.Prime] in
/-- The entries of `poleColumn n y` vanish at the places outside `P`. -/
lemma Seesaw.poleColumn_apply_eq_zero (y : n' → P → ZMod N) (k : n' × (n ⊕ Unit)) (w : FinPlace E)
    (hw : w ∉ P) : poleColumn n y k w = 0 := by
  simp [poleColumn, apply_ite, ite_apply, hw]

omit [WeilData E] [Fintype n'] [DecidableEq n'] [Fact N.Prime] [Fintype m] [DecidableEq m] in
/-- The entries of `poleRow m y` vanish at the places whose conjugate is outside `P`. -/
lemma Seesaw.poleRow_apply_eq_zero (y : n' → P → ZMod N) (k : (m ⊕ Unit) × n') (w : FinPlace E)
    (hw_star : star w ∉ P) : poleRow m y k w = 0 := by
  simp [poleRow, apply_ite, ite_apply, hw_star]

open scoped Classical in
variable (n n' P N m) in
/-- For a double lift, the sum over the vectors `y / N` with at most simple poles at `P`, modulo
integral vectors, of the translation of the first datum by the last column `-y / N` and of the
second by the last row `-ȳ / N`. -/
def Seesaw.doubleLiftGluing : Module.End ℂ
    (((stdSpace E (n ⊕ Unit)).hom (stdSpace E n')).finitePart ⊗[ℂ]
      ((stdSpace E n').hom (stdSpace E (m ⊕ Unit))).finitePart) :=
  ∑ y : n' → P → ZMod N,
    TensorProduct.map (heisenbergFinPart _ (poleColumn n y)) (heisenbergFinPart _ (poleRow m y))

/-- The projection `V.projOn S` on the vacuum at the places of `S` and their conjugates, restricted
to the finite part of the data space of `V`. -/
abbrev Space.vacuumProjFinPart {s : n → ℤˣ} (V : Space E n s) (S : Set (FinPlace E)) :
    Module.End ℂ V.finitePart :=
  (V.projOn S).toLinearMap.restrict fun _ ↦ projOn_mem_finitePart

namespace IsSplitLevel

/-- The character `g ↦ χ (det g) |det g| ^ (-k / 2)` of `GL n` over `LocProd P`, the product of the
completions of `E` at the places of `P`. -/
def detCharAt (χ : HeckeChar E) (k : ℕ) : GL n (LocProd P) →* ℂˣ :=
  (localChar P χ (-k)).toUnitHom.comp det

/-- The operator `v ↦ Ψ ⊗ v` of the Schrödinger model at `P` on the finite part for the standard
spaces on `n` and `n'`, as a linear function of the function `Ψ` of matrices over `LocProd P`. Here
`Ψ` is read as a function of finite adelic matrices through their components at `P`. -/
def schrodingerOpAt [_h : IsSplitLevel P N] : (Matrix n' n (LocProd P) → ℂ) →ₗ[ℂ]
    Module.End ℂ ((stdSpace E n).hom (stdSpace E n')).finitePart :=
  LinearMap.mk₂ ℂ
    (fun Ψ v ↦ ⟨_, schrodingerOp_mem_finitePart P (Ψ ∘ fun T ↦ (vecToMatrix T).map (evalPlaces P))
      v.2⟩)
    (by simp [Pi.add_comp]) (by simp [Pi.smul_comp]) (by simp) (by simp)

variable [h : IsSplitLevel P N]

/-- The element of the finite adelic unitary group that is supported above `N` and has the given
components at `P`. -/
def embedGL : GL n (LocProd P) →* Gf E n :=
  (ofSplitPlaces h.star_notMem).comp (.pi fun w ↦ map (Pi.evalRingHom _ w))

omit [WeilData E] [Fact N.Prime] in
@[simp] lemma atPlaces_embedGL (g : GL n (LocProd P)) : atPlaces P (embedGL g) = g := by
  ext i j w : 3
  have h_at : (embedGL g).atPlace w = GeneralLinearGroup.map (Pi.evalRingHom _ w) g :=
    atPlace_ofSplitPlaces star_notMem _ w
  exact congrArg (fun k : GL n (LocField w.1) ↦ k i j) h_at

open scoped Classical in
omit [WeilData E] in
/-- At a place `w` of `P`, the component `atPlace w` of `embedGL (h.diagN n S)` is
`diag (1, …, 1, N)` if `w` is in `S`, and `1` otherwise. -/
lemma atPlace_embedGL_diagN (w : P) : (embedGL (h.diagN n S)).atPlace w =
    diagGL fun i : n ⊕ Unit ↦
      if i.isLeft then 1 else if ↑w ∈ S then .mk0 (N : LocField w.1) NeZero.out else 1 :=
  (atPlace_ofSplitPlaces star_notMem _ w).trans (by simp [diagN, Units.ext_iff])

omit [WeilData E] [Fact N.Prime] in
lemma embedGL_mem_supportedOn (g : GL n (LocProd P)) : embedGL g ∈ supportedOn n P :=
  ofSplitPlaces_mem_supportedOn star_notMem _

include h

section

omit [WeilData E] [Fact N.Prime]

lemma isConjDisjoint : Set.IsConjDisjoint (E := E) P := by grind [star_notMem]

lemma natCast_level_mem : ∀ w ∈ P, ↑N ∈ w.1 := fun w hw ↦ (h.natCast_mem_iff w).2 (.inl hw)

/-- Let `P` hold one place of each conjugate pair above the prime `N` (`IsSplitLevel P N`). An
element `g` of the finite adelic unitary group whose component at `P` is an integral invertible
matrix `a` (through `inclGL`) is integral at all places above `N`, that is,
`g ∈ integralAbove n N`. -/
lemma mem_integralAbove_of_inclGL_eq {g : Gf E n} {a : GL n (O (F := LocProd P))}
    (ha : inclGL a = atPlaces P g) : g ∈ integralAbove n N := by
  intro w hw
  have h_at (u : FinPlace E) (hu : u ∈ P) : g.atPlace u ∈ localIntGL n u :=
    let ⟨h_int, h_inv⟩ := mem_intGL.1 (⟨a, ha⟩ : atPlaces P g ∈ intGL n O)
    mem_intGL.2 ⟨fun i j ↦ h_int i j ⟨u, hu⟩ ⟨⟩, fun i j ↦ h_inv i j ⟨u, hu⟩ ⟨⟩⟩
  -- A place above `N` or its conjugate lies in `P`, and integrality passes to the conjugate.
  exact ((h.natCast_mem_iff w).1 hw).elim (h_at w) (atPlace_star_mem_iff.1 <| h_at _ ·)

end

section

omit [WeilData E]

/-- Let `x` be the component at `P` of `N u`, assumed integral. Its reduction modulo `N` is `c`
exactly when `u - c / N` is integral at `P`, with `c / N = residueOverN c`. -/
lemma reduction_eq_iff_idem_mul_mem {x : O (F := LocProd P)} {c : P → ZMod N} {u : 𝔸f E}
    (hx : x.1 = evalPlaces P (N * u)) :
    h.reduction x = c ↔ idem P * (u - residueOverN c) ∈ Ô E := by
  simp +contextual [hx, reduction_eq_iff, sub_div, idem_mul_mem_Ô, NeZero.ne]

omit h in
/-- Let `P` hold one place of each conjugate pair above the prime `N`, all unramified of degree one
(`IsSplitLevel P N`), and let `w` be in `P`. Let `ν` be an integral finite adele of norm one that
is `1` away from `w` and `w̄`. Then there is a unit `x` of the integers at `P`, with reduction `1`
modulo `N` at the places of `P` other than `w`, such that the scalar matrix `ν` is the unitary
element `embedGL` supported above `N` whose component at `P` is the scalar matrix `x`. -/
lemma exists_embedGL_scalar_eq_scalarFin [h : IsSplitLevel P N] {ν : unitary (𝔸f E)} (w : P)
    (h_int : ν.1 ∈ Ô E) (h_supp : ∀ v : FinPlace E, v ≠ w.1 → star v ≠ w.1 → ν.1 v = 1) :
    ∃ x : (O (F := LocProd P))ˣ, (∀ v : P, v ≠ w → h.reduction x v = 1) ∧
      h.embedGL (inclGL (scalar n x)) = scalarFin n ν := by
  -- `x` is the component of `ν` at `P`; its inverse is the component of `star ν`.
  have h_inv : evalPlaces P ν.1 * evalPlaces P (star ν.1) = 1 := by
    rw [← map_mul, ν.property.right, map_one]
  let x : (O (F := LocProd P))ˣ :=
    .mkOfMulEqOne ⟨_, evalPlaces_mem_O _ h_int⟩ ⟨_, evalPlaces_mem_O _ (star_mem_Ô h_int)⟩
      (Subtype.ext h_inv)
  refine ⟨x, fun v hv ↦ ?_, eq_of_supportedOn (embedGL_mem_supportedOn _) ?_ ?_⟩
  · -- `P` contains no pair of conjugate places, so `v` is neither `w` nor its conjugate.
    have h_one : ν.1 v = 1 := h_supp v (by grind) (by grind [star_notMem])
    have h_residue : residueAt v (x : O (F := LocProd P)) = 1 :=
      (congrArg (IsLocalRing.residue (LocInt v.1)) (Subtype.ext h_one)).trans (map_one _)
    exact (residueEquiv v).map_eq_one_iff.2 h_residue
  · simp +contextual (disch := grind) [Units.ext_iff, h_supp]
  · simp [x, Subtype.forall', embedGL, Units.ext_iff]

omit h [DecidableEq n] [DecidableEq n'] in
/-- Let `P` hold one place of each conjugate pair above the prime `N`, all unramified of degree one
(`IsSplitLevel P N`), so that `residueEquiv` identifies the residue fields at `P` with `ZMod N`.
Let `f` be a function of matrices modulo `N`, and `h.liftFn f` the function of matrices at `P` that
is `f` of the reduction on integral matrices and zero elsewhere. Evaluated on finite adelic matrices
through their components at `P`, it is the residue datum of `f`: the value of `f` at the residues
at `P` if the matrix is integral there, and zero otherwise. -/
lemma liftFn_eq_residueDatum [h : IsSplitLevel P N] (f : Matrix n' n (P → ZMod N) → ℂ) :
    (h.liftFn f ∘ fun T : n' × n → 𝔸f E ↦ (vecToMatrix T).map (evalPlaces P)) =
    residueDatum (fun w : P ↦ w.1) fun T : (w : P) → Matrix n' n (ResField w.1) ↦
      f (of fun (i : n') (j : n) (w : P) ↦ residueEquiv w (T w i j)) := by
  classical
  -- The conditions of integrality at `P` agree, and on integral entries so do the residue maps.
  refine funext fun x ↦ .symm (dite_congr ?_ (fun h_int ↦ ?_) (by simp))
  · simpa [mem_O_locProd] using
      ⟨fun h_int i j w hw ↦ h_int w hw i j, fun h_int w hw i j ↦ h_int i j w hw⟩
  · congr!
    exact congrArg _ (dite_eq_left _)

/-- The composite of `h.liftFn f` with the map sending `T` to the entrywise image of `vecToMatrix T`
under `evalPlaces P` is a Schwartz–Bruhat function at `P`. -/
instance isSchwartzBruhat_liftFn (f : Matrix n' n (P → ZMod N) → ℂ) :
    IsSchwartzBruhat P (h.liftFn f ∘ fun T : n' × n → 𝔸f E ↦
      (vecToMatrix T).map (evalPlaces P)) := by
  simpa [liftFn_eq_residueDatum] using
    isSchwartzBruhat_residueDatum (w := fun w : P ↦ w.1) _ (by grind [star_notMem])

omit h in
/-- Let `P` hold one place of each conjugate pair above the prime `N`, all unramified of degree one
(`IsSplitLevel P N`). Let `f` be a function of matrices modulo `N`, and `h.liftFn f` the function of
matrices at `P` that is `f` of the reduction on integral matrices and zero elsewhere. For invertible
matrices `g` and `k` at `P`, the function `T ↦ h.liftFn f (k⁻¹ T g)` of finite adelic matrices, read
through their components at `P`, is Schwartz–Bruhat at `P`. -/
lemma isSchwartzBruhat_liftFn_mul [h : IsSplitLevel P N] (g : GL n (LocProd P))
    (f : Matrix n' n (P → ZMod N) → ℂ) (k : GL n' (LocProd P)) :
    IsSchwartzBruhat P fun T : n' × n → 𝔸f E ↦
      h.liftFn f (k⁻¹.val * (vecToMatrix T).map (evalPlaces P) * g.val) := by
  rw [← atPlaces_embedGL g, ← atPlaces_embedGL k]
  -- The substitution `T ↦ k⁻¹ T g` is multiplication of the vector `T` by an invertible matrix.
  let M := (G.onHom (s := 1) (s' := 1) ((1, embedGL g), 1, embedGL k)).2⁻¹.1
  simpa only [M, onHom_snd_inv_mulVec, vecToMatrix_matrixToVec, Matrix.map_mul, Function.comp_def]
    using!
    (h.isSchwartzBruhat_liftFn f).comp_mulVec M

end

omit h in
/-- Let `P` hold one place of each conjugate pair above the prime `N`, all unramified of degree one
(`IsSplitLevel P N`). Let `Ψ = liftFn f` be `f` of the reduction modulo `N` on integral matrices at
`P` and zero elsewhere. Let `v` lie in the finite part of the Schwartz space of
`(stdSpace E n).hom (stdSpace E n')`, the matrices between the standard definite spaces, and let
`Ψ ⊗ v = schrodingerOpAt Ψ v` in the Schrödinger model at `P`. The Weil action `pairWeilFinite` with
characters `a`, `b` of the unitary elements above `N` with components `g`, `k` at `P` turns `Ψ ⊗ v`
into `(T ↦ Ψ (k⁻¹ T g)) ⊗ v`, times a scalar. The scalar is a quotient of values of
`detCharAt χ l : x ↦ χ (det x) |det x| ^ (-l / 2)`, for `χ = c.spaceChar l` the base change of `c`
divided by `υ ^ l`, with `υ` the splitting character: the value at `k` for `c = a`, `l = card n`,
over the value at `g` for `c = b`, `l = card n'`. -/
lemma pairWeilFinite_schrodingerOpAt [h : IsSplitLevel P N] (g : GL n (LocProd P))
    (f : Matrix n' n (P → ZMod N) → ℂ) (a b : AutChar E) (k : GL n' (LocProd P))
    (v : ((stdSpace E n).hom (stdSpace E n')).finitePart) :
    pairWeilFinite (stdSpace E n) (stdSpace E n') a b (h.embedGL g, h.embedGL k)
        (h.schrodingerOpAt (h.liftFn f) v) =
      ((detCharAt (b.spaceChar (card n')) (card n') g)⁻¹ *
          detCharAt (a.spaceChar (card n)) (card n) k) •
        h.schrodingerOpAt
          (fun T : Matrix n' n (LocProd P) ↦ h.liftFn f (k⁻¹.val * T * g.val)) v := by
  -- Read `g` and `k` on the right as the components at `P` of their lifts; then this is
  -- `pairWeil_schrodingerOp_of_mem_supportedOn`.
  nth_rw 2 3 [← atPlaces_embedGL g, ← atPlaces_embedGL k]
  ext1
  simp [schrodingerOpAt, detCharAt, pairWeil_schrodingerOp_of_mem_supportedOn, h.isConjDisjoint,
    embedGL_mem_supportedOn,
    -coe_units_inv, -atPlaces_embedGL]
  -- The two functions of matrices agree, and the two scalars differ only in notation.
  congr 1
  simp [-atPlaces_embedGL, field]

omit h [Fact N.Prime] in
/-- Let `P` hold one place of each conjugate pair above `N`, all unramified of degree one
(`IsSplitLevel P N`), and let the base change of `a` be unramified at every place of `P`. Let
`χ = a.spaceChar i` be this base change divided by the `i`-th power of the splitting character `υ`.
The character `detCharAt χ k: x ↦ χ (det x) |det x| ^ (-k / 2)` of the invertible matrices at `P` is
trivial on those that are invertible over the integers, which `inclGL` includes. -/
lemma detCharAt_inclGL [_h : IsSplitLevel P N] (a : AutChar E)
    (h_unr : ∀ w ∈ P, CharUnramifiedAt a.baseChange.finPart w) (i k : ℕ)
    (g : GL n (O (F := LocProd P))) : detCharAt (a.spaceChar i) k (inclGL g) = 1 := by
  -- The determinant is a unit at each place of `P`, where both characters in `spaceChar` are
  -- unramified.
  have h_unit : ∀ w : P, Valued.v ((g.val.det : LocProd P) w) = 1 :=
    isIntegralUnit_iff_v_eq_one.1 (isIntegralUnit_iff_isUnit.2 g.det.isUnit)
  have h_space (w : P) (u : (LocField w.1)ˣ) (hu : Valued.v u.val = 1) :
      (a.spaceChar i).finPart (locIdele w.1 u) = 1 := by
    simp [AutChar.spaceChar, h_unr w w.property u hu, charUnramifiedAt_upsilon w.1 u hu]
  ext
  simp [detCharAt, localChar, g.map_det, norm_locField_eq_q_zpow, h_unit, h_space]

section

omit [WeilData E]

omit h in
/-- Let `P` hold one place of each conjugate pair above the prime `N`, all unramified of degree one
(`IsSplitLevel P N`). The character `detCharAt χ k` is `g ↦ χ (det g) |det g| ^ (-k / 2)` over the
completions at `P`, and `h.diagN n S` is `diag (1, …, 1, N)` at `P ∩ S` and `1` at `P \ S`. For an
embedding `ι` of `ℂ` into `ℂ_[N]` and `k ≤ k'`, the `N`-adic size of `detCharAt χ k'` at this matrix
is at most that of `detCharAt χ k`, whatever the sizes of the two matrices. -/
lemma norm_detCharAt_diagN_anti [h : IsSplitLevel P N] {ι : ℂ →+* ℂ_[N]} {χ : HeckeChar E}
    {k k' : ℕ} (hk : k ≤ k') :
    ‖ι (detCharAt χ k' (h.diagN n S))‖ ≤ ‖ι (detCharAt χ k (h.diagN n' S))‖ := by
  classical
  -- The local determinant `d w` is `N` or `1`, of norm `N⁻¹` or `1`; the square root of this norm
  -- has `N`-adic size at least `1`, and it occurs with the exponent `-k`.
  let d (w : P) : (LocField w.1)ˣ := if ↑w ∈ S then .mk0 N NeZero.out else 1
  have hd_one_le (w : P) : 1 ≤ ‖ι √‖(d w).1‖‖ := by
    rw [← one_le_sq_iff₀ (by simp), ← norm_pow, ← map_pow]
    norm_cast
    by_cases hw : ↑w ∈ S
    · simp [d, hw, norm_locField_eq_q_zpow, h.q_eq, h.v_natCast, norm_p_eq_inv, NeZero.one_le,
        NeZero.ne]
    · simp [d, hw]
  -- In every rank the value is a product over `P` of local factors at the determinants `d w`.
  have h_norm {r : Type} [Fintype r] [DecidableEq r] (l : ℕ) :
      ‖ι (detCharAt χ l (h.diagN r S))‖ = ∏ w : P,
        ‖ι (χ.finPart (locIdele w.1 (d w)) : ℂ)‖ * (‖ι √‖(d w).1‖‖ ^ l)⁻¹ := by
    have h_det : (detCharAt χ l (h.diagN r S) : ℂ) =
        localChar P χ (-l) (MulEquiv.piUnits.symm d : (LocProd P)ˣ) := by
      simp [diagN, detCharAt, d]
    have h_component (w : P) : Units.map (Pi.evalMonoidHom (fun v : P ↦ LocField v.1) w)
        (MulEquiv.piUnits.symm d) = d w := rfl
    simp [h_det, localChar, h_component]
  rw [h_norm, h_norm]
  gcongr with w
  · simp
  · exact hd_one_le w

open scoped Classical in
/-- The matrix `diag (1, …, 1, N)` at all of `P` is the product of those at `P \ S` and at `S`. -/
lemma diagN_eq_sdiff_mul (S : Finset (FinPlace E)) : h.diagN n P = diagN n (P \ S) * diagN n S := by
  simp +contextual [diagN, ← map_mul, Pi.mul_def]

omit h in
/-- Let `P` hold one place of each conjugate pair above the prime `N`, all unramified of degree one
(`IsSplitLevel P N`). An adele is integral at `P` if it lies in the integral adeles `Ô E` after
multiplication by `idem P`, the adele that is `1` at `P` and `0` elsewhere. If `N z` is integral at
`P`, then `z - y / N` is integral at `P` for exactly one class `y` modulo `N`, and otherwise for
none. -/
lemma exists_sub_residueOverN_mem_iff [h : IsSplitLevel P N] (z : 𝔸f E) :
    ∃ b : P → ZMod N, ∀ y : P → ZMod N,
      idem P * (z - residueOverN y) ∈ Ô E ↔ idem P * ((N : 𝔸f E) * z) ∈ Ô E ∧ b = y := by
  -- `b` is the residue of `N z` at `P` when `N z` is integral there.
  let x : O (F := LocProd P) := Function.invFun Subtype.val (evalPlaces P (N * z))
  refine ⟨h.reduction x, fun y ↦ ?_⟩
  -- If `z - y / N` is integral at `P`, so is `N z = N (z - y / N) + y`.
  have h_int (hz : idem P * (z - residueOverN y) ∈ Ô E) : idem P * ((N : 𝔸f E) * z) ∈ Ô E := by
    simpa [mul_sub, mul_div_cancel₀, mem_O_locProd, idem_mul_mem_Ô, idem_apply, NeZero.ne] using
      add_mem (nsmul_mem (evalPlaces_mem_O _ hz) N)
        (mem_O_locProd.2 fun w ↦ natCast_mem (LocInt _) (y w).val)
  refine (iff_and_self.2 h_int).trans (and_congr_right fun hz ↦ ?_)
  have hx : x.1 = evalPlaces P (N * z) :=
    Function.invFun_eq (by simpa [mem_O_locProd, idem_mul_mem_Ô] using hz)
  exact (reduction_eq_iff_idem_mul_mem hx).symm

/-- The finite adele `residueOverN y`, which is `y w / N` at each `w ∈ P` and `0` elsewhere,
multiplied on the left by its conjugate `star (residueOverN y)`, is zero. -/
lemma star_residueOverN_mul_self (y : P → ZMod N) : star (residueOverN y) * residueOverN y = 0 := by
  rw [← idem_mul_residueOverN y, star_mul', mul_mul_mul_comm, mul_comm (star (idem _)),
    idem_mul_star h.isConjDisjoint, zero_mul]

end

section Glued

omit h

omit [WeilData E] [Fact N.Prime] in
/-- The idempotent of the places in `P` and their conjugates is that of the places in `S` and their
conjugates, both being the places above `N`. -/
lemma idem_add_star_eq [hP : IsSplitLevel P N] (hS : IsSplitLevel S N) :
    (idem P + star (idem P) : 𝔸f E) = idem S + star (idem S) := by
  ext w
  simp [idem_apply]
  grind [hP.star_notMem w, hS.star_notMem w, hP.natCast_mem_iff w, hS.natCast_mem_iff w]

omit [WeilData E] in
/-- Let `P` and `S` each hold one place of every conjugate pair above the prime `N`, all unramified
of degree one (`IsSplitLevel`). Let `y / N = residueOverN y` run over the classes with simple poles
at `S`. Let `p` be `N` at `S` and `1` elsewhere, so that `N + 1 - p` is `1` at `S` and `N`
elsewhere. If `t p` and `(N + 1 - p) s` are integral at `P`, then `t - y / N` and `s - ȳ / N` are
both integral at `P` for exactly one class `y`; otherwise for none. -/
lemma exists_sub_mem_and_sub_star_mem_iff [hP : IsSplitLevel P N] (hS : IsSplitLevel S N)
    {p : 𝔸f E} (hp : p = 1 + idem S * ((N : 𝔸f E) - 1)) (t s : 𝔸f E) :
    ∃ b : S → ZMod N, ∀ y : S → ZMod N,
      idem P * (t - residueOverN y) ∈ Ô E ∧ idem P * (s - star (residueOverN y)) ∈ Ô E ↔
        (idem P * (t * p) ∈ Ô E ∧ idem P * (((N : 𝔸f E) + 1 - p) * s) ∈ Ô E) ∧ b = y := by
  -- Integrality of an adele and its conjugate at `P` means integrality at all places above `N`.
  have h_closure (x : 𝔸f E) : idem P * x ∈ Ô E ∧ idem P * star x ∈ Ô E ↔
      idem S * x ∈ Ô E ∧ idem S * star x ∈ Ô E := by
    grind [IsSplitLevel, star_star, idem_mul_mem_Ô, v_star_apply]
  -- `b` is the class at `S` of the adele `z` that is `t` on `P` and `s̄` on the conjugates of `P`.
  let z : 𝔸f E := idem P * t + star (idem P * s)
  obtain ⟨b, hb⟩ := hS.exists_sub_residueOverN_mem_iff z
  refine ⟨b, fun y ↦ ?_⟩
  -- Apply this to `z - y / N` and to `p z`.
  have h_sub := h_closure (z - residueOverN y)
  have h_mul := h_closure (p * z)
  simp only [z, hp, star_sub, star_add, star_mul', star_star, star_one, star_natCast] at h_sub h_mul
  grind [hb y, idem_mul_star hP.isConjDisjoint, idem_mul_star hS.isConjDisjoint,
    hP.idem_add_star_eq hS, idem_mul_residueOverN, idem_mul_self, star_mul']

open scoped Classical in
/-- Let `P` and `S` each hold one place of every conjugate pair above the prime `N`, all unramified
of degree one (`IsSplitLevel`); neither need contain the other. Translate the indicators of the
matrices integral at `P`, in the Schrödinger model at `P`, by `poleColumn` and `poleRow` (last
column `-y / N` at `S`, last row its conjugate). The products of their values at `T` and `R`, summed
over `y`, give `gluedDatum T' R'` at `T' = T diag (1, …, 1, N)_S` and
`R' = diag (1, …, 1, N)_{P \ S} R`. This is zero unless `T'` and `R'` are integral at `P`, and then
it is `ψ_N c`, where `c` is the residue modulo `N` at `P` of the entry of `R' T'` in the last row
and last column. Here `ψ_N c = ψ₀ (-c / N)` (`psiN`), with `ψ₀` the additive character
`stdLattice.selfDualAddChar E`. So the sum is supported on the pairs `(T, R)` that are integral at
`P` up to simple poles in the last column of `T` at `P ∩ S` and in the last row of `R` at
`P \ S`. -/
lemma sum_translate_eq_gluedDatum [hP : IsSplitLevel P N] (hS : IsSplitLevel S N)
    (T : n' × (n ⊕ Unit) → 𝔸f E) (R : (m ⊕ Unit) × n' → 𝔸f E) :
    ∑ y : n' → S → ZMod N,
        schrodingerAct P (poleColumn n y) (boxIndicator (n' × (n ⊕ Unit)) P) T *
          schrodingerAct P (poleRow m y) (boxIndicator ((m ⊕ Unit) × n') P) R =
      hP.gluedDatum ((vecToMatrix T).map (evalPlaces P) * (hP.diagN n S).val)
        ((hP.diagN m (P \ S)).val * (vecToMatrix R).map (evalPlaces P)) := by
  -- Let `t` be the last column of `T` and `r` the last row of `R`. At most one class `b` makes
  -- `t - b / N` and `r - b̄ / N` integral at `P`, and its term is `ψ₀ (-r ⬝ t)`.
  let j : 𝔸f E := idem P
  let p : 𝔸f E := 1 + idem S * ((N : 𝔸f E) - 1)
  have h_class (i : n') : ∃ b : S → ZMod N, ∀ y : S → ZMod N,
      j * (T (i, .inr ()) - residueOverN y) ∈ Ô E ∧
        j * (R (.inr (), i) - star (residueOverN y)) ∈ Ô E ↔
      (j * (T (i, .inr ()) * p) ∈ Ô E ∧ j * ((N + 1 - p) * R (.inr (), i)) ∈ Ô E) ∧ b = y :=
    hP.exists_sub_mem_and_sub_star_mem_iff hS rfl _ _
  choose b hb using h_class
  have hD_S : (diagN n S).val = diagonal fun i ↦ evalPlaces P (if i.isLeft then 1 else p) := by
    simp +contextual [diagN, funext_iff, apply_ite, p, idem_apply]
  have hD_PS : (diagN m (P \ S)).val =
      diagonal fun i ↦ evalPlaces P (if i.isLeft then 1 else N + 1 - p) := by
    simp +contextual [diagN, funext_iff, apply_ite, p, idem_apply]
  have h_int (x : 𝔸f E) : evalPlaces P x ∈ O ↔ j * x ∈ Ô E := by
    simp [j, mem_O_locProd, idem_mul_mem_Ô]
  have h_norm (i : n') : star (residueOverN (b i)) * residueOverN (b i) = 0 :=
    hS.star_residueOverN_mul_self (b i)
  have hj_idem : j * j = j := idem_mul_self _
  have hp_mul : p * (N + 1 - p) = N := by grind [idem_mul_self]
  -- Each term is a character value on a set given by integrality conditions, and zero off it.
  simp [gluedDatum, charDatum, poleColumn, poleRow, hD_S, hD_PS, h_int, ← map_mul, vecToMatrix,
    schrodingerAct, ← ite_and, mem_integralBox, ← AddChar.map_add_eq_mul, liftFn_apply, ← map_sum,
    sum_prod_type, dotProduct, mul_sum]
  -- Only the class `b` contributes.
  rw [Fintype.sum_eq_single b fun y hy ↦ ite_eq_right fun h_y ↦
    hy (funext fun i ↦ ((hb i (y i)).1 (by grind)).right.symm)]
  replace hb (i : n') := hb i (b i)
  repeat split
  · -- Let `c` be the residue of `N r ⬝ t`. The two phases differ by
    -- `(t - b / N) ⬝ (r - b̄ / N) - (r ⬝ t - c / N)` at `P`, which is integral.
    generalize hc : hP.reduction _ = c
    have h_prod : ∑ i, j * (T (i, .inr ()) - residueOverN (b i)) *
        (j * (R (.inr (), i) - star (residueOverN (b i)))) ∈ Ô E :=
      sum_mem fun i _ ↦ ((hb i).2 (by grind)).elim mul_mem
    have h_red : j * (∑ i, R (.inr (), i) * T (i, .inr ()) - residueOverN c) ∈ Ô E := by
      refine (reduction_eq_iff_idem_mul_mem ?_).1 hc
      simp [-map_mul, mul_sum]
      grind
    apply selfDualAddChar_congr 0 (sub_mem h_prod h_red)
    simp [← sum_add_distrib, ← sum_neg_distrib, ← sum_sub_distrib, ← sub_add, mul_sub, mul_sum]
    grind [idem_mul_residueOverN]
  -- By `hb` the two supports agree.
  all_goals grind

open scoped Classical in
/-- **The glued datum in any model.** Let `P` and `S` each hold one place of every conjugate pair
above the prime `N`, all unramified of degree one (`IsSplitLevel`). Let `v`, `v'` be finite data of
`Hom (n + 1, n')` and `Hom (n', m + 1)`. Average each over the Heisenberg operators of the integral
vectors supported above `N` (`vacuumProjFinPart`), and apply `doubleLiftGluing`, the sum over `y`
modulo `N` at `S` of the translations by the last column `-y / N` and the last row `-ȳ / N`. The
result is given in the Schrödinger model at `P` by a sum over the vectors `z` modulo `N` at `P`.
Here `lastColDatum z` is the indicator of the matrices integral at `P` whose last column reduces to
`z` modulo `N`. The function `charDatum z` is zero off the integral matrices, and on these it is
`ψ_N (r ⬝ᵥ z)`, with `r` the reduction of the last row and `ψ_N c = ψ₀ (-c / N)` (`psiN`) for the
additive character `ψ₀ = stdLattice.selfDualAddChar E`. The matrices are first multiplied by
`hP.diagN n S` and `hP.diagN m (P \ S)`, which are `diag (1, …, 1, N)` at `P ∩ S` and at `P \ S`
respectively, and `1` at the other places of `P`. -/
lemma doubleLiftGluing_eq_sum_schrodingerOpAt [hP : IsSplitLevel P N] (hS : IsSplitLevel S N)
    (v : ((stdSpace E (n ⊕ Unit)).hom (stdSpace E n')).finitePart)
    (v' : ((stdSpace E n').hom (stdSpace E (m ⊕ Unit))).finitePart) :
    doubleLiftGluing n n' S N m
        (vacuumProjFinPart ((stdSpace E (n ⊕ Unit)).hom (stdSpace E n')) S v ⊗ₜ[ℂ]
          vacuumProjFinPart ((stdSpace E n').hom (stdSpace E (m ⊕ Unit))) S v') =
      ∑ z : n' → P → ZMod N,
        hP.schrodingerOpAt (fun T : Matrix n' (n ⊕ Unit) (LocProd P) ↦
            hP.lastColDatum z (T * (hP.diagN n S).val)) v ⊗ₜ[ℂ]
          hP.schrodingerOpAt (fun R : Matrix (m ⊕ Unit) n' (LocProd P) ↦
            hP.charDatum z ((hP.diagN m (P \ S)).val * R)) v' := by
  -- Both sides come from tensors of functions, and these tensors have the same values.
  let F (y : n' → S → ZMod N) := schrodingerAct P (poleColumn n y) (boxIndicator _ P)
  let G (y : n' → S → ZMod N) := schrodingerAct P (poleRow m y) (boxIndicator _ P)
  let F' (z : n' → P → ZMod N) (T : n' × (n ⊕ Unit) → 𝔸f E) : ℂ :=
    hP.lastColDatum z ((vecToMatrix T).map (evalPlaces P) * (hP.diagN n S).val)
  let G' (z : n' → P → ZMod N) (R : (m ⊕ Unit) × n' → 𝔸f E) : ℂ :=
    hP.charDatum z ((hP.diagN m (P \ S)).val * (vecToMatrix R).map (evalPlaces P))
  have h_kernel : ∑ y, F y ⊗ₜ[ℂ] G y = ∑ z, F' z ⊗ₜ G' z := by
    refine sub_eq_zero.1
      (tensor_eq_zero_of_separating (f := .proj) funext _ fun T ↦ funext fun R ↦ ?_)
    simpa [sub_eq_zero, gluedDatum_eq_sum] using hP.sum_translate_eq_gluedDatum hS T R
  have h_supp (y : S → ZMod N) :
      (idem S + star (idem S)) * residueOverN y = residueOverN y ∧
      (idem S + star (idem S)) * star (residueOverN y) = star (residueOverN y) := by
    grind [idem_mul_star hS.isConjDisjoint, idem_mul_residueOverN, star_mul']
  let applyModel := TensorProduct.map
    ((ContinuousLinearMap.apply ℂ _ v.val).toLinearMap ∘ₗ Space.schrodingerOp _ P)
    ((ContinuousLinearMap.apply ℂ _ v'.val).toLinearMap ∘ₗ Space.schrodingerOp _ P)
  apply Module.Flat.tensorProduct_mapIncl_injective_of_left
  calc
    _ = applyModel (∑ y, F y ⊗ₜ G y) := by
      -- A translated indicator gives a translate of the projection on vacua, and this projection
      -- is the same for `P` and `S`.
      simp [applyModel, F, G, doubleLiftGluing, poleColumn, poleRow, hP.idem_add_star_eq hS, h_supp,
        hS.star_residueOverN_mul_self, mul_comm (residueOverN _), projOn, finHeisenbergOp, semichar,
        idem_conjClosure_eq_add_star, schrodingerOp_schrodingerAct_boxIndicator,
        isConjDisjoint (N := N), Pi.smul_def, apply_ite, dotProduct]
    _ = applyModel (∑ z, F' z ⊗ₜ G' z) := congrArg applyModel h_kernel
    _ = _ := by simp [applyModel, F', G', schrodingerOpAt, Function.comp_def]

end Glued

end IsSplitLevel

end New

/-!
## Levels, spaces of forms and branching along the chain

* `New.Data.IsBranchingMap`: the properties of an integral branching matrix from `X_m` to `Y_m`.
  It intertwines the actions up to the character with exponents `New.Data.branchExponent`. Its
  operator norm is bounded, and over `ℂ` it spans the equivariant maps.

A weight is a pair `(κ, e)`: `κ τ h` counts the columns of height `h` of the diagram at `τ`, and
`e τ` is the power of the determinant (`New.weylRep`).
-/

section ColumnDefs

open Matrix Finset Subgroup Ideal Fintype

namespace New.Data

variable {P : Parameters} (D : Data P) (j : ℕ) {w : FinPlace D.E}

/-! ### The primes dividing `π` -/

@[simp] lemma piN_ne_zero : D.piN ≠ 0 := by grind [piN_mul_star, NeZero.natCast_ne]

/-- The finite set of primes w of E dividing π = `D.piN`, the integer of E with π π̄ = N. -/
def piNPlaces : Finset (FinPlace D.E) :=
  (finite_factors (span_singleton_eq_bot.ne.mpr D.piN_ne_zero)).toFinset

lemma mem_piNPlaces : w ∈ D.piNPlaces ↔ D.piN ∈ w.asIdeal := by simp [piNPlaces]

/-- Of a place `w` above the prime `D.N` and its conjugate `star w`, exactly one lies in
`D.piNPlaces`, that is, divides the integer `D.piN` of E. -/
lemma star_mem_piNPlaces_iff (hN_mem : ↑D.N ∈ w.asIdeal) :
    star w ∈ D.piNPlaces ↔ w ∉ D.piNPlaces := by
  rw [mem_piNPlaces, mem_piNPlaces, mem_star_place]
  exact P.star_mem_iff_notMem D.N_modEq_one hN_mem D.piN_mul_star_eq_N_mul_one D.N.coprime_one_right

/-- The primes `D.piNPlaces` dividing `π = D.piN`, the integer of `E` with `π π̄ = N`, are split of
degree one above `N = D.N` (`IsSplitLevel`): none is conjugate to one of them, each has norm `N`,
and `N` is a uniformiser at each. -/
protected lemma isSplitLevel_piNPlaces : IsSplitLevel D.piNPlaces D.N := by
  -- As `π * star π = N` and `N` splits completely, a place above `N` has norm `N` and contains
  -- exactly one of `π` and `star π`.
  have N_mem {w : FinPlace D.E} (hw : w ∈ D.piNPlaces) : ↑D.N ∈ w.asIdeal := by
    simpa only [piN_mul_star] using w.asIdeal.mul_mem_right (star D.piN) (D.mem_piNPlaces.1 hw)
  refine
    { star_notMem := fun w hw h_star ↦ (D.star_mem_piNPlaces_iff (N_mem hw)).1 h_star hw
      q_eq := fun w hw ↦ P.q_eq_of_modEq_one D.N_modEq_one (N_mem hw)
      v_natCast := fun w hw ↦ v_N_eq_exp_neg_one (N_mem hw)
      natCast_mem_iff := fun w ↦ ⟨fun hw ↦ by simp [D.star_mem_piNPlaces_iff hw, em], ?_⟩ }
  exact fun h_or ↦ h_or.elim N_mem fun h_star ↦ by
    simpa only [mem_star_place, star_natCast] using N_mem h_star

/-- The number of primes of E dividing π = `D.piN` (the set `D.piNPlaces`) equals `D.f`, the number
of infinite places of E. -/
lemma card_piNPlaces : #D.piNPlaces = D.f := by
  -- The infinite places are in bijection with the finite places containing both `π` and `N`.
  obtain ⟨e⟩ : Nonempty (D.Φ ≃ {w : FinPlace D.E // D.piN ∈ w.asIdeal ∧ ↑D.N ∈ w.asIdeal}) :=
    P.nonempty_infinitePlace_equiv_finPlace D.N_modEq_one D.piN_mul_star_eq_N_mul_one
      D.N.coprime_one_right
  simpa [and_iff_left_of_imp (D.isSplitLevel_piNPlaces.natCast_level_mem _), ← mem_piNPlaces] using
    e.cardinal_eq.symm

/-! ### The level of stage `j` -/

/-- The level of stage j: elements of the chosen level `New.Data.chosenLevel` on X_j whose last row
is congruent to (0, …, 0, 1) modulo π. -/
def levelX : Subgroup (Gf D.E (D.X j)) :=
  D.chosenLevel (n := D.X j) ⊓
    (congruenceGL (Ô D.E ∙ algebraMap (NumberField.RingOfIntegers D.E) (𝔸f D.E) D.piN)
        Sum.inr).subgroupOf (U 1)

lemma principalLevel_le_levelX : principalLevel (D.X j) (D.piM * D.piN) ≤ D.levelX j := by
  -- Level `piM * π` lies in level `piM` and in level `π`; the latter constrains every row.
  intro g hg
  have hg_π : g ∈ principalLevel (D.X j) D.piN := principalLevel_le_of_dvd (dvd_mul_left ..) hg
  exact ⟨D.principalLevel_le_chosenLevel (by simp) hg, hg_π.imp_right (by simp)⟩

/-- The level of stage j is a level: it lies in `New.stdLevel` and is open. -/
instance isLevel_levelX {j : ℕ} : IsLevel (D.levelX j) where
  le := inf_le_of_left_le levelOf_le_stdLevel
  isOpen := isOpen_mono (D.principalLevel_le_levelX j) (isOpen_principalLevel (by simp))

/-- A chosen bijection between the finite index sets Y_m and `InitIndex m`, which have the same
cardinality. -/
def lastIndexEquiv : D.Y D.m ≃ D.InitIndex D.m :=
  Fintype.equivOfCardEq <| by
    simp only [BlockIndex.card, card_sum, Fintype.card_fin, card_unique]
    grind [ϱ, n]

lemma card_X : card (D.X j) = D.n j := by
  simpa using Nat.sub_add_cancel (by grind [n] : 1 ≤ D.n j)

lemma card_Y_m : card (D.Y D.m) = D.n D.m - 1 :=
  (card_congr D.lastIndexEquiv).trans (Fintype.card_fin _)

/-- For each `i`, the `i`-th row length of the diagram with `D.columnCount τ u` columns of each
height `u < n_{j+1}` (`New.diagramWeight`; `rankAt` gives the rank at `τ`) is row `i` of the diagram
`New.Data.liftDiagram` of lift `j + 1`. -/
lemma cast_diagramWeight_columnCount (τ : D.Φ) (i : ℕ) :
    (diagramWeight (rankAt fun _ : D.Φ ↦ D.X (j + 1)) D.columnCount (τ, i) : ℤ) =
      D.liftDiagram j τ i := by
  rw [diagramWeight_apply, rankAt, card_X, liftDiagram_eq_sum_columnCount]

/-- The properties of a branching map from the Weyl module of the weight `μ(X_m)` to that of
`μ(Y_m)`. The weights have the column numbers `D.columnCount` and `D.columnsY`, and both have the
determinant exponents `D.lastEntry D.m`. -/
structure IsBranchingMap
    (br : Matrix (WeylIndex (D.Y D.m) D.columnsY) (WeylIndex (D.X D.m) D.columnCount) ℤ) :
      Prop where
  /-- Over every field of characteristic zero, `br` takes the action of `y = diag (g, z)` to
  `∏ τ, z τ ^ n_τ` times the action of `g`, where `n_τ = D.branchExponent τ` is the sum of the
  entries of `μ(X_m)` at `τ` less that of `μ(Y_m)`. -/
  mul_weylRep (R : Type) [Field R] [CharZero R] (g : D.Φ → GL (D.Y D.m) R) (z : D.Φ → Rˣ)
    (y : D.Φ → GL (D.X D.m) R)
    (hy : ∀ τ : D.Φ, (y τ).val = GL.blockScalar (fun _ ↦ D.lastIndexEquiv.sumCongr (.refl Unit))
      (fun τ : D.Φ ↦ (g τ).val) (fun τ : D.Φ ↦ (z τ).val) τ) :
    br.map ((↑) : ℤ → R) * weylRep D.columnCount (D.lastEntry D.m) y =
      (∏ τ : D.Φ, z τ ^ D.branchExponent τ) •
        (weylRep D.columnsY (D.lastEntry D.m) g * br.map ((↑) : ℤ → R))
  /-- The square of the operator norm of `br` is at most `exp (x ^ 70)`, with `x = D.x` the length
  of the prime sum. -/
  weylNormSq_le (ξ : WeylIndex (D.X D.m) D.columnCount → ℂ) :
    weylNormSq (br.map (↑) *ᵥ ξ) ≤ Real.exp (D.x ^ 70) * weylNormSq ξ
  /-- Every complex matrix that is equivariant for the elements `diag (g, 1)`, `g` unitary, is a
  multiple of `br`. -/
  spans : SpansBranchingMaps (fun _ ↦ D.lastIndexEquiv.sumCongr (.refl Unit)) (D.lastEntry D.m)
    (D.lastEntry D.m) (br.map (↑))

/-- The weight on `Y_m` has `D.columnsY τ u` columns of height `u` at the infinite place `τ`. There
is a number `l` that bounds the boxes in the columns of height at least `k` and less than
`n_m - 1`, summed over `τ`, and satisfies `((l ^ l) ^ 3) ^ 2 ≤ exp (x ^ 70)`, with `x = D.x` the
length of the prime sum. -/
lemma exists_sum_columnsY_le_and_pow_le_exp :
    ∃ l : ℕ, (∑ τ : D.Φ, ∑ u ∈ Ico D.k (card (D.Y D.m)), u * D.columnsY τ u ≤ l) ∧
      (((l : ℝ) ^ l) ^ 3) ^ 2 ≤ Real.exp (D.x ^ 70) := by
  -- Take `l = f n_m² Δ`, with `Δ = D.gap`.
  refine ⟨∑ _ : D.Φ, D.n D.m * (D.n D.m * D.gap), sum_le_sum fun τ _ ↦ ?_, ?_⟩
  · -- at most `n_m` heights, each below `n_m`, and at most `Δ` columns of each height
    rw [card_Y_m]
    refine (sum_le_card_nsmul _ _ (D.n D.m * D.gap) fun u hu ↦ ?_).trans ?_
    · exact Nat.mul_le_mul (by grind) (D.columnsY_le τ (mem_Ico.1 hu).1)
    · exact Nat.mul_le_mul_right _ (by grind [Nat.card_Ico])
  · refine Real.le_exp_of_log_le ?_
    push_cast [sum_const, card_univ, smul_eq_mul, Real.log_pow]
    exact D.le_of_hasLogBound

/-- There is an integer matrix `br` from the Weyl module on `X_m` to that on `Y_m` that is a
branching map (`IsBranchingMap`). It is equivariant for the block matrices `diag (g, z)` up to the
character `∏ τ, z τ ^ n_τ`, where `n_τ = D.branchExponent τ` is the sum of the entries of the weight
on `X_m` at `τ` less that on `Y_m`. The square of its operator norm is at most `exp (x ^ 70)`, with
`x = D.x` the length of the prime sum. Over `ℂ` it spans the maps that are equivariant for
`diag (g, 1)`, `g` unitary. -/
lemma exists_isBranchingMap :
    ∃ br : Matrix (WeylIndex (D.Y D.m) D.columnsY) (WeylIndex (D.X D.m) D.columnCount) ℤ,
      D.IsBranchingMap br := by
  -- The weights interlace: the columns counted by `keptColumns` keep their height, the others lose
  -- a box. As `keptColumns` vanishes below height `k`, the norm bound omits the heights below `k`.
  have h_split : (D.columnCount - fun _ ↦ D.keptColumns) + (fun _ ↦ D.keptColumns) =
    D.columnCount :=
    tsub_add_cancel_of_le fun τ u ↦ D.keptColumns_le_columnCount τ u
  have h_last (τ : D.Φ) :
      D.lastEntry D.m τ = D.lastEntry D.m τ + D.keptColumns (card (D.Y D.m)) := by
    rw [card_Y_m, keptColumns_n_sub_one, Nat.cast_zero, add_zero]
  have h_interlace (τ : D.Φ) (u : ℕ) (_ : u ∈ Ioo 0 (card (D.Y D.m))) :
      D.columnsY τ u = D.keptColumns u + (D.columnCount τ (u + 1) - D.keptColumns (u + 1)) := rfl
  obtain ⟨br, h_equivariant, h_norm, h_span⟩ := exists_branching_matrix
    (fun _ : D.Φ ↦ D.lastIndexEquiv.sumCongr (.refl Unit)) D.columnsY D.k (D.lastEntry D.m)
    (D.lastEntry D.m) h_split h_interlace (fun _ _ ↦ D.keptColumns_eq_zero_of_lt_k) h_last
  refine ⟨br, fun R _ _ g z y hy ↦ ?_, fun ξ ↦ ?_, h_span⟩
  · rw [h_equivariant R g z y hy]
    simp only [diagramWeight_apply, rankAt, card_X, branchExponent_eq_sum_columns, Pi.sub_apply]
  · obtain ⟨l, h_boxes, h_exp⟩ := D.exists_sum_columnsY_le_and_pow_le_exp
    exact (h_norm l h_boxes ξ).trans (mul_le_mul_of_nonneg_right h_exp (weylNormSq_nonneg ξ))

/-- A fixed branching map `br` from the Weyl module of `μ(X_m)` to that of `μ(Y_m)`. -/
def branching : Matrix (WeylIndex (D.Y D.m) D.columnsY) (WeylIndex (D.X D.m) D.columnCount) ℤ :=
  D.exists_isBranchingMap.choose

lemma isBranchingMap_branching : D.IsBranchingMap D.branching :=
  D.exists_isBranchingMap.choose_spec

/-- The level of stage 0 is free: for the group `Γ` of rational points and this level `K`, the
groups `Γ ∩ g K g⁻¹` are trivial. -/
lemma classAut_levelX_zero_eq_bot :
    ∀ g : Gf D.E (D.X 0), classAut stdRatPoints (D.levelX 0) g = ⊥ :=
  D.classAut_eq_bot_of_le_chosenLevel inf_le_left (by grind [card_X, n])

/-! ### Source forms and smooth forms -/

/-- The space of source forms: algebraic forms on X_0 of weight (`D.columnCount`, `D.lastEntry 0`)
(column numbers, determinant exponents) fixed by the level `New.Data.levelX` of stage 0. -/
abbrev SourceForm := levelSpace (algFormRep D.columnCount (D.lastEntry 0)) (D.levelX 0)

/-- The space of smooth algebraic forms on X_j of weight (`D.columnCount`, `D.lastEntry j`): column
numbers and determinant exponents. -/
abbrev FormX : Submodule ℂ (Gf D.E (D.X j) → WeylIndex (D.X j) D.columnCount → ℂ) :=
  AlgForm (D.X j) D.columnCount (D.lastEntry j)

/-! ### Restriction of forms from `X_m` to `Y_m` -/

/-- The homomorphism g ↦ diag(g, 1) from the finite adelic unitary group on Y_m to that on X_m,
relabelling along `New.Data.lastIndexEquiv`. -/
def borderU :
    U (1 : Matrix (D.Y D.m) (D.Y D.m) (𝔸f D.E)) →*
      U (1 : Matrix (D.InitIndex D.m ⊕ Unit) (D.InitIndex D.m ⊕ Unit) (𝔸f D.E)) :=
  (U.block (R := 𝔸f D.E) (D.lastIndexEquiv.sumCongr (Equiv.refl Unit))).comp
    (MonoidHom.inl (U 1) (U (1 : Matrix Unit Unit (𝔸f D.E))))

/-- The restriction of algebraic forms from X_m to Y_m: restrict to points diag(h,1), apply the
branching matrix, and multiply by ∏_τ τ(π̄)^{−n_τ}, τ read as its embedding in the CM type. -/
def restrictToY :
    AlgForm (D.InitIndex D.m ⊕ Unit) D.columnCount (D.lastEntry D.m) →ₗ[ℂ]
      AlgForm (D.Y D.m) D.columnsY (D.lastEntry D.m) :=
  (∏ τ : NumberField.InfinitePlace D.E, Φ τ (star ↑D.piN) ^ (-D.branchExponent τ)) •
    ((D.branching.map (↑)).mulVecLin.compLeft (U 1) ∘ₗ
      .funLeft ℂ (WeylIndex (D.X D.m) D.columnCount → ℂ) D.borderU).restrict
      (p := AlgForm (D.InitIndex D.m ⊕ Unit) D.columnCount (D.lastEntry D.m))
      (q := AlgForm (D.Y D.m) D.columnsY (D.lastEntry D.m)) (by
    rintro ψ ⟨smooth, equivariant⟩
    refine ⟨?_, fun γ g ↦ ?_⟩
    · -- the stabiliser contains the preimage under `borderU` of the open stabiliser of `ψ`
      have cont : Continuous D.borderU := by
        refine (U.isClosedEmbedding_coe isUnit_one).continuous_iff.2 (.matrix_reindex ?_ ..)
        -- each entry of `diag (g, 1)` is a constant or an entry of `g`
        simp [U.sum]
        fun_prop
      exact ((rightStabilizer ψ).comap D.borderU).isOpen_mono (fun _ hk ↦ by simp [hk _])
        (smooth.preimage cont)
    -- `branching` intertwines the action of `diag (γ, 1)` with that of `γ`
    simp [stdSpace_weightRep_apply]
    -- `erw`: the index types of `borderU` and of `stdSpace` agree only up to unfolding.
    erw [block_embFin, equivariant, stdSpace_weightRep_apply]
    rw [mulVec_mulVec, D.isBranchingMap_branching.mul_weylRep _ _ 1, Finset.prod_eq_one,
      one_smul] <;>
      simp [← ext_iff, GL.blockScalar])

end New.Data

end ColumnDefs

namespace New.Data

/-!
## Kernels of the lifts of source forms, translated data and combinations of chains

* `New.Data.liftKernel`: the kernel of lift j + 1, built from `New.thetaKernel`.
* `New.Data.Translations`, `New.Data.translateDatum`: tuples of translations, and the translated
  vacua they define.
* `New.Data.restrictedChain`: a combination of chains with such data, restricted to `Y_m`.
-/

section LiftKernelDefs

variable {P : Parameters} {D : Data P} (ϑ : D.TameChar) (j : ℕ)

/-- The column numbers `D.columnCount` and determinant exponents `D.lastEntry j` form a lift weight
(`IsLiftWeight`) from `X_j = D.X j` to `X_{j+1}` along the exponent ⌊n_{j+1} / 2⌋ - κ_{j+1}. That
is, n_j < n_{j+1}, and no column has a height strictly between n_j and n_{j+1}. Also,
`D.lastEntry j τ` is this exponent plus the number of columns of height n_j at `τ`. -/
lemma isLiftWeight_columnCount (j : ℕ) : IsLiftWeight (D.X j) (D.X (j + 1)) D.columnCount
    (fun τ : D.Φ ↦ (Fintype.card (D.X (j + 1)) / 2 : ℕ) - D.liftWeight (j + 1) τ)
      (D.lastEntry j) := by
  have h_rank : Fintype.card (D.X j) < Fintype.card (D.X (j + 1)) := by grind [card_X, n_succ]
  refine ⟨fun τ ↦ ⟨h_rank.le, fun u hu ↦ D.columnCount_eq_zero_of_mem_Ioo j τ ?_⟩, h_rank,
    funext fun τ ↦ ?_⟩
  · simpa only [rankAt, card_X] using hu
  · rw [lastEntry_eq, card_X, card_X, Int.natCast_ediv, Nat.cast_ofNat]

/-- The hermitian space Hom(X_j, X_{j+1}) of the standard definite spaces on the index sets X_j
and X_{j+1}. -/
abbrev homX : Space D.E (D.X (j + 1) × D.X j) (homSigns 1 1) :=
  (stdSpace D.E (D.X j)).hom (stdSpace D.E (D.X (j + 1)))

/-- The theta kernel of lift j + 1, for a character ϑ of U(1)(𝔸) of weight 0 with given tame part
(`New.Data.TameChar`). It goes from forms on X_j to forms on X_{j+1}, and its level on X_j is
`D.levelX j`. Its two characters are the twists `New.rankTwist`, by the ranks of X_j and X_{j+1}, of
`D.chainChar ϑ (j + 1)`, the product of `D.untwistedLiftChar (j + 1)` and ϑ^{j+1}. Derivatives are
scaled by π_M times the period `P.jetScale D.towerExp`, where π_M is the conjugate of the integer
`D.piMBar` of K of norm `D.M`. -/
@[simps! -isSimp ω]
def liftKernel :
    Kernel (D.X j) (D.X (j + 1)) D.columnCount (D.lastEntry j) (D.lastEntry (j + 1))
      (D.levelX j)
      (D.homX j).finitePart := by
  -- Both characters are twists of `chainChar ϑ (j + 1)`, whose weight is
  -- `-D.liftWeight (j + 1)`; the twist by the rank `n_j` raises this weight to `lastEntry (j + 1)`.
  obtain weight :
      (D.chainChar ϑ j.succ).HasWeight (-D.liftWeight j.succ ·)
        (D.liftTamePart (ϑ.pow j.succ) j.succ) :=
    D.hasWeight_liftChar
  exact thetaKernel (D.isLiftWeight_columnCount j) (star ↑D.piMBar * P.jetScale D.towerExp)
    (by
      convert weight.hasWeight_rankTwist (n := D.X j)
      grind [lastEntry, card_X])
    weight.hasWeight_rankTwist (D.levelX j)

/-- Tuples (x_j) of finite adelic matrices with rows X_{j+1} and columns X_j, the translations
that define the data of a chain. -/
abbrev Translations : Type := ∀ j : ℕ, D.X (j + 1) × D.X j → 𝔸f D.E

/-- The j-th datum of the tuple x: the normalised vacuum `New.Parameters.intVacuum` of Hom(X_j,
X_{j+1}) translated by the finite Heisenberg operator of x_j. -/
def translateDatum (x : D.Translations) (j : ℕ) : (D.homX j).finitePart :=
  (D.homX j).heisenbergFinPart (x j) ⟨P.intVacuum (homX j), SMulMemClass.smul_mem _ (by simp)⟩

/-- The linear map ∑_x Ψ(x)·C_x from algebraic forms of stage 0 to stage j, where C_x is the chain
(`New.chain`) of j theta lifts with data Φ x. -/
abbrev chainCombination (Ψ : D.Translations →₀ ℂ)
    (Φ : D.Translations → ∀ i : ℕ, (D.homX i).finitePart) (j : ℕ) : D.FormX 0 →ₗ[ℂ] D.FormX j :=
  Ψ.sum fun x c ↦ c • chain (D.liftKernel ϑ) (Φ x) j

/-- The combination `Ψ` of the chains of `m` lifts whose data are translates of the integral vacuum,
followed by the restriction to `Y_m`. The composite lift of a chain datum has this form, with `Ψ`
obtained by expanding its glued tensor (`IsChainDatum.exists_isWeakChainDatum_compositeLift_eq`). -/
def restrictedChain (Ψ : D.Translations →₀ ℂ) :
    D.SourceForm →ₗ[ℂ] AlgForm (E := D.E) (D.Y D.m) D.columnsY (D.lastEntry D.m) :=
  D.restrictToY ∘ₗ chainCombination ϑ Ψ D.translateDatum D.m ∘ₗ D.SourceForm.subtype

variable (D) in
/-- The number of lifts satisfies m = 2ϱ + 2, where ϱ = `New.Data.ϱ` is ⌊m/2⌋ − 1 truncated at
zero; so m is even and at least 2. -/
@[grind! .]
lemma m_eq_two_mul_varrho_add_two : D.m = 2 * D.ϱ + 2 := by grind [ϱ]

end LiftKernelDefs

/-!
## Chain data

A chain datum is a finitely supported function `Ψ` on tuples of translations, with conditions on
denominators, integrality and size, whose glued tensor `Glue φ♭` is jointly invariant. Here `φ♭` is
the combination `Ψ` of translates of the integral vacuum, and `Glue` applies to each double lift a
sum of translates with simple poles above `N` (`gluedDoubleLiftDatum`).
-/

section GoodDatumDefs

open Seesaw Space
open scoped TensorProduct

variable {P : Parameters} {D : Data P} (ϑ : D.Twist)

/-- The gluing for the double lift `X_{2i} → X_{2i+1} → X_{2i+2}`: the sum `doubleLiftGluing` of the
translates of `v (2 i) ⊗ v (2 i + 1)`, with simple poles at the places `w ∣ π` in the first factor
and at their conjugates in the second. -/
noncomputable def gluedDoubleLiftDatum (v : ∀ j : ℕ, (D.homX j).finitePart) (i : ℕ) :
    (D.homX (2 * i)).finitePart ⊗[ℂ] (D.homX (2 * i + 1)).finitePart :=
  doubleLiftGluing (D.InitIndex (2 * i)) (D.X (2 * i + 1)) D.piNPlaces D.N
    (D.InitIndex (2 * i + 1 + 1))
    (v (2 * i) ⊗ₜ v (2 * i + 1))

/-- The tuples of translations that become integral at all places prime to `q` after multiplication
by the conjugate of `D.piM`. -/
def admissibleTranslations (q : ℕ) : Set D.Translations :=
  {t : D.Translations | ∀ j : ℕ, t j ∈ translations (D.X (j + 1) × D.X j) q (star ↑D.piM)}

/-- Tensors of finite data for the chain `X_0 → ⋯ → X_m`, grouped by double lifts. -/
abbrev ChainTensor (D : Data P) : Type :=
  TensorChain (fun i : ℕ ↦ (D.homX (2 * i)).finitePart ⊗[ℂ] (D.homX (2 * i + 1)).finitePart)
    (D.ϱ + 1)

/-- A tensor is jointly invariant if the levels of `X_0, …, X_{m-1}` fix it under the Weil actions
for `ϑ`, with the identity on `X_m`. -/
def ChainTensor.IsInvariant (ϑ : D.TameChar) (w : D.ChainTensor) : Prop :=
  ∀ b : ∀ j : ℕ, D.levelX j, b (2 * D.ϱ + 2) = 1 →
    TensorChain.map (twoKernelAction (D.liftKernel ϑ) fun j : ℕ ↦ b j) (D.ϱ + 1) w = w

variable (D) in
/-- The tensor of the translates of the integral vacuum by `t`, glued in each double lift. -/
noncomputable def gluedVacuum (t : D.Translations) : D.ChainTensor :=
  TensorChain.pure (D.gluedDoubleLiftDatum (D.translateDatum t)) (D.ϱ + 1)

/-- The tensor `φ♭ = ∑ x, Ψ x • ⊗ⱼ translateDatum x j`. -/
noncomputable def plainTensor (Ψ : D.Translations →₀ ℂ) : D.ChainTensor :=
  Ψ.sum fun (x : D.Translations) (c : ℂ) ↦ c • TensorChain.pure
    (fun i : ℕ ↦ D.translateDatum x (2 * i) ⊗ₜ D.translateDatum x (2 * i + 1)) (D.ϱ + 1)

/-- The glued tensor `φ^ch = Glue φ♭`, with `Glue` applied to each term of `φ♭`. -/
noncomputable def gluedTensor (Ψ : D.Translations →₀ ℂ) : D.ChainTensor :=
  Ψ.sum fun (x : D.Translations) (c : ℂ) ↦ c • D.gluedVacuum x

/-- The tuples of translations that vanish at all places prime to `q`. -/
def supportedTranslations (q : ℕ) : Set D.Translations :=
  {t | ∀ (j : ℕ) (i : D.X (j + 1) × D.X j) (w : FinPlace D.E), ↑q ∉ w.asIdeal → t j i w = 0}

/-- `Ψ` is a chain datum for the twist `ϑ`, a character of weight 0 whose tame part is non-trivial
exactly at the places of the finite set `ϑ.Q`. Let `q` be the product of their norms and `M` the
principal level `D.M`. The translations in the support of `Ψ` vanish at the places prime to `M q`
and lie in `admissibleTranslations q`; the values of `Ψ` are integral away from `q`, with
denominator `1`; if `ϑ.Q` is empty, then `∑ x, |σ (Ψ x)| ≤ M ^ (3 f m n_m²)` for every automorphism
`σ` of `ℂ`; and the glued tensor is jointly invariant. -/
structure IsChainDatum (Ψ : D.Translations →₀ ℂ) : Prop extends IsAdmissibleCoeffs
    (D.admissibleTranslations ϑ.normQ ∩ D.supportedTranslations (D.M * ϑ.normQ))
    ϑ.normQ 1 (ϑ.Q = ∅) (D.M ^ (3 * D.f * D.m * D.n D.m ^ 2)) Ψ where
  /-- The glued tensor is jointly invariant. -/
  isInvariant : (gluedTensor Ψ).IsInvariant ϑ

/-- The translations in the support of a chain datum for `ϑ` are admissible for the norm of its
set `Q` of places: times the conjugate of `D.piM` they are integral away from that norm. -/
lemma IsChainDatum.mem_admissibleTranslations {ϑ : D.Twist} {Ψ : D.Translations →₀ ℂ}
    (hΨ : IsChainDatum ϑ Ψ) {x : D.Translations} (hx : x ∈ Ψ.support) :
    x ∈ D.admissibleTranslations ϑ.normQ :=
  Set.inter_subset_left (hΨ.support_subset x hx)

/-- The restriction map `restrictToY` on forms on `X_l`, for a number `l` equal to `m`. -/
noncomputable def restrictToYOfEq {l : ℕ} (hl : D.m = l) :
    D.FormX l →ₗ[ℂ] AlgForm (E := D.E) (D.Y D.m) D.columnsY (D.lastEntry D.m) := by
  subst hl
  exact D.restrictToY

/-- At `F l` with `l = m`, the map `restrictToYOfEq` takes the value `restrictToY (F m)`. -/
lemma restrictToYOfEq_apply {l : ℕ} (hl : D.m = l) (F : ∀ j : ℕ, D.FormX j) :
    restrictToYOfEq hl (F l) = D.restrictToY (F D.m) := by
  subst hl
  rfl

/-- The chain of double lifts of a form on `X_0`, as a linear function of the tensor of data. -/
noncomputable abbrev chainOfTensor (ϑ : D.TameChar) (φ : D.FormX 0) :
    D.ChainTensor →ₗ[ℂ] D.FormX (2 * D.ϱ + 2) :=
  TensorChain.lift (TensorChain.liftInPairs fun j : ℕ ↦ (D.liftKernel ϑ j).lift) φ (D.ϱ + 1)

/-- The composite lift: the chain of double lifts with the glued tensor of `Ψ` as data, followed by
the restriction of forms from `X_m` to `Y_m`. -/
noncomputable def compositeLift (ϑ : D.TameChar) (Ψ : D.Translations →₀ ℂ) (φ : D.SourceForm) :
    AlgForm (E := D.E) (D.Y D.m) D.columnsY (D.lastEntry D.m) :=
  restrictToYOfEq D.m_eq_two_mul_varrho_add_two (chainOfTensor ϑ φ (gluedTensor Ψ))

/-- A weak chain datum: the coefficients `Ψ` of a jointly invariant sum of translates of the
integral vacuum. The conditions are those of a chain datum, but there is no gluing, the translations
need not vanish anywhere and may have denominators above `N`, and the size is at most
`exp (D.x ^ 60)` if `ϑ.Q` is empty. For a chain datum, both `φ♭` and the expansion of `Glue φ♭` have
this form. -/
structure IsWeakChainDatum (Ψ : D.Translations →₀ ℂ) : Prop extends
    IsAdmissibleCoeffs (D.admissibleTranslations (ϑ.normQ * D.N)) ϑ.normQ 1 (ϑ.Q = ∅)
      (Real.exp (D.x ^ 60)) Ψ where
  /-- The tensor `∑ x, Ψ x • ⊗ⱼ translateDatum x j` is jointly invariant. -/
  isJointlyInvariant : IsJointlyInvariant (D.liftKernel ϑ) D.m Ψ.support
    (fun x : D.Translations ↦ Ψ x • .id) D.translateDatum

end GoodDatumDefs

end New.Data

end
