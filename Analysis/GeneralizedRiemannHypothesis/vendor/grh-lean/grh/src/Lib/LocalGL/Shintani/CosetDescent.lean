import Lib.Adelic.Unitary.ComponentsAndBlockSums
import Lib.LocalGL.Green.CuspidalFunctions
import Lib.LocalGL.Shintani.CosetRootChoice

/-!
# Descent of class functions along a coset and lifts from GL_n(k') ⋊ Gal(k'/k)

This file applies descent along a coset to `GL_n(k') ⋊ Gal(k'/k)` for an extension `k'/k` of finite
fields. Here functions on similarity classes of matrices (`New.Hall k`) are multiplied by parabolic
induction. It defines lifts of such functions from `k` to `k'` and proves that they are stable under
differences and products. It then shows that the eigenvalue sums `New.Hall.brauerLift k θ` have
virtual lifts.

## Main definitions and results

* `New.DescendsTo Φ X`: a function Φ on GL_n(k') ⋊ Gal(k'/k) (`New.GalSemidirect`) descends to X,
  that is, Φ(s) = X(s^{ord σ}) on the coset of each σ whose fixed field is the field of X.
* `New.Lift Z F F'`: in each rank, some `Z`-combination of characters of `GL_n(k') ⋊ Gal(k'/k)`
  descends to `F` over `k` and to `F'` over `k'`.
* `New.Lift.sub`, `New.Lift.mul`, `New.Lift.mulMoebius`,
  `New.Lift.rankPart_mulMoebius_mul_constOne`: lifts are stable under differences, under the
  product, and under pointwise multiplication by the inverse μ (`moebius`; `F.mulMoebius` is F·μ) of
  the constant function 1.
* `New.exists_torus_induced_descendsTo`: the character induced from (k' ⊗ L)ˣ ⋊ Gal(k'/k), for
  [L:k] = m, descends to C_θ·μ over k, where C_θ = `New.Hall.greenCuspidal` k θ.
* `New.exists_lift_brauerLift`: the eigenvalue sum `β_θ = New.Hall.brauerLift k θ` has a virtual
  lift. It is obtained from `New.exists_torus_induced_descendsTo` by recursion on the rank and
  `β_θ = −C_θ ∗ 𝟙`.

Notions from other files:
* `New.Hall.constOne`: The complex-valued function on classes of endomorphisms that takes the value
  1 on every class, in every dimension.
* `New.Hall.rankPart`: The function on similarity classes equal to F on classes of dimension n and
  zero on the others.
* `New.Hall.rankInner`: For complex functions F, H on similarity classes, the average over GL_n(k)
  of the conjugate of F times H.
* `New.IsRootChoice` (`Lib.LocalGL.Shintani.CosetRootChoice`): a conjugation-equivariant choice of
  `(ord σ)`-th roots over `σ`.
* `New.induceClassFn` (`Lib.LocalGL.Shintani.CosetRootChoice`): induction of class functions
  along `ρ` over `Γ`.

## Relation to the literature

Known; see `Lib.LocalGL.Shintani.LiftingGreenCharacters` and `Lib.LocalGL.Green.CuspidalFunctions`
for sources.
-/

namespace New

/-!
## Descent from GL_n(k') ⋊ Gal(k'/k) and lifts under products

`F.evalGL` is the restriction of a function `F` in `New.Hall k` to one `GL_n(k)`, and
`New.virtualChars Z G` is the `Z`-span of the characters of `G`. For levels `b : n → ι`,
`parabolic b` is the subgroup of block upper triangular matrices and `blockHom b i` takes the
diagonal block of level `i`.
-/

section CharacterLifts

open Finset Matrix GeneralLinearGroup Hall SemidirectProduct Function Fintype Submodule

variable (k k' Z : Type*)
  {k₀ R : Type*} [Field k] [Field k'] [Field k₀] [Algebra k k'] [Finite k] [Algebra k₀ k']
  [Finite k'] [Finite k₀] [CommSemiring Z] [Algebra Z ℂ] [CommRing R] [Algebra R ℂ]
  {F G : Hall k} {F' G' : Hall k'} {σ : Gal(k'/k)}
  (n : Type*) [Fintype n] [DecidableEq n]

/-- The action of Gal(k'/k) on GL_n(k') by group automorphisms, applying the field automorphism
to each matrix entry. -/
noncomputable def galActionGL : Gal(k'/k) →* MulAut (GL n k') :=
  MonoidHom.mk' (fun σ ↦ Units.mapEquiv σ.mapMatrix.toMulEquiv) (by tauto)

/-- The semidirect product GL_n(k') ⋊ Gal(k'/k), the Galois group acting on matrix entries. -/
abbrev GalSemidirect : Type _ := GL n k' ⋊[galActionGL k k' n] Gal(k'/k)

variable {k k' n} (Φ : GalSemidirect k k' n → ℂ) (X : Hall k₀)

variable (k₀) in
/-- The fixed field of σ ∈ Gal(k'/k) is k₀: the image of k₀ in k' is exactly the set of elements
fixed by σ. -/
abbrev HasFixedField (σ : Gal(k'/k)) : Prop := Set.range (algebraMap k₀ k') = fixedPoints σ

/-- For each σ ∈ Gal(k'/k) with fixed field k₀ and each s over σ in GL_n(k')⋊Gal(k'/k) whose
power s^{ord σ} is γ ∈ GL_n(k₀), Φ(s) = X(γ). -/
def DescendsTo : Prop :=
  ∀ σ : Gal(k'/k), HasFixedField k₀ σ →
    DescendsOnCoset rightHom σ (fun γ : GL n k₀ ↦ inl (γ.map (algebraMap k₀ k'))) Φ X.evalGL

variable (F F' n)

/-- Some Z-combination Φ of characters of GL_n(k') ⋊ Gal(k'/k) descends, in the sense of
`New.DescendsTo`, both to F over k and to F' over k'. -/
def HasCommonLift : Prop :=
  ∃ Φ ∈ virtualChars Z (GalSemidirect k k' n), DescendsTo Φ F ∧ DescendsTo Φ F'

/-- F lifts to F' over Z: for every m, one Z-combination Φ of characters of GL_m(k')⋊Gal(k'/k)
satisfies `New.DescendsTo` for both F (over k) and F' (over k'). -/
def Lift : Prop := ∀ m : ℕ, HasCommonLift Z F F' (Fin m)

end CharacterLifts

section CharacterLifts

open Finset Matrix GeneralLinearGroup Hall SemidirectProduct Function Fintype Submodule

variable {k k' Z : Type*} {k₀ R : Type*} [Field k] [Field k'] [Field k₀] [Algebra k k']
  [Algebra k₀ k'] [Finite k₀] [CommSemiring Z] [Algebra Z ℂ] [CommRing R] [Algebra R ℂ]
  {F G : Hall k} {F' G' : Hall k'} {σ : Gal(k'/k)} {n : Type*} [Fintype n] [DecidableEq n]
  {Φ : GalSemidirect k k' n → ℂ} (X : Hall k₀)

/-- Renumbering the rows and columns along `e` commutes with the action of `τ` on the entries. -/
private lemma reindexGL_comp_galActionGL {n' : Type*} [Fintype n'] [DecidableEq n'] (e : n ≃ n')
    (τ : Gal(k'/k)) :
    (reindexGL e).toMonoidHom.comp (galActionGL k k' n τ).toMonoidHom =
      (galActionGL k k' n' (MonoidHom.id Gal(k'/k) τ)).toMonoidHom.comp (reindexGL e).toMonoidHom :=
  rfl

omit [Finite k₀] in
/-- Renumbering the rows and columns along `e` keeps the relation `DescendsTo` with `X`. -/
lemma descendsTo_comp_reindexGL {n' : Type*} [Fintype n'] [DecidableEq n'] (e : n ≃ n')
    {Ψ : GalSemidirect k k' n' → ℂ} {X : Hall k₀} (hΨ : DescendsTo Ψ X) :
    DescendsTo
    (Ψ ∘ SemidirectProduct.map (reindexGL e).toMonoidHom (MonoidHom.id Gal(k'/k))
      (reindexGL_comp_galActionGL e))
      X := by
  intro σ hσ s γ hs hγ
  set ρ : GalSemidirect k k' n →* GalSemidirect k k' n' :=
    map (reindexGL e).toMonoidHom (.id _) (reindexGL_comp_galActionGL e)
  -- `ρ s` is a root of the renumbered `γ`, which is similar to `γ`.
  have h_pow : ρ s ^ orderOf σ = inl ((reindexGL e γ).map (algebraMap k₀ k')) := by
    rw [← map_pow, hγ]
    -- `ρ` renumbers the matrix part, which commutes with applying `algebraMap k₀ k'` to the entries
    rfl
  calc Ψ (ρ s) = X.evalGL (reindexGL e γ) := hΨ σ hσ (ρ s) (reindexGL e γ) hs h_pow
    _ = X.evalGL γ := by
      show X (simClassOf (γ.val.submatrix e.symm e.symm).toLin') = X (simClassOf γ.val.toLin')
      rw [simClassOf_submatrix]

/-- If (F, F') is a lift with coefficients in Z, then for every finite index set n some
Z-combination of characters of GL_n(k')⋊Gal(k'/k) descends (`New.DescendsTo`) to F over k and to F'
over k'. -/
lemma Lift.hasCommonLift [Finite k'] (h : Lift Z F F') (n : Type*) [Fintype n] [DecidableEq n] :
    HasCommonLift Z F F' n := by
  -- Take the lift in rank `card n` and renumber `n` as `Fin (card n)`.
  obtain ⟨Φ, hΦ, hF, hF'⟩ := h (card n)
  exact ⟨_, comp_mem_virtualChars hΦ _, descendsTo_comp_reindexGL (equivFin n) hF,
    descendsTo_comp_reindexGL (equivFin n) hF'⟩

/-- The restriction `F.evalGL` of a function on similarity classes to `GL n k` is a class
function. -/
lemma isClassFunction_evalGL : IsClassFunction (F.evalGL (n := n)) := by
  intro g x
  -- Multiplication by `x` intertwines `g` with `x * g * x⁻¹`.
  have h_sim : simClassOf g.val.toLin' = simClassOf (x * g * x⁻¹).val.toLin' :=
    simClassOf_eq_of_equiv x.toLin.toLinearEquiv fun v ↦ by simp
  exact congrArg F h_sim.symm

private lemma evalGL_sub (X Y : Hall k₀) (γ : GL n k₀) :
    (X - Y).evalGL γ = X.evalGL γ - Y.evalGL γ := rfl

private lemma evalGL_mulMoebius (X : Hall k₀) (γ : GL n k₀) :
    X.mulMoebius.evalGL γ = X.evalGL γ * moebius.evalGL γ := rfl

omit [Finite k₀] in
/-- If `Φ` descends to `X` (`New.DescendsTo`) and `Y` takes the same values as `X` on
`GL n k₀`, then `Φ` descends to `Y`. -/
private lemma DescendsTo.of_evalGL_eq {X Y : Hall k₀} (h_desc : DescendsTo Φ X)
    (h_eq : ∀ γ : GL n k₀, X.evalGL γ = Y.evalGL γ) : DescendsTo Φ Y :=
  fun σ hσ s γ hs hγ ↦ (h_desc σ hσ s γ hs hγ).trans (h_eq γ)

/-- On `GL_m(k₀)`, the function `moebius + (1 - constOne) ^ (m + 1) * -moebius` agrees with
`moebius`: its second term vanishes on classes of dimension at most `m`. -/
private lemma evalGL_moebius_add_one_sub_constOne_pow_mul {m : ℕ} (γ : GL (Fin m) k₀) :
    (moebius + (1 - constOne) ^ (m + 1) * -moebius : Hall k₀).evalGL γ =
      (moebius : Hall k₀).evalGL γ := by
  have h_zero : ((1 - constOne) ^ (m + 1) * -moebius : Hall k₀) (simClassOf γ.val.toLin') = 0 :=
    mul_apply_eq_zero_of_dim_lt (n := 0) (one_sub_constOne_pow_apply_eq_zero (m + 1)) (by simp) _
      (by simp [dim_simClassOf])
  rw [evalGL, evalGL, Hall.add_apply, h_zero, add_zero]

/-- One step `J ↦ J - (constOne * J - 1)` of the iteration that approaches `moebius` takes
`moebius + (1 - constOne) ^ N * -moebius` to the same expression with exponent `N + 1`. -/
private lemma moebius_add_one_sub_constOne_pow_succ_mul (N : ℕ) :
    (moebius + (1 - constOne) ^ (N + 1) * -moebius : Hall k₀) =
      (moebius + (1 - constOne) ^ N * -moebius) -
        (constOne * (moebius + (1 - constOne) ^ N * -moebius) - 1) := by
  grind [isUnit_constOne]

/-! ### First properties and examples of lifts -/

/-- Let σ have fixed field k₀. Then the matrices γ in GL_n(k₀) have (a) a natural choice of
(ord σ)-th roots r(γ) over σ in GL_n(k') ⋊ Gal(k'/k) (`New.IsRootChoice`) such that (b) the matrix
part of r(γ) lies in every k'-subalgebra of matrices that contains the image of γ. -/
lemma exists_isRootChoice_GL [Finite k'] (hσ : HasFixedField k₀ σ) :
    ∃ r : GL n k₀ → GalSemidirect k k' n,
      -- (a) `r` is a natural choice of roots in the coset of `σ`
      IsRootChoice rightHom σ (inl.comp (GeneralLinearGroup.map (algebraMap k₀ k'))) r ∧
      -- (b) the matrix part of `r γ` lies in every subalgebra that contains `γ`
      ∀ (B : Subalgebra k' (Matrix n n k')) (γ : GL n k₀),
        (γ.map (algebraMap k₀ k')).val ∈ B → (r γ).left.val ∈ B := by
  let j : GL n k₀ →* GL n k' := map (algebraMap k₀ k')
  -- A matrix over `k'` is fixed by `σ` exactly when its entries lie in `k₀`.
  have h_fixed (u : GL n k') : u ∈ j.range ↔ galActionGL k k' n σ u = u := by
    refine ⟨?_, exists_gl_map_eq_of_fixed (σ := σ.toRingHom) (RingHom.injective _) hσ.ge⟩
    rintro ⟨g, rfl⟩
    ext
    exact hσ.le ⟨_, rfl⟩
  -- `σ` acts on `GL n k'` through the ring map that applies `σ` to each entry.
  have h_act (u : GL n k') :
      (galActionGL k k' n σ u : Matrix n n k') = RingHom.mapMatrix (σ : k' →+* k') u := rfl
  have h_semiconj :
      Semiconj (algebraMap k' (Matrix n n k')) σ (RingHom.mapMatrix (σ : k' →+* k')) := by
    simp [algebraMap, Semiconj]
  exact exists_isRootChoice _ h_act h_semiconj
    (by simp [Injective, GeneralLinearGroup.ext_iff]) h_fixed

/-- Φ descends to a class function F' over k' itself exactly when F' is the restriction of Φ to
GL_n(k'). -/
@[simp]
lemma DescendsTo.iff_comp_inl_eq_evalGL :
    DescendsTo Φ F' ↔ (fun g : GL n k' ↦ Φ (inl g)) = F'.evalGL := by
  constructor
  · -- The fixed field of `σ = 1` is `k'`, and `inl g` is its own root over `1`.
    intro h_desc
    funext g
    have h_fix : HasFixedField k' (1 : Gal(k'/k)) := by
      ext x
      simp [Function.IsFixedPt]
    exact h_desc 1 h_fix (inl g) g (by simp) (by simp)
  · -- The only automorphism whose fixed field is `k'` is `σ = 1`, of order one, so
    -- `s ^ orderOf σ = inl γ` says that `s` is `inl γ`.
    intro h_eq σ hσ s γ hs hγ
    obtain rfl : σ = 1 := σ.ext fun x ↦ hσ.le ⟨x, rfl⟩
    have hs_eq : s = inl (γ.map (algebraMap k' k')) := by simpa using hγ
    simp [hs_eq, ← h_eq]

/-- If in every rank some Z-combination of characters descends to F, then F lifts to some class
function G over k'. -/
lemma Lift.exists_lift_of_descendsTo [Finite k']
    (h : ∀ m : ℕ, ∃ Φ ∈ virtualChars Z (GalSemidirect k k' (Fin m)), DescendsTo Φ F) :
    ∃ G : Hall k', Lift Z F G := by
  choose Φ h_virt h_desc using h
  -- The restriction of `Φ m` to `GL m k'` is a class function, so it comes from some `X m`.
  have h_exists (m : ℕ) : ∃ X : Hall k', (fun g : GL (Fin m) k' ↦ Φ m (inl g)) = X.evalGL :=
    exists_eq_evalGL (isClassFunction_of_mem_virtualChars (comp_mem_virtualChars (h_virt m) inl))
  choose X hX using h_exists
  -- Use `X m` on the classes of dimension `m`.
  refine ⟨fun c ↦ X c.dim c, fun m ↦ ⟨Φ m, h_virt m, h_desc m, ?_⟩⟩
  rw [DescendsTo.iff_comp_inl_eq_evalGL, hX m]
  funext g
  simp [evalGL, dim_simClassOf]

/-- Suppose Gal(k'/k) is trivial, F' on GL_n(k') is a Z-combination of characters, and F' agrees
with F on GL_n(k). Then some Z-combination of characters of GL_n(k') ⋊ Gal(k'/k) descends
(`New.DescendsTo`) to both F and F'. -/
lemma hasCommonLift_of_gal_trivial [Finite k'] (h_triv : ∀ σ : Gal(k'/k), σ = 1)
    (h : F'.evalGL ∈ virtualChars Z (GL n k'))
    (h_ev : ∀ g : GL n k, F'.evalGL (g.map (algebraMap k k')) = F.evalGL g) :
    HasCommonLift Z F F' n := by
  -- With trivial Galois group, `left` is a homomorphism; pull `F'.evalGL` back along it.
  have h_left_mul (a b : GalSemidirect k k' n) : (a * b).left = a.left * b.left := by
    rw [mul_left, h_triv a.right, map_one, MulAut.one_apply]
  let π : GalSemidirect k k' n →* GL n k' := .mk' left h_left_mul
  -- The only `σ` is `1`, of order one, so `s ^ orderOf σ = inl γ` says that `s` is `inl` of the
  -- image of `γ`, and `π s` is that image; `h_ev` gives the value over `k`.
  have h_desc_k : DescendsTo (F'.evalGL ∘ π) F := by simp_all [π, DescendsTo, DescendsOnCoset]
  have h_desc_k' : DescendsTo (F'.evalGL ∘ π) F' := by simp_all [π, DescendsTo, DescendsOnCoset]
  exact ⟨F'.evalGL ∘ π, comp_mem_virtualChars h π, h_desc_k, h_desc_k'⟩

/-- If one Z-combination Φ of characters of GL_m(k')⋊Gal(k'/k) descends (`New.DescendsTo`) to F over
k and to F' over k', then the dimension m parts of F and F' form a lift over Z in all ranks. -/
lemma Lift.rankPart_of_hasCommonLift {m : ℕ} (h : HasCommonLift Z F F' (Fin m)) :
    Lift Z (rankPart m F) (rankPart m F') := by
  intro n
  obtain rfl | hn := eq_or_ne n m
  · -- In dimension `n` the two parts are `F` and `F'` themselves.
    simpa [HasCommonLift, DescendsTo, DescendsOnCoset, evalGL]
  · -- Both parts vanish in dimension `n`, and so does the zero function.
    refine ⟨0, zero_mem _, ?_, ?_⟩ <;> simp [hn, DescendsTo, DescendsOnCoset, evalGL]

/-- The constant function 1 lifts to itself, through the trivial character. -/
lemma Lift.lift_constOne : Lift Z (constOne : Hall k) (constOne : Hall k') := by
  intro m
  -- The trivial character takes the value `1` everywhere.
  refine ⟨1, one_mem _, ?_, ?_⟩ <;> simp [DescendsTo, DescendsOnCoset, evalGL]

/-- The unit of the product, the dimension 0 part of the constant function, lifts to itself. -/
@[simp]
lemma Lift.one : Lift (k := k) (k' := k') Z 1 1 := rankPart_of_hasCommonLift (lift_constOne 0)

variable [Finite k] [Finite k']

/-- If `F` lifts to `G` with coefficients in `Z` (`New.Lift`, here with both functions over
`k`, so along the trivial extension `k/k`), then the restriction of `F` to `GL_n(k)` is a
`Z`-combination of characters of `GL_n(k)`. -/
lemma Lift.evalGL_mem_virtualChars (h : Lift Z F G) : F.evalGL ∈ virtualChars Z (GL n k) := by
  obtain ⟨Φ, hΦ, hF, -⟩ := h.hasCommonLift n
  -- The restriction of `Φ` to `GL n k` is `F.evalGL`.
  rw [← DescendsTo.iff_comp_inl_eq_evalGL.mp hF]
  exact comp_mem_virtualChars hΦ inl

/-- If F lifts to F' and G lifts to G' with coefficients in a commutative ring R (`New.Lift`), then
F - G lifts to F' - G'. -/
lemma Lift.sub (h : Lift R F F') (h' : Lift R G G') : Lift R (F - G) (F' - G') := by
  intro m
  obtain ⟨Φ, hΦ, hΦ_F, hΦ_F'⟩ := h m
  obtain ⟨Ψ, hΨ, hΨ_G, hΨ_G'⟩ := h' m
  -- On the coset of each `σ` with fixed field `k`, `Φ - Ψ` takes the value `F γ - G γ`; where the
  -- fixed field is `k'`, it takes the value of `F' - G'`.
  refine ⟨Φ - Ψ, sub_mem hΦ hΨ, fun σ hσ s γ hs hγ ↦ ?_, fun σ hσ s γ hs hγ ↦ ?_⟩
  · rw [Pi.sub_apply, hΦ_F σ hσ s γ hs hγ, hΨ_G σ hσ s γ hs hγ, evalGL_sub]
  · rw [Pi.sub_apply, hΦ_F' σ hσ s γ hs hγ, hΨ_G' σ hσ s γ hs hγ, evalGL_sub]

omit [Finite k] in
/-- Let `b` split the indices `n` into ordered blocks. Let `P` be the subgroup of
`GL_n(k') ⋊ Gal(k'/k)` whose matrix part is block upper triangular for `b`, and let `β i` send an
element of `P` to its `i`-th diagonal block together with its Galois part. If each `Ψ i` is a
`Z`-combination of characters of its block's group that descends to `Y i` (its value at `s` over `σ`
with fixed field `k₀` is `Y i` at `s ^ orderOf σ`), then the function induced along `P`
(`induceClassFn`; it conjugates only by matrices, since `rightHom` is the Galois part) from the
product of the `Ψ i ∘ β i` descends to the induction product of the `Y i`, each `Y i` taken in the
dimension of its block. -/
lemma DescendsTo.induceClassFn_parabolic {ι : Type*} [Fintype ι] [LinearOrder ι] {b : n → ι}
    {P : Subgroup (GalSemidirect k k' n)}
    (hP : ∀ s : GalSemidirect k k' n, s ∈ P ↔ s.left ∈ parabolic b)
    (β : ∀ i : ι, P →* GalSemidirect k k' {j // b j = i})
    (hβ : ∀ (i : ι) (s : P),
      β i s = ⟨blockHom b i ⟨(s : GalSemidirect k k' n).left, (hP s).mp s.property⟩,
        (s : GalSemidirect k k' n).right⟩)
    {Ψ : ∀ i : ι, GalSemidirect k k' {j // b j = i} → ℂ}
    (hΨ : ∀ i : ι, Ψ i ∈ virtualChars Z (GalSemidirect k k' {j // b j = i})) {Y : ι → Hall k₀}
    (hY : ∀ i : ι, DescendsTo (Ψ i) (Y i)) :
    DescendsTo (induceClassFn rightHom P.subtype (∏ i : ι, Ψ i ∘ β i))
      (∏ i : ι, (Y i).rankPart (Nat.card {j // b j = i})) := by
  intro σ hσ
  simp only [Nat.card_eq_fintype_card]
  obtain ⟨r, hr, hr_sub⟩ := exists_isRootChoice_GL (n := n) hσ
  -- Block triangular matrices form a subalgebra, so the roots of elements of the parabolic
  -- subgroup lie in `P`, and `r` restricts to a choice of roots for the two subgroups.
  have hr_mem : ∀ γ ∈ parabolic b, r γ ∈ P := fun γ hγ ↦ (hP _).mpr
    (hr_sub (blockTriangularSubalgebra k' k' b) γ (mem_blockTriangularSubalgebra.mpr (.map _ hγ)))
  -- The preimage of `P` in `GL n k₀` is the parabolic subgroup.
  have h_comap :
      Subgroup.comap (MonoidHom.comp inl (GeneralLinearGroup.map (algebraMap k₀ k'))) P =
        parabolic b := by
    simp [Subgroup.ext_iff, hP, parabolic, BlockTriangular]
  have h_class : IsClassFunction (∏ i : ι, Ψ i ∘ β i) :=
    isClassFunction_of_mem_virtualChars (prod_mem fun i _ ↦ comp_mem_virtualChars (hΨ i) _)
  -- Descent commutes with induction (`DescendsOnCoset.induce`), and the product of the `Y i` is
  -- induced from the parabolic subgroup (`classInner_evalGL_prod`). This reduces the claim to `P`,
  -- where it holds block by block.
  refine DescendsOnCoset.induce hr h_class (fun γ : parabolic (R := k₀) b ↦ (γ : GL n k₀))
    (fun _ ↦ rfl) (hr.restrict_subgroup P h_comap hr_mem) (fun s γ hs hpow ↦ ?_)
      isClassFunction_evalGL
    (classInner_evalGL_prod b Y fun j ↦ mem_univ (b j))
  simp only [Finset.prod_apply]
  refine prod_congr rfl fun i _ ↦ ?_
  have h_pow : β i s ^ orderOf σ = inl ((blockHom b i γ).map (algebraMap k₀ k')) := by
    rw [← map_pow, hpow, hβ]
    -- the diagonal block of the image of `γ` is the image of the diagonal block of `γ`
    rfl
  exact hY i σ hσ (β i s) (blockHom b i γ) (by simpa [hβ] using hs) h_pow

/-- The value of the product `F * G` at `γ` in `GL_m(k)`, sorted by the dimension `a` of the stable
subspace: it is the sum over `a ≤ m` of the value at `γ` of the product of the part of `F` of
dimension `#{j < a} = a` and the part of `G` of dimension `#{j ≥ a} = m - a`. -/
lemma sum_evalGL_prod_rankPart {m : ℕ} (γ : GL (Fin m) k) :
    ∑ a ∈ Iic m,
        (∏ i : Bool, rankPart (Nat.card {j : Fin m // decide (j.val < a) = i}) (cond i F G)).evalGL
          γ =
      (F * G).evalGL γ := by
  -- Expand both products over the stable subspaces `W` and exchange the sums: only `a = dim W`
  -- contributes, and then the quotient has dimension `m - a`.
  -- (`mul_ite` and `not_lt` are erased: without that this simp runs out of steps)
  simp +contextual [mul_simClassOf, -not_lt, -mul_ite, -Nat.not_lt, sum_comm,
    card_fin_lt_of_le ∘ mem_Iic.mp, finrank_quotient, (finrank_le _).trans, evalGL,
    finsum_eq_sum_of_fintype]

/-- `F` lifts to `F'` over `Z` (`New.Lift`) when, for every `m`, one `Z`-combination of characters
of `GL_m(k') ⋊ Gal(k'/k)` descends (`New.DescendsTo`) both to `F` over `k` and to `F'` over `k'`.
Lifting is multiplicative: if `F` lifts to `F'` and `G` lifts to `G'` over `Z`, then the
parabolic-induction product `F * G` lifts to `F' * G'`. -/
lemma Lift.mul (h : Lift Z F F') (h' : Lift Z G G') : Lift Z (F * G) (F' * G') := by
  -- For each `a ≤ m` split `Fin m` into blocks of sizes `a` and `m - a`, pull the characters of the
  -- two lifts back along the blocks, induce from the parabolic subgroup, and sum over `a`.
  intro m
  let b (a : ℕ) (j : Fin m) : Bool := decide (j.val < a)
  have hblock : ∀ i : Bool, Lift Z (cond i F G) (cond i F' G') := Bool.forall_bool.mpr ⟨h', h⟩
  have h_lifts (a : ℕ) (i : Bool) :
      HasCommonLift Z (cond i F G) (cond i F' G') {j // b a j = i} :=
    (hblock i).hasCommonLift _
  choose Φ hΦ hΦ_k hΦ_k' using h_lifts
  -- `P a`: the elements whose matrix part is block upper triangular for the levels `b a`.
  let P (a : ℕ) : Subgroup (GalSemidirect k k' (Fin m)) :=
    { carrier := {s | s.left ∈ parabolic (b a)}
      mul_mem' := fun {x _} hx hy ↦ hx.mul (hy.map x.right)
      one_mem' := by simp
      inv_mem' := fun {x} hx ↦ .map x.right⁻¹ ((parabolic _).inv_mem hx) }
  -- `β a i`: the diagonal block of level `i`, with the same Galois part.
  let β (a : ℕ) (i : Bool) : P a →* GalSemidirect k k' {j // b a j = i} :=
    .mk' (fun s ↦ ⟨blockHom (b a) i ⟨(s : GalSemidirect k k' (Fin m)).left, s.property⟩,
        (s : GalSemidirect k k' (Fin m)).right⟩) fun x y ↦ by
      refine SemidirectProduct.ext ?_ rfl
      -- Taking a diagonal block is multiplicative and commutes with the Galois action on entries.
      exact (blockHom (b a) i).map_mul ⟨(x : GalSemidirect k k' (Fin m)).left, x.property⟩
        ⟨galActionGL k k' _ (x : GalSemidirect k k' (Fin m)).right
            (y : GalSemidirect k k' (Fin m)).left,
          y.property.map (x : GalSemidirect k k' (Fin m)).right⟩
  -- `P a` meets the coset of `GL_m(k')` over each `σ` in the Galois group, in `inr σ`.
  have h_surj (a : ℕ) : Surjective (rightHom.comp (P a).subtype) :=
    fun σ ↦ ⟨⟨inr σ, blockTriangular_one⟩, rfl⟩
  have h_virt (a : ℕ) :
      induceClassFn rightHom (P a).subtype (∏ i, Φ a i ∘ β a i) ∈
        virtualChars Z (GalSemidirect k k' (Fin m)) :=
    induceClassFn_mem_virtualChars (h_surj a)
      (prod_mem fun i _ ↦ comp_mem_virtualChars (hΦ a i) _)
  refine ⟨∑ a ∈ Iic m, induceClassFn rightHom (P a).subtype (∏ i, Φ a i ∘ β a i),
    sum_mem fun a _ ↦ h_virt a, fun σ hσ s γ hs hpow ↦ ?_, fun σ hσ s γ hs hpow ↦ ?_⟩
  -- Over `k` and over `k'` alike, `sum_evalGL_prod_rankPart` splits the product by `a`, and each
  -- term is `DescendsTo.induceClassFn_parabolic` for the blocks of `b a`.
  all_goals
    rw [Finset.sum_apply, ← sum_evalGL_prod_rankPart]
    refine sum_congr rfl fun a _ ↦
      DescendsTo.induceClassFn_parabolic (fun _ ↦ .rfl) (β a) (fun _ _ ↦ rfl) (hΦ a) ?_ σ hσ s γ hs
        hpow
  exacts [hΦ_k a, hΦ_k' a]

/-! ### The inverse of the constant function, and characters of degree one -/

/-- If F lifts to F' with coefficients in a commutative ring R, then F·μ lifts to F'·μ. Here μ is
the inverse of the constant function 1 for the parabolic-induction product. -/
lemma Lift.mulMoebius (h : Lift R F F') : Lift R F.mulMoebius F'.mulMoebius := by
  -- Iterating `J ↦ J - (constOne * J - 1)` from `J = 0` gives these lifts.
  have hJ (N : ℕ) :
      Lift (k := k) (k' := k') R (moebius + (1 - constOne) ^ N * -moebius)
        (moebius + (1 - constOne) ^ N * -moebius) := by
    induction N with
    | zero => simpa using one.sub one
    | succ N ih =>
      rw [moebius_add_one_sub_constOne_pow_succ_mul, moebius_add_one_sub_constOne_pow_succ_mul]
      exact ih.sub ((lift_constOne.mul ih).sub one)
  -- The `N`-th one agrees with `moebius` in dimension less than `N`, where `(1 - constOne) ^ N`
  -- vanishes.
  have hμ : Lift (k := k) (k' := k') R moebius moebius := by
    intro m
    obtain ⟨Φ, hΦ, hΦ_k, hΦ_k'⟩ := hJ (m + 1) m
    exact ⟨Φ, hΦ, hΦ_k.of_evalGL_eq evalGL_moebius_add_one_sub_constOne_pow_mul,
      hΦ_k'.of_evalGL_eq evalGL_moebius_add_one_sub_constOne_pow_mul⟩
  -- `F.mulMoebius` is the pointwise product of `F` and `moebius`, so `Φ * Ψ` takes the value
  -- `F γ * moebius γ` on the coset of each `σ`.
  intro m
  obtain ⟨Φ, hΦ, hΦ_F, hΦ_F'⟩ := h m
  obtain ⟨Ψ, hΨ, hΨ_k, hΨ_k'⟩ := hμ m
  refine ⟨Φ * Ψ, mul_mem hΦ hΨ, fun σ hσ s γ hs hγ ↦ ?_, fun σ hσ s γ hs hγ ↦ ?_⟩
  · rw [Pi.mul_apply, hΦ_F σ hσ s γ hs hγ, hΨ_k σ hσ s γ hs hγ, evalGL_mulMoebius]
  · rw [Pi.mul_apply, hΦ_F' σ hσ s γ hs hγ, hΨ_k' σ hσ s γ hs hγ, evalGL_mulMoebius]

/-- If F lifts to F', then (−1)^m times the dimension m part of `F.mulMoebius * constOne` lifts to
the same expression for F'. Here `F.mulMoebius` is the pointwise product F·μ, with μ the inverse of
`constOne`. -/
lemma Lift.rankPart_mulMoebius_mul_constOne {m : ℕ} (h : Lift R F F') :
    Lift R ((-1 : ℂ) ^ m • rankPart m (F.mulMoebius * constOne))
      ((-1 : ℂ) ^ m • rankPart m (F'.mulMoebius * constOne)) := by
  have h_part : Lift R (rankPart m (F.mulMoebius * constOne))
      (rankPart m (F'.mulMoebius * constOne)) :=
    rankPart_of_hasCommonLift (h.mulMoebius.mul lift_constOne m)
  -- Lifts are closed under negation, since `-X = X - X - X`.
  obtain h_even | h_odd := m.even_or_odd
  · simpa [h_even] using h_part
  · simpa [h_odd] using (h_part.sub h_part).sub h_part

omit [Finite k] in
/-- Let S be a finite monoid, α an action of Gal(k'/k) on its unit group Sˣ, and ν : S → ℂ a monoid
homomorphism. Then there is a function ϑ on Sˣ ⋊ Gal(k'/k) such that (a) ϑ is a character, (b)
ϑ(s) = ∏_τ ν(α(τ) s₁), with s₁ the component of s in Sˣ, and (c) for σ with fixed field k,
ϑ(s) = ν(γ) whenever s lies over σ and s^{ord σ} = γ. -/
lemma exists_norm_char_semidirect {S : Type*} [Monoid S] [Finite S] (α : Gal(k'/k) →* MulAut Sˣ)
    (ν : S →* ℂ) :
    ∃ ϑ : Sˣ ⋊[α] Gal(k'/k) → ℂ,
      -- (a) `ϑ` is a character
      IsChar ϑ ∧
      -- (b) its value is the product of `ν` over the Galois conjugates
      (∀ s : Sˣ ⋊[α] Gal(k'/k), ϑ s = ∏ τ : Gal(k'/k), ν (α τ s.left)) ∧
      -- (c) on the cosets of the `σ` with fixed field `k` it is `ν` of the norm
      ∀ σ : Gal(k'/k), HasFixedField k σ →
        DescendsOnCoset rightHom σ inl ϑ fun u : Sˣ ↦ ν u.val := by
  classical
  -- `ϑ s = ∏ τ, ν (α τ s.left)` is multiplicative: in `(a * b).left = a.left * α a.right b.left`
  -- the twist by `a.right` only permutes the factors.
  let ϑ : Sˣ ⋊[α] Gal(k'/k) →* ℂ :=
    { toFun s := ∏ τ, ν (α τ s.left)
      map_one' := by simp
      map_mul' a b := by
        simp [← Equiv.prod_comp (.mulRight a.right) fun τ ↦ ν (α τ b.left), prod_mul_distrib] }
  refine ⟨ϑ, isChar_monoidHom ϑ, fun _ ↦ rfl, fun σ hσ s γ hs hγ ↦ ?_⟩
  -- The fixed field of `σ` is `k`, so `σ` generates the Galois group.
  have h_gen (τ : Gal(k'/k)) : τ ∈ Subgroup.zpowers σ := by
    refine (IntermediateField.fixingSubgroup_fixedField (.zpowers σ)).le fun x ↦ ?_
    obtain ⟨y, hy⟩ : (x : k') ∈ Set.range (algebraMap k k') :=
      hσ.ge (x.property ⟨σ, Subgroup.mem_zpowers σ⟩)
    simp [← hy]
  -- The first component of `s ^ i` is the product of the `α (σ ^ l) s.left`, `l < i`, in order.
  have h_pow (i : ℕ) : ∏ l ∈ range i, ν ((α σ ^ l) s.left) = ν (s ^ i).left := by
    subst hs
    induction i with
    | zero => simp
    | succ i ih =>
      -- the Galois part of `s ^ i` is the `i`-th power of that of `s`
      have h_right : (s ^ i).right = s.right ^ i := map_pow rightHom s i
      simp_all [pow_succ, prod_range_succ, ← map_pow]
  -- As `σ` generates the Galois group, `l ↦ σ ^ l` maps `range (orderOf σ)` bijectively onto it.
  calc ϑ s = ∏ τ : Gal(k'/k), ν (α τ s.left) := rfl
    _ = ∏ l ∈ range (orderOf σ), ν ((α σ ^ l) s.left) := by
      simp [← IsCyclic.image_range_orderOf h_gen, prod_image, pow_injOn_Iio_orderOf]
    _ = ν (s ^ orderOf σ).left := h_pow _
    _ = ν γ := by rw [hγ, left_inl]

end CharacterLifts

/-!
## Green's theorem with Galois action for Brauer functions

Let `k'/k` be an extension of finite fields and `θ` a multiplicative character of an algebraically
closed field `K` over `k'`.
-/

section GreenLift

open Module Hall ComplexConjugate SemidirectProduct Algebra TensorProduct LinearMap FiniteField

attribute [local instance low] Fintype.ofFinite

variable (k k' : Type*) {K L : Type*}
  {m : ℕ} [Field k] [Field k'] [Algebra k k'] [Finite k'] [Field K] [IsAlgClosed K]
  [Algebra k K] [Algebra k' K] [IsScalarTower k k' K]
  (θ : MulChar K ℂ) [Field L] [Finite L] [Algebra k L]

/-- For a basis `b` of a finite `k`-algebra `A` and an element `t` of `A`, the matrix of left
multiplication by `t` in the basis `b` and left multiplication by `t` on `A` have the same
similarity class. -/
lemma simClassOf_leftMulMatrix {A : Type*} [Ring A] [Algebra k A] [Finite A] (b : Basis (Fin m) k A)
    (t : A) :
    simClassOf (leftMulMatrix b t).toLin' = simClassOf (mulLeft k t) := by
  -- The coordinates in `b` turn multiplication by `t` into its matrix.
  have h_coords (x : A) :
      b.equivFun (mulLeft k t x) = Matrix.toLin' (leftMulMatrix b t) (b.equivFun x) := by
    simp [leftMulMatrix_mulVec_repr]
  exact (simClassOf_eq_of_equiv b.equivFun h_coords).symm

omit [Finite k'] [Finite L] in
/-- Let `b` be a basis of `L` over `k`, and `σ ∈ Gal(k'/k)`. Applying `σ` to the factor `k'` of
`k' ⊗[k] L` applies `σ` to the coordinates in the basis of `k' ⊗[k] L` over `k'` induced by `b`. -/
private lemma basis_repr_congr_one_apply (b : Basis (Fin m) k L) (σ : Gal(k'/k))
    (x : k' ⊗[k] L) (j : Fin m) :
    (basis k' b).repr (Algebra.TensorProduct.congr σ (1 : Gal(L/k)) x) j =
      σ ((basis k' b).repr x j) := by
  induction x with
  | tmul a l => aesop
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

/-- Let `σ ∈ Gal(k'/k)` have fixed field `k` and act on `k' ⊗[k] L` through the factor `k'`. A unit
of `k' ⊗[k] L` is `1 ⊗ y` for a unit `y` of `L` exactly when `σ` fixes it. -/
private lemma mem_range_unitsMap_includeRight_iff {σ : Gal(k'/k)} (hσ : HasFixedField k σ)
    (x : (k' ⊗[k] L)ˣ) :
    x ∈ (Units.map (includeRight : L →ₐ[k] k' ⊗[k] L).toRingHom.toMonoidHom).range ↔
      Algebra.TensorProduct.congr σ (1 : Gal(L/k)) x.val = x.val := by
  let b : Basis (Fin (finrank k L)) k L := Module.finBasis k L
  let B : Basis (Fin (finrank k L)) k' (k' ⊗[k] L) := basis k' b
  constructor
  · rintro ⟨y, rfl⟩
    simp
  intro hx
  -- the coordinates of `x` in `B` are fixed by `σ`, so they lie in `k`
  have h_coord_mem (j : Fin (finrank k L)) : ∃ c : k, algebraMap k k' c = B.repr x j :=
    hσ.ge <| show σ (B.repr x j) = B.repr x j by
      rw [← basis_repr_congr_one_apply k k' b σ x j, hx]
  choose c hc using h_coord_mem
  have h_tmul_eq : (1 : k') ⊗ₜ[k] b.equivFun.symm c = x.val :=
    B.ext_elem fun j ↦ by simp [B, hc, Finsupp.single_apply]
  have h_ne : b.equivFun.symm c ≠ 0 := fun h_zero ↦ x.ne_zero (by simp [← h_tmul_eq, h_zero])
  exact ⟨Units.mk0 _ h_ne, Units.ext h_tmul_eq⟩

omit [IsAlgClosed K] in
/-- Let `L` be an extension of `k` of degree `m` with basis `b`. Let `β` be the action of
`Gal(k'/k)` on `(k' ⊗[k] L)ˣ` through the factor `k'`, and let `ρ` map `(k' ⊗[k] L)ˣ ⋊ Gal(k'/k)` to
`GL_m(k') ⋊ Gal(k'/k)` by sending a unit to its multiplication matrix in the basis induced by `b`;
by `h_comp` this map turns `β` into the entrywise action `galActionGL`. Suppose `ϑ` is a character
of `(k' ⊗[k] L)ˣ ⋊ Gal(k'/k)` with `ϑ s = θ (φ u)` whenever `s` lies over some `σ` with fixed field
`k` and `s ^ orderOf σ = u`. Then the induction of `ϑ` along `ρ` descends over `k` to
`(New.Hall.greenCuspidal k θ).mulMoebius`, that is, to `((β_θ·μ) ∗ 𝟙)·μ`, where `μ` is the inverse
of `𝟙` for the induction product: its value at each such `s` equals that class function at
`s ^ orderOf σ ∈ GL_m(k)`. -/
private lemma descendsTo_induceClassFn_greenCuspidal_mulMoebius [Finite k] (hrank : finrank k L = m)
    (φ : k' ⊗[k] L →ₐ[k'] K) (b : Basis (Fin m) k L) {β : Gal(k'/k) →* MulAut (k' ⊗[k] L)ˣ}
    (hβ_val : ∀ (τ : Gal(k'/k)) (u : (k' ⊗[k] L)ˣ),
      (β τ u : k' ⊗[k] L) = Algebra.TensorProduct.congr τ (1 : Gal(L/k)) u)
    (h_comp : ∀ τ : Gal(k'/k),
      (Units.map (leftMulMatrix (basis k' b)).toMonoidHom).comp (β τ).toMonoidHom =
        (galActionGL k k' (Fin m) τ).toMonoidHom.comp
          (Units.map (leftMulMatrix (basis k' b)).toMonoidHom))
    {ρ : (k' ⊗[k] L)ˣ ⋊[β] Gal(k'/k) →* GalSemidirect k k' (Fin m)}
    (hρ : ρ = SemidirectProduct.map (Units.map (leftMulMatrix (basis k' b)).toMonoidHom)
      (MonoidHom.id Gal(k'/k)) h_comp)
    {ϑ : (k' ⊗[k] L)ˣ ⋊[β] Gal(k'/k) → ℂ} (hϑ_char : IsChar ϑ)
    (hϑ_descends : ∀ σ : Gal(k'/k), HasFixedField k σ →
      DescendsOnCoset rightHom σ inl ϑ fun u : (k' ⊗[k] L)ˣ ↦ θ (φ u.val)) :
    DescendsTo (induceClassFn rightHom ρ ϑ) (greenCuspidal k θ).mulMoebius := by
  subst hρ
  intro σ hσ
  let B : Basis (Fin m) k' (k' ⊗[k] L) := basis k' b
  have : Fintype (k' ⊗[k] L) := fintypeOfFintype B
  -- The units of `k' ⊗[k] L` fixed by `σ` are those of `L`.
  let ι : Lˣ →* (k' ⊗[k] L)ˣ :=
    Units.map (includeRight : L →ₐ[k] k' ⊗[k] L).toRingHom.toMonoidHom
  have hfix (x : (k' ⊗[k] L)ˣ) : x ∈ ι.range ↔ β σ x = x := by
    simpa [ι, Units.ext_iff, hβ_val] using mem_range_unitsMap_includeRight_iff k k' hσ x
  -- Descent commutes with induction (`DescendsOnCoset.induce`), so it remains to see by inner
  -- products that `(greenCuspidal k θ).mulMoebius` is induced from `Lˣ`: this is
  -- `rankInner_greenCuspidal_mulMoebius`.
  obtain ⟨r_GL, hr_GL, -⟩ := exists_isRootChoice_GL (n := Fin m) hσ
  -- `σ` acts on the units through a `σ`-semilinear ring map: both sides send `x` to `σ x ⊗ 1`
  have hg_semiconj : Function.Semiconj (algebraMap k' (k' ⊗[k] L)) σ
      (Algebra.TensorProduct.congr σ (1 : Gal(L/k)) : k' ⊗[k] L →+* k' ⊗[k] L) := fun _ ↦ rfl
  obtain ⟨r_units, hr_units, -⟩ := exists_isRootChoice (β := β)
    (Algebra.TensorProduct.congr σ (1 : Gal(L/k))) (hβ_val σ) hg_semiconj
    (Units.map_injective (RingHom.injective _)) hfix
  -- `ρ` sends a unit of `L` to its matrix in the basis `b`, seen over `k'`
  have h_comm (y : Lˣ) :
      SemidirectProduct.map (Units.map (leftMulMatrix B).toMonoidHom) (MonoidHom.id Gal(k'/k))
          h_comp ((SemidirectProduct.inl.comp ι) y) =
        (SemidirectProduct.inl.comp (Matrix.GeneralLinearGroup.map (algebraMap k k')))
          (Units.map (leftMulMatrix b).toMonoidHom y) := by
    ext i j
    · simp [B, ι, leftMulMatrix_eq_repr_mul]
    · rfl
  refine .induce hr_GL hϑ_char.isClassFunction (Units.map (leftMulMatrix b).toMonoidHom) h_comm
    hr_units (fun s γ ↦ hϑ_descends σ hσ s (ι γ)) isClassFunction_evalGL fun χ hχ ↦ ?_
  obtain ⟨Y, rfl⟩ := exists_eq_evalGL hχ
  -- `μ` is real, so it moves to the other side of the inner product
  have h_rank_eq : rankInner m (greenCuspidal k θ).mulMoebius Y =
      rankInner (finrank k L) (greenCuspidal k θ) Y.mulMoebius := by
    simp [← hrank, rankInner.eq_1, mul_right_comm, mul_assoc]
  -- the latter is a mean over `Lˣ` (`rankInner_greenCuspidal_mulMoebius`)
  rw [classInner_evalGL, Fintype.card_fin, h_rank_eq,
    rankInner_greenCuspidal_mulMoebius θ ((AlgHom.liftEquiv k k' L K).symm φ) Y]
  -- the matrix of `z` in `b` has the class of multiplication by `z`
  simp [ι, classInner, evalGL, simClassOf_leftMulMatrix]

omit [IsAlgClosed K] [Algebra k K] [IsScalarTower k k' K] in
/-- Descent over `k'` in `exists_torus_induced_descendsTo`. Let `B` be a `k'`-basis of `k' ⊗[k] L`,
let `β` be the action of `Gal(k'/k)` on `(k' ⊗[k] L)ˣ` through the factor `k'`, and let
`ρ : (k' ⊗[k] L)ˣ ⋊ Gal(k'/k) → GL_m(k') ⋊ Gal(k'/k)` send a unit to its matrix in `B`. If `ϑ` is a
character with `ϑ(s) = ∏_τ θ(φ(τ s₁))`, where `s₁` is the unit part of `s`, then the class function
induced from `ϑ` along `ρ` over `Gal(k'/k)` satisfies `DescendsTo` (equals `X` on `GL_m(k')`) for
every `X : Hall k'` whose rank-`m` inner product with every `Y` is the mean over units `t` of
`conj θ(φ(∏_τ τ t))` times `Y` at the class of multiplication by `t`. -/
private lemma descendsTo_induceClassFn_of_rankInner_eq (φ : k' ⊗[k] L →ₐ[k'] K)
    (B : Basis (Fin m) k' (k' ⊗[k] L)) {β : Gal(k'/k) →* MulAut (k' ⊗[k] L)ˣ}
    (hβ_val : ∀ (τ : Gal(k'/k)) (u : (k' ⊗[k] L)ˣ),
      (β τ u : k' ⊗[k] L) = Algebra.TensorProduct.congr τ (1 : Gal(L/k)) u)
    (h_comp : ∀ τ : Gal(k'/k),
      (Units.map (leftMulMatrix B).toMonoidHom).comp (β τ).toMonoidHom =
        (galActionGL k k' (Fin m) τ).toMonoidHom.comp (Units.map (leftMulMatrix B).toMonoidHom))
    {ρ : (k' ⊗[k] L)ˣ ⋊[β] Gal(k'/k) →* GalSemidirect k k' (Fin m)}
    (hρ : ρ = SemidirectProduct.map (Units.map (leftMulMatrix B).toMonoidHom)
      (MonoidHom.id Gal(k'/k)) h_comp)
    {ϑ : (k' ⊗[k] L)ˣ ⋊[β] Gal(k'/k) → ℂ} (hϑ_char : IsChar ϑ)
    (hϑ_eq_prod : ∀ s : (k' ⊗[k] L)ˣ ⋊[β] Gal(k'/k), ϑ s = ∏ τ : Gal(k'/k), θ (φ (β τ s.left)))
    (X : Hall k')
    (hX : ∀ Y : Hall k',
      rankInner m X Y =
        finMean fun t : (k' ⊗[k] L)ˣ ↦
          conj (θ (φ (∏ τ : Gal(k'/k),
              Algebra.TensorProduct.map τ.toAlgHom (AlgHom.id k L) t.val))) *
            Y (simClassOf (mulLeft k' t.val))) :
    DescendsTo (induceClassFn rightHom ρ ϑ) X := by
  have : Fintype (k' ⊗[k] L) := fintypeOfFintype B
  -- Here `σ = 1`, and every unit of `k' ⊗[k] L` is its own root.
  intro σ hσ
  obtain rfl : σ = 1 := σ.ext fun x ↦ hσ.le ⟨x, rfl⟩
  obtain ⟨r_GL, hr_GL, -⟩ := exists_isRootChoice_GL (n := Fin m) hσ
  have hr_units : IsRootChoice (rightHom.comp ρ) 1 inl inl :=
    { injective := inl_injective
      -- `inl γ` lies over `1`, whose order is one
      map_apply := by simp [hρ]
      pow_orderOf := by simp
      map_conj := by simp [← map_inv, ← map_mul]
      -- the kernel of `rightHom` is the image of `inl`
      mem_range_of_conj := by simp +contextual [hρ, range_inl_eq_ker_rightHom] }
  have h_comm (t : (k' ⊗[k] L)ˣ) :
      ρ (inl t) = (SemidirectProduct.inl.comp (Matrix.GeneralLinearGroup.map (algebraMap k' k')))
        (t.map (leftMulMatrix B)) := by simp [hρ]
  have h_lift : DescendsOnCoset (rightHom.comp ρ) 1 inl ϑ (ϑ ∘ inl) := by simp_all [DescendsOnCoset]
  -- Descent commutes with induction; the inner products with class functions are those of `hX`.
  refine .induce hr_GL hϑ_char.isClassFunction (fun t ↦ t.map (leftMulMatrix B)) h_comm hr_units
    h_lift isClassFunction_evalGL fun χ hχ ↦ ?_
  obtain ⟨Y, rfl⟩ := exists_eq_evalGL hχ
  have h_summand (t : (k' ⊗[k] L)ˣ) :
      ϑ (inl t) =
        θ (φ (∏ τ : Gal(k'/k), Algebra.TensorProduct.map τ.toAlgHom (AlgHom.id k L) t.val)) := by
    aesop (add simp [hϑ_eq_prod, hβ_val, map_prod])
  rw [classInner_evalGL, Fintype.card_fin, hX Y]
  -- the matrix of `t` in `B` has the class of multiplication by `t`
  simp [classInner, evalGL, simClassOf_leftMulMatrix, h_summand]

variable [Finite k]

omit [IsAlgClosed K] in
/-- Let `k ⊆ k'` be finite fields, `K` a field over `k'` with a multiplicative character `θ`, `L` an
extension of `k` of degree `m`, and `φ : k' ⊗[k] L → K` a `k'`-algebra map. (a) There is a character
`Φ` of `GL_m(k') ⋊ Gal(k'/k)` that (b) descends over `k` to `C_θ·μ`, and (c) descends over `k'` to
every `X : Hall k'` whose rank-`m` inner product with every `Y` is the mean over `t ∈ (k' ⊗[k] L)ˣ`
of `conj θ(φ(∏_τ τ t))` times `Y` at the class of multiplication by `t`. Here
`C_θ = greenCuspidal k θ = (β_θ·μ) ∗ 1`, `μ` is the inverse of the constant function 1 for parabolic
induction, `τ ∈ Gal(k'/k)` acts on the factor `k'`, and `DescendsTo Φ X` means `Φ(s) = X(s^{ord σ})`
whenever `s` lies over a `σ` whose fixed field is the field of `X`. -/
lemma exists_torus_induced_descendsTo (hrank : finrank k L = m) (φ : k' ⊗[k] L →ₐ[k'] K) :
    ∃ Φ : GalSemidirect k k' (Fin m) → ℂ,
      -- (a)
      IsChar Φ ∧
      -- (b)
      DescendsTo Φ (greenCuspidal k θ).mulMoebius ∧
      -- (c)
      ∀ X : Hall k',
        (∀ Y : Hall k',
          rankInner m X Y =
            finMean fun t : (k' ⊗[k] L)ˣ ↦
              conj (θ (φ (∏ τ : Gal(k'/k),
                  Algebra.TensorProduct.map τ.toAlgHom (AlgHom.id k L) t.val))) *
                Y (simClassOf (mulLeft k' t.val))) →
        DescendsTo Φ X := by
  -- A basis of `L` embeds `Aˣ ⋊ Gal(k'/k)`, `A = k' ⊗ L`, in `GalSemidirect` (the map `ρ`);
  -- induce from there the character `ϑ (a, σ) = ∏ τ, θ (φ (τ a))`.
  let b : Basis (Fin m) k L := finBasisOfFinrankEq k L hrank
  let B : Basis (Fin m) k' (k' ⊗[k] L) := basis k' b
  have : Fintype (k' ⊗[k] L) := fintypeOfFintype B
  -- `σ` acts on `A` through the first factor, hence on coordinates in the basis `B`
  let g (σ : Gal(k'/k)) : k' ⊗[k] L ≃ₐ[k] k' ⊗[k] L := Algebra.TensorProduct.congr σ (1 : Gal(L/k))
  have hrepr (σ : Gal(k'/k)) (x : k' ⊗[k] L) (j : Fin m) : B.repr (g σ x) j = σ (B.repr x j) :=
    basis_repr_congr_one_apply k k' b σ x j
  let β : Gal(k'/k) →* MulAut (k' ⊗[k] L)ˣ :=
    .mk' (fun σ ↦ Units.mapEquiv (g σ).toMulEquiv) (by aesop (add simp B.ext_elem_iff))
  -- the matrix of `g σ x` in `B` is the matrix of `x` with `σ` applied to its entries
  have hβ_matrix (σ : Gal(k'/k)) :
      (Units.map (leftMulMatrix B).toMonoidHom).comp (β σ).toMonoidHom =
        (galActionGL k k' (Fin m) σ).toMonoidHom.comp
          (Units.map (leftMulMatrix B).toMonoidHom) := by
    ext
    simp [galActionGL, β, ← hrepr, B, g, Units.mapEquiv, leftMulMatrix_eq_repr_mul]
  let ρ : (k' ⊗[k] L)ˣ ⋊[β] Gal(k'/k) →* GalSemidirect k k' (Fin m) :=
    map (Units.map (leftMulMatrix B).toMonoidHom) (MonoidHom.id Gal(k'/k)) hβ_matrix
  obtain ⟨ϑ, hϑ_char, hϑ_eq_prod, hϑ_descends⟩ := exists_norm_char_semidirect β (θ.comp φ)
  have hΦ_char : IsChar (induceClassFn rightHom ρ ϑ) :=
    isChar_of_mem_virtualChars
      (induceClassFn_mem_virtualChars rightHom_surjective hϑ_char.mem_virtualChars)
  have hβ_val (τ : Gal(k'/k)) (u : (k' ⊗[k] L)ˣ) : (β τ u : k' ⊗[k] L) = g τ u := rfl
  refine ⟨induceClassFn rightHom ρ ϑ, hΦ_char, ?_, fun X hX ↦ ?_⟩
  · exact descendsTo_induceClassFn_greenCuspidal_mulMoebius k k' θ hrank φ b hβ_val hβ_matrix rfl
      hϑ_char hϑ_descends
  · exact descendsTo_induceClassFn_of_rankInner_eq k k' θ φ B hβ_val hβ_matrix rfl
      hϑ_char hϑ_eq_prod X hX

/-- For a multiplicative character `θ` of `K`, let `β_θ = New.Hall.brauerLift k θ` send a matrix
over `k` to the sum of `θ` over the roots of its characteristic polynomial, with multiplicity. Then
some class function `B : Hall k'` lifts `β_θ` over `ℤ` (`New.Lift`). That is, for each `m` one
ℤ-combination of characters of `GL_m(k') ⋊ Gal(k'/k)` descends to both. -/
lemma exists_lift_brauerLift : ∃ B : Hall k', Lift ℤ (brauerLift k θ) B := by
  -- `(greenCuspidal k θ).mulMoebius` has a lift `I`, by `exists_torus_induced_descendsTo` in each
  -- positive dimension.
  obtain ⟨I, hI⟩ : ∃ I : Hall k', Lift ℤ (greenCuspidal k θ).mulMoebius I := by
    refine Lift.exists_lift_of_descendsTo ?_
    rintro (_ | m)
    · -- in dimension `0` the function `greenCuspidal k θ` vanishes, and `0` descends to it
      exact ⟨0, zero_mem _,
        by simp [greenCuspidal_eq_zero_of_dim_lt_one, DescendsTo, DescendsOnCoset, evalGL]⟩
    · -- in dimension `m + 1`, use the extension of `k` of degree `m + 1`
      obtain ⟨Φ, hΦ_char, hΦ_descends, -⟩ := exists_torus_induced_descendsTo k k' θ
        (finrank_extension k (ringChar k) (m + 1)) (AlgHom.liftEquiv k k' _ K IsAlgClosed.lift)
      exact ⟨Φ, hΦ_char.mem_virtualChars, hΦ_descends⟩
  -- Recursion on the dimension: liftable `J` that agree with `-greenCuspidal k θ` below `N`.
  have h_approx (N : ℕ) : ∃ (J : Hall k) (J' : Hall k'),
      Lift ℤ J J' ∧ ∀ c : SimClass k, c.dim < N → (greenCuspidal k θ + J : Hall k) c = 0 := by
    induction N with
    | zero => exact ⟨constOne, constOne, .lift_constOne, nofun⟩
    | succ N ih =>
      obtain ⟨J, J', hJ, hJ_vanish⟩ := ih
      refine ⟨((greenCuspidal k θ).mulMoebius - (J * constOne - J).mulMoebius) * constOne,
        (I - (J' * constOne - J').mulMoebius) * constOne,
        (hI.sub ((hJ.mul .lift_constOne).sub hJ).mulMoebius).mul .lift_constOne, ?_⟩
      -- `(greenCuspidal k θ + J) * (1 - constOne)` vanishes one dimension further, and
      -- `greenCuspidal k θ * constOne` is `-brauerLift k θ`.
      have hstep (c : SimClass k) (hc : c.dim < N + 1) :
          greenCuspidal k θ c + J c = (J * constOne : Hall k) c - brauerLift k θ c := by
        have h_prod_zero : ((greenCuspidal k θ + J) * (1 - constOne) ^ 1 : Hall k) c = 0 :=
          Hall.mul_apply_eq_zero_of_dim_lt hJ_vanish (one_sub_constOne_pow_apply_eq_zero 1) c hc
        have h_expand : ((greenCuspidal k θ + J) * (1 - constOne) ^ 1 : Hall k) =
            greenCuspidal k θ + J + brauerLift k θ - J * constOne := by
          rw [pow_one, mul_sub, mul_one, add_mul, greenCuspidal_mul_constOne]
          abel
        rw [h_expand] at h_prod_zero
        simp only [sub_eq_add_neg, Hall.add_apply, Hall.neg_apply] at h_prod_zero
        linear_combination h_prod_zero
      -- So `(brauerLift k θ + greenCuspidal k θ - (J * constOne - J)).mulMoebius` vanishes below
      -- `N + 1`, and its product with `constOne` is `greenCuspidal k θ` plus the next function.
      nth_rw 1 [greenCuspidal, ← add_mul]
      refine Hall.mul_apply_eq_zero_of_dim_lt (n := 0) (fun c hc ↦ ?_) nofun
      simp only [sub_eq_add_neg, Hall.add_apply, Hall.neg_apply, mulMoebius]
      linear_combination moebius c * hstep c hc
  obtain ⟨C, hC⟩ : ∃ C : Hall k', Lift ℤ (-greenCuspidal k θ) C := by
    refine Lift.exists_lift_of_descendsTo fun m ↦ ?_
    obtain ⟨J, J', hJ, hJ_vanish⟩ := h_approx (m + 1)
    obtain ⟨Φ, hΦ_virt, hΦ_J, -⟩ := hJ m
    refine ⟨Φ, hΦ_virt, hΦ_J.of_evalGL_eq fun γ ↦ ?_⟩
    -- `J` agrees with `-greenCuspidal k θ` at the class of `γ`, whose dimension is `m < m + 1`
    have h_sum_zero :
        greenCuspidal k θ (simClassOf (Matrix.toLin' γ.val)) +
          J (simClassOf (Matrix.toLin' γ.val)) = 0 :=
      hJ_vanish _ (by simp)
    rw [Hall.evalGL, Hall.evalGL, Hall.neg_apply]
    linear_combination h_sum_zero
  -- `brauerLift k θ = -greenCuspidal k θ * constOne`
  have h_brauer : brauerLift k θ = -greenCuspidal k θ * constOne := by
    rw [neg_mul, greenCuspidal_mul_constOne, neg_neg]
  exact ⟨C * constOne, by simpa only [h_brauer] using hC.mul .lift_constOne⟩

end GreenLift

end New
