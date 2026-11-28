import Lib.Adelic.AutomorphicForms.HeckeEigenforms
import Lib.General.LinearAlgebra.BlockEmbeddings
import Lib.LocalGL.Shintani.LiftingGreenCharacters

/-!
# Local GL_N(E_w)-action on forms, parahoric types and labels at a split place

This file relates forms on a definite hermitian space `V` to the local theory of `GL_N(E_w)` at a
split place `w`. The action of `GL n (𝒪_w)` on a function on the finite adelic group is then
described through the finite group `GL n (k_w)`, in two ways: by parahoric types and by labels.

## Main definitions and results

* `New.Patching.localFormRep`: the local representation on forms. It is smooth, and the vectors
  fixed by the pro-`p` Iwahori subgroup `New.proIwahori` in the span of the translates of one form
  (`New.cyclicSpan`) are finite-dimensional; both are instances.
* `New.hasHeckePolyAt_iff_localFormRep`: the Hecke polynomial at `w` read in the local
  representation.
* `New.HasParahoricType`: `f` has a parahoric type: the parabolic subgroup with blocks `b` acts
  through characters of the determinant on all blocks but one, and on the remaining block through a
  character of the determinant times a function `F`.
* `New.HasProductLabel`: `f` has a label: the class function of `GL n (k_w)` built from a polynomial
  and characters does not kill `f` (`New.HasLabel`).
* `New.HasParahoricType.hasProductLabel`: a type gives a label.

Notions from other files:
* `New.ofSplitPlace`: For a split place w, the homomorphism GL_n(E_w) → G_f sending g to the unitary
  element with component g at w and 1 off w, w̄; `New.offPartComap` is the open subgroup of G_f
  pulled back along the map replacing the components of an element of G_f at w and w̄ by 1.
* `New.ResField`: The residue field of the completion E_w of E at the finite place w.
* `New.labelChar`: The multiplicative map sending `c` to the parabolic-induction product of the
  class functions attached to the monic irreducible factors of `c`, with multiplicity.

## Relation to the literature

Known; see `Lib.GaloisRep.LocalGlobal.LabelCompatibility` for sources.
-/

namespace New

/-!
## The local representation on forms and its Hecke polynomials

`New.IsEigenform f P` says `f ≠ 0` and `New.HasHeckePolyAt f w hw (P w)` at almost all places of
prime norm; `New.levelSpace π K` is the space of `K`-fixed vectors.
-/

section LocalRep

variable {E n : Type _} [Field E] [CMType E] [Fintype n]
  [DecidableEq n] (V : Space E n 1) (κ) {w : FinPlace E} (hw : star w ≠ w)

/-- For a split place w, the homomorphism GL_N(E_w) → G_f, N the cardinality of n, given by a
chosen numbering of n followed by `New.ofSplitPlace`. -/
noncomputable abbrev Patching.embedAtSplit {E : Type _} [Field E] [NumberField E]
    [NumberField.IsCMField E] {w : FinPlace E} (hw : star w ≠ w) :
    GL (Fin (Fintype.card n)) (LocField w) →* Gf E n :=
  (ofSplitPlace hw).comp (reindexGL (Fintype.equivFin n)).symm.toMonoidHom

/-- The representation of GL_N(E_w), N the cardinality of n, on forms of weight κ (a `New.Weight E`)
on V at a split place w: right translation `V.formTranslation κ` by G_f, pulled back along
`embedAtSplit`, which uses a chosen numbering of n. -/
noncomputable abbrev Patching.localFormRep :
    Rep.{0, 0, 0} ℂ (GL (Fin (Fintype.card n)) (LocField w)) :=
  Rep.of ((V.formTranslation κ).comp (embedAtSplit hw))

end LocalRep

section LocalTranslates

open Set Fintype Submodule Module End Gf Patching

variable {E n : Type _} [Field E] [CMType E] [Fintype n]
  [DecidableEq n] {V : Space E n 1} {κ : Weight E} {w : FinPlace E} {hw : star w ≠ w}
  {x : localFormRep V κ hw}

/-- The local representation on forms is smooth: each form is fixed by an open subgroup of the
local group. -/
instance : IsSmoothRep (localFormRep V κ hw).ρ := by
  refine ⟨fun x ↦ ?_⟩
  -- The stabiliser of `x` is open, and so is its preimage in the local group.
  have h_cont : Continuous (embedAtSplit (n := n) hw) :=
    (continuous_ofSplitPlace hw).comp (.units_map _
      (continuous_id.matrix_reindex (equivFin n).symm (equivFin n).symm))
  obtain ⟨h_stab_open, -⟩ := x.prop
  have h_open : IsOpen (embedAtSplit hw ⁻¹' (rightStabilizer x.val).carrier) :=
    h_stab_open.preimage h_cont
  filter_upwards [h_open.mem_nhds (by simp)] with g hg
  exact Subtype.ext (funext hg)

/-- In the span of the translates of one form, the vectors fixed by the pro-`p` Iwahori subgroup
form a finite-dimensional space. -/
instance :
    Module.Finite ℂ
      ((cyclicSpan (localFormRep V κ hw).ρ x).submoduleOf
        (levelSpace (localFormRep V κ hw).ρ proIwahori)) := by
  -- Let `K` be the open subgroup of the `k` whose part off `w, w̄` fixes `x` and whose component at
  -- `w` lies in `proIwahori`. The space in question embeds in the finite-dimensional space of
  -- `K`-fixed forms.
  let r : GL n (LocField w) ≃* GL (Fin (card n)) (LocField w) := reindexGL (equivFin n)
  let Kloc : OpenSubgroup (GL n (LocField w)) := .comap r.toMonoidHom
    (.units_map _ (continuous_id.matrix_reindex _ _)) ⟨proIwahori, isOpen_proIwahori⟩
  obtain ⟨h_stab_open, -⟩ := x.prop
  let K : OpenSubgroup (Gf E n) :=
    offPartComap hw ⟨rightStabilizer x.val, h_stab_open⟩ ⊓
      Kloc.comap (Gf.atPlace w) (continuous_atPlace w)
  have h_fg : (levelSpace (V.formTranslation κ) K).FG :=
    Finite.iff_fg.mp (V.finite_formTranslation_levelSpace κ K.isOpen')
  refine .of_fg (fg_of_fg_map (levelSpace (localFormRep V κ hw).ρ proIwahori).subtype
    (ker_subtype _) (h_fg.of_le ?_))
  rintro _ ⟨z, hz, rfl⟩ ⟨k, hk_off, hk_at⟩
  -- On the translates of `x`, the element `k` acts as its component at `w`: its part off `w, w̄`
  -- commutes with the local group and fixes `x`.
  have h_act (g : GL (Fin (card n)) (LocField w)) :
      V.formTranslation κ k ((localFormRep V κ hw).ρ g x) =
        (localFormRep V κ hw).ρ (r (k.atPlace w)) ((localFormRep V κ hw).ρ g x) := by
    ext1
    ext1 y
    refine .trans ?_ (hk_off (y * embedAtSplit hw (r (k.atPlace w)) * embedAtSplit hw g))
    simp [r, (commute_supportedOn_trivialOn (ofSplitPlace_mem_supportedOn _ _) _).right_comm,
      ← mul_assoc]
  -- So it does on their span, and that component fixes `z`.
  exact (LinearMap.eqOn_span (eqOn_range.mpr (funext h_act)) hz).trans (z.prop ⟨_, hk_at⟩)

variable (V κ) in
/-- A positive definite sesquilinear form on the forms of weight `κ` on `V` for which right
translation by the finite adelic unitary group is unitary (`New.IsUnitary`), chosen by
`New.Space.exists_isUnitary_formTranslation`. -/
noncomputable def Space.invariantForm : V.forms κ →ₗ⋆[ℂ] V.forms κ →ₗ[ℂ] ℂ :=
  (V.exists_isUnitary_formTranslation κ).choose

variable (V κ) in
lemma Space.isUnitary_formTranslation : IsUnitary (V.formTranslation κ) (V.invariantForm κ) :=
  (V.exists_isUnitary_formTranslation κ).choose_spec

lemma isUnitary_localFormRep : IsUnitary (localFormRep V κ hw).ρ (V.invariantForm κ) := by
  obtain ⟨h_pos, h_inv⟩ := V.isUnitary_formTranslation κ
  exact ⟨h_pos, fun a ↦ h_inv (embedAtSplit hw a)⟩

/-- If a form x on V is an eigenform for the system P of Hecke polynomials, then so is every
non-zero y in the span of the translates of x under the local group GL_n(E_w) at a split
place w. -/
lemma IsEigenform.of_mem_cyclicSpan {y : localFormRep V κ hw} {P : FinPlace E → Polynomial ℂ}
    (hx_eig : IsEigenform x.val P) (hy : y ∈ cyclicSpan (localFormRep V κ hw).ρ x) (hy_ne : y ≠ 0) :
    IsEigenform y.val P := by
  -- At a place `u` other than `w` and its conjugate, translation by the local group at `w`
  -- commutes with the maximal compact subgroup and with the Hecke operators at `u`; so the
  -- translates of `x`, and with them their span, stay in the same eigenspaces.
  obtain ⟨-, hx_ev⟩ := hx_eig
  -- The exceptional places are `w` and its conjugate.
  have h_away :
      ∀ᶠ u : FinPlace E in Filter.cofinite, u ∈ (insert w (star {w}) : Set (FinPlace E))ᶜ :=
    ((toFinite {w}).star.insert w).compl_mem_cofinite
  refine ⟨by simpa using hy_ne, hx_ev.mp (h_away.mono ?_)⟩
  intro u hu hx_at hq
  obtain ⟨hsplit, hx_hecke⟩ := hx_at hq
  obtain ⟨h_fixed, t, hP, h_hecke⟩ := (hasHeckePolyAt_iff hsplit).mp hx_hecke
  rw [mem_span] at hy
  refine ⟨hsplit, (hasHeckePolyAt_iff hsplit).mpr
    ⟨hy (sphericalAt (V.formTranslation κ) u) ?_, t, hP, fun j ↦ ?_⟩⟩
  · -- an element `k` of the compact subgroup at `u` moves past the translation and fixes `x`
    rintro _ ⟨g, rfl⟩
    refine mem_levelSpace.mpr fun k ↦ ?_
    obtain ⟨-, hk_supp⟩ := k.prop
    have h_triv : embedAtSplit hw g ∈ Gf.trivialOn n {u} := by
      aesop (add simp atPlace_ofSplitPlace_of_ne)
    have h_comm : Commute k.val (embedAtSplit hw g) := commute_supportedOn_trivialOn hk_supp h_triv
    have h_swap :
        V.formTranslation κ k (V.formTranslation κ (embedAtSplit hw g) x) =
          V.formTranslation κ (embedAtSplit hw g) (V.formTranslation κ k x) := by
      rw [← mul_apply, ← map_mul, h_comm.eq, map_mul, mul_apply]
    simpa [mem_levelSpace.mp h_fixed k] using h_swap
  · -- the Hecke operators at `u` commute with the translations at `w`, so each translate of `x`
    -- is an eigenvector with eigenvalue `t j`
    have h_range : Set.range (fun g ↦ (localFormRep V κ hw).ρ g x) ⊆
        eigenspace (heckeSplit (V.formTranslation κ) hsplit j) (t j) := by
      simp_all [← heckeSplit_comm_of_trivialOn, range_subset_iff, atPlace_ofSplitPlace_of_ne]
    simpa using hy _ h_range

/-- At a split place w, a form x has Hecke polynomial P if and only if, in the local
representation of GL_n(E_w) on forms, GL_n(O_w) fixes x, the j-th Hecke operator scales x by
t_j, and P = Σ (−1)^j q_w^{j(j−1)/2} t_j X^{n−j}. -/
lemma hasHeckePolyAt_iff_localFormRep {P : Polynomial ℂ} :
    HasHeckePolyAt x.val w hw P ↔
      x ∈ levelSpace (localFormRep V κ hw).ρ (localIntGL (Fin (card n)) w) ∧
      ∃ t : ℕ → ℂ,
        P = heckePoly w.q (card n) t ∧ ∀ j : ℕ, heckeGL (localFormRep V κ hw).ρ j x = t j • x := by
  -- Both sides agree after transport along the isomorphism `r` that renumbers the indices.
  let r : GL n (LocField w) ≃* GL (Fin (card n)) (LocField w) := reindexGL (equivFin n)
  have h_fixed : x ∈ levelSpace ((V.formTranslation κ).comp (ofSplitPlace hw)) (localIntGL n w) ↔
      x ∈ levelSpace (localFormRep V κ hw).ρ (localIntGL (Fin (card n)) w) := by
    simp [reindex_equiv r, r, reindex_equiv (equivFin n).symm, mem_intGL]
  -- `r` matches the maximal compact subgroups and the double cosets `basicDoubleCoset`, hence the
  -- Hecke operators, which `heckeFun_comp` transports along a surjective homomorphism.
  have h_hecke (hx : x ∈ levelSpace (localFormRep V κ hw).ρ (localIntGL (Fin (card n)) w)) (j : ℕ) :
      heckeSplit (V.formTranslation κ) hw j x = heckeGL (localFormRep V κ hw).ρ j x := by
    apply heckeFun_comp r.toMonoidHom _ hx (isHeckeFunction_basicDoubleCoset j).1 r.surjective
    · simp [r, reindex_equiv (equivFin n).symm, mem_intGL]
    · simp [r]
    · simp [r, indicator, basicDoubleCoset, reindex_equiv (equivFin n).symm]
    · simp
  rw [hasHeckePolyAt_iff, mem_sphericalAt_iff hw, h_fixed]
  refine and_congr_right fun hx ↦ ?_
  simp only [h_hecke hx]

end LocalTranslates

/-! ## Parahoric types and labels at a split place -/

section ParahoricTypeLabel

open NumberField Matrix Polynomial Fintype Function Fin Set MulChar Finset

attribute [local instance low] Fintype.ofFinite

variable {E n M K ρ : Type} [Field E] [NumberField E] [IsCMField E] [Fintype n] [DecidableEq n]
  {w : FinPlace E} [Field K] [Algebra (ResField w) K] [Fintype ρ] [DecidableEq ρ] {s : ℕ}
  {V : Type*} [AddCommGroup V] [Module ℂ V] {σ : Representation ℂ (GL ρ (ResField w)) V}

/-- `f` has a parahoric type at the split place `w`. The function `b` cuts the indices into blocks
`0, …, s`, and `e` numbers block `0`. An integral matrix `k` whose reduction is block triangular,
with block `0` equal to `x`, sends `f` to `∏ l, χ l (det k_(l+1))` times `ψ (det x)` times `F x`. -/
def HasParahoricType (f : Gf E n → M → ℂ) (hw : w.IsSplit) (e : ρ ↪ n) (b : n → Fin (s + 1))
    (ψ : MulChar (ResField w) ℂ) (χ : Fin s → MulChar (ResField w) ℂ)
    (F : GL ρ (ResField w) → Gf E n → M → ℂ) : Prop :=
  -- (a) block `0` is the image of `e`
  (∀ i : n, b i = 0 ↔ i ∈ Set.range e) ∧
  -- (b) an integral `k` with block triangular reduction and block `0` equal to `x` sends `f` to
  -- `ψ (det x) • F x` times the characters of the determinants of the other blocks
  ∀ (k : intGL n Valued.v.integer) (x : GL ρ (ResField w)) (h : reduceGL k ∈ parabolic b),
    submatrix (reduceGL k) e e = x.val →
    rightRegular ℂ (Gf E n) (M → ℂ) (ofSplitPlace hw k.val) f =
      (∏ l : Fin s, χ l (blockHom b l.succ ⟨reduceGL k, h⟩).det.val) • ψ x.det.val • F x

/-- `f` has a label at `w` built from `c` and the characters `χ l`. Here `c` is a label of degree
`d` (`IsLabel`), `c * ∏ l, (X - charName T (χ l))` is separable (`charName T (χ l)`, a unit of
`ResField w`, is the name of `χ l` read through `T`), and `d + ∑ l, t l = card n`. The label is
`labelChar T c * ∏ l, (χ l ∘ det on GL (t l))`. -/
def HasProductLabel (f : Gf E n → M → ℂ) (hw : star w ≠ w) (T : MulChar K ℂ) [IsFaithfulMulChar K T]
    (d : ℕ) (c : (ResField w)[X]) (χ : Fin s → MulChar (ResField w) ℂ) (t : Fin s → ℕ) : Prop :=
  -- (a) `c` is a label of degree `d`
  IsLabel d c ∧
  -- (b) the roots of `c` are simple, and they and the names of the `χ l` are pairwise distinct
  Separable (c * ∏ l : Fin s, (X - C (charName T (χ l)).val)) ∧
  -- (c) the block sizes `d` and `t l` add up to the rank
  d + ∑ l : Fin s, t l = Fintype.card n ∧
  -- (d) `f` has the class function induced from `labelChar T c` and the `χ l ∘ det` in size `t l`
  HasLabel f hw (labelChar T c * ∏ l : Fin s, (detChar (χ l)).rankPart (t l)).evalGL

omit [IsCMField E] in
/-- Let block `0` of the blocks `b` be the image of `e` (`h_block`). Then the map from the
parabolic subgroup of `b` to `GL ρ (ResField w)` that takes block `0`, renumbered along `e`, is
onto: a matrix `x` extends by the identity matrix outside block `0`. -/
private lemma surjective_reindexGL_comp_blockHom_zero {e : ρ ↪ n} {b : n → Fin (s + 1)}
    (h_block : ∀ i : n, b i = 0 ↔ i ∈ Set.range e) :
    Surjective
      ((reindexGL ((Equiv.subtypeEquivRight h_block).trans e.toEquivRange.symm)).toMonoidHom.comp
        (blockHom b 0) : parabolic b →* GL ρ (ResField w)) := by
  intro x
  obtain ⟨h_block0, h_off⟩ := submatrix_extendGL_and_apply_of_notMem_range e x
  refine ⟨⟨extendGL e x, fun _ ↦ ?_⟩, Units.ext h_block0⟩
  grind [one_apply_ne]

/-- Over a perfect field, `a * ∏ l, (X - C (x l))` is separable when `a` is squarefree, the `x l`
are distinct and none of them is a root of `a`. -/
private lemma _root_.Polynomial.separable_mul_prod_X_sub_C_of_squarefree {F : Type*} [Field F]
    [PerfectField F] {s : ℕ} {a : F[X]} {x : Fin s → F} (ha : Squarefree a) (hx : Injective x)
    (h_root : ∀ l : Fin s, ¬a.IsRoot (x l)) : (a * ∏ l : Fin s, (X - C (x l))).Separable := by
  refine (PerfectField.separable_iff_squarefree.mpr ha).mul (separable_prod_X_sub_C_iff.mpr hx)
    (.prod_right fun l _ ↦ ?_)
  exact ((prime_X_sub_C (x l)).coprime_iff_not_dvd.mpr (mt dvd_iff_isRoot.mp (h_root l))).symm

/-- A parahoric type gives a label. Let `σ` be a representation of `GL ρ (k_w)` on `V`, `L` an
injective linear map from `V` to functions on the finite adelic group, and `y` a vector not killed
by the idempotent `labelIdem ρ c` (a multiple of `∑ x, star ((labelChar T c).evalGL x) • x`, with
`T` as below; it is zero unless `c` is a label of degree `card ρ`). Let `f` have a parahoric type
with distinct `χ l`: `b` cuts `n` into blocks `0, …, s` and `e` numbers block `0`. An integral `k`
whose reduction is block triangular with block `0` equal to `x` sends `f` to
`∏ l, χ l (det k_(l+1))` times `ψ (det x)` times `L (σ x y)`. Let `T` be
`faithfulChar (ResField w)`, a chosen faithful character of the algebraic closure of `ResField w`
and `a` be `c` with its roots scaled by `charName T ψ`. If no `charName T (χ l)` is a root of `a`,
then `f` has the label `labelChar T a * ∏ l, (χ l ∘ det)` of degree `card ρ`, with blocks `l + 1`
(`New.HasProductLabel`). -/
lemma HasParahoricType.hasProductLabel {f : Gf E n → M → ℂ} {hw : w.IsSplit} {e : ρ ↪ n} {y : V}
    {b : n → Fin (s + 1)} {c : (ResField w)[X]} {ψ : MulChar (ResField w) ℂ}
    {χ : Fin s → MulChar (ResField w) ℂ} (L : V →ₗ[ℂ] Gf E n → M → ℂ) (hL : Injective L)
    (h_idem : σ.asAlgebraHom (labelIdem ρ c) y ≠ 0)
    (h_type : HasParahoricType f hw e b ψ χ fun x : GL ρ (ResField w) ↦ L (σ x y))
    (hχ : Injective χ) :
    let T : MulChar (AlgebraicClosure (ResField w)) ℂ := faithfulChar (ResField w)
    let a : (ResField w)[X] := c.scaleRoots (charName T ψ)
    (h_root : ∀ l : Fin s, ¬a.IsRoot (charName T (χ l)).val) →
    HasProductLabel f hw T (Fintype.card ρ) a χ fun l : Fin s ↦
      Fintype.card {i // b i = l.succ} := by
  -- Frobenius reciprocity (`sum_evalGL_prod_eq_zero_iff`) turns the sum over `GL n` against the
  -- induced character into a sum over the parabolic subgroup. There the characters `χ l` cancel and
  -- `ψ` undoes the scaling of `c`; what is left is, through `L`, the idempotent of `c` applied to
  -- `y`.
  intro T a h_root
  obtain ⟨h_block, h_act⟩ := h_type
  have hc : IsLabel (card ρ) c := by
    by_contra hc
    simp [labelIdem, hc] at h_idem
  have ha : IsLabel (card ρ) a := hc.scaleRoots _
  have ha_sqfree : Squarefree a := by
    obtain ⟨-, h_sqfree, -⟩ := ha
    exact h_sqfree
  let ε : {i // b i = 0} ≃ ρ := (Equiv.subtypeEquivRight h_block).trans e.toEquivRange.symm
  let π : parabolic b →* GL ρ (ResField w) := (reindexGL ε).toMonoidHom.comp (blockHom b 0)
  have h_par (k : intGL n Valued.v.integer) (hk : reduceGL k ∈ parabolic b) :
      rightRegular ℂ (Gf E n) (M → ℂ) (ofSplitPlace hw k.val) f =
        (∏ l, χ l (blockHom b l.succ ⟨reduceGL k, hk⟩).det.val) •
          ψ (π ⟨reduceGL k, hk⟩).det.val • L (σ (π ⟨reduceGL k, hk⟩) y) :=
    h_act k (π ⟨reduceGL k, hk⟩) hk rfl
  -- A matrix with trivial reduction acts as the identity matrix does.
  have h_ker (k : intGL n Valued.v.integer) (hk : reduceGL k = 1) :
      rightRegular ℂ (Gf E n) (M → ℂ) (ofSplitPlace hw k.val) f = f := by
    -- by `h_par`, the translate of `f` by `k` depends only on its reduction `1`, so it equals the
    -- translate by `1`, which is `f`.
    simpa [hk, h_par k (by simp [hk])] using (h_par 1 (by simp)).symm
  refine ⟨ha, ?_, ?_, h_ker, fun h_zero ↦ h_idem (hL ?_)⟩
  · -- `a` is squarefree, the `charName T (χ l)` are distinct, and none of them is a root of `a`.
    have h_inj : Injective fun l : Fin s ↦ (charName T (χ l)).val :=
      Units.val_injective.comp ((charName T).injective.comp hχ)
    exact separable_mul_prod_X_sub_C_of_squarefree ha_sqfree h_inj h_root
  · simp [← card_congr (.sigmaFiberEquiv b), sum_univ_succ, card_congr ε]
  -- On `f` the action of integral matrices factors through `GL n (ResField w)`.
  let τ : GL n (ResField w) → intGL n Valued.v.integer := surjInv reduceGL_surjective
  let A (g : GL n (ResField w)) : (Gf E n → M → ℂ) →ₗ[ℂ] Gf E n → M → ℂ :=
    rightRegular ℂ (Gf E n) (M → ℂ) (ofSplitPlace hw (τ g).val)
  have h_mul (g x : GL n (ResField w)) : A g (A x f) = A (g * x) f := by
    simpa [A, Representation.inv_apply_eq_iff] using
      h_ker ((τ (g * x))⁻¹ * τ g * τ x) (by simp [τ, surjInv_eq])
  -- `Ξ i` is the class function on block `i`.
  let Ξ : Fin (s + 1) → Hall (ResField w) := cons (labelChar T a) fun l ↦ detChar (χ l)
  -- The hypothesis `h_zero`, with the class function written block by block: block `0`, of size
  -- `card ρ`, carries `labelChar T a`, and block `l + 1` carries `detChar (χ l)`.
  have h_blocks : ∑ᶠ g : GL n (ResField w),
      star ((∏ i : Fin (s + 1), (Ξ i).rankPart (card {j // b j = i})).evalGL g) • A g f = 0 := by
    simpa [Ξ, prod_univ_succ, card_congr ε, rankPart_labelChar T ha] using h_zero
  -- Frobenius reciprocity, at the translate by `1`.
  have h_sum : ∑ᶠ p : parabolic b, star (∏ i, (Ξ i).evalGL (blockHom b i p)) • A (p * 1) f = 0 :=
    (sum_evalGL_prod_eq_zero_iff b (F := Ξ)
        (cases (lift_labelChar_self T ha) fun _ ↦ lift_detChar T rfl) A h_mul).mp h_blocks 1
  have h_A (p : parabolic b) : A p f =
      (∏ l, χ l (blockHom b l.succ p).det.val) • ψ (π p).det.val • L (σ (π p) y) := by
    simpa [τ, surjInv_eq] using h_par (τ p) (by simp [τ, surjInv_eq])
  -- Evaluate at a point `(g, m)`.
  ext g m
  let Φ (x : GL ρ (ResField w)) : ℂ := star ((labelChar T c).evalGL x) * L (σ x y) g m
  have h_ev (p : parabolic b) :
      (labelChar T c).evalGL (blockHom b 0 p) = (labelChar T c).evalGL (π p) :=
    congrArg (labelChar T c) (simClassOf_submatrix ε.symm (blockHom b 0 p).val).symm
  have h_det_ne {ι : Type} [Fintype ι] [DecidableEq ι] (φ : MulChar (ResField w) ℂ)
      (u : GL ι (ResField w)) : φ u.val.det ≠ 0 := ((isUnits_det_units u).map φ).ne_zero
  -- Term by term: by `h_A` the factors `star (χ l _) * χ l _` are `1`, and `labelChar T a` is
  -- `labelChar T c` times `ψ ∘ det` (`evalGL_labelChar_mul_det`), so `star (ψ _) * ψ _` is `1` as
  -- well.
  have h_term (p : parabolic b) :
      (star (∏ i, (Ξ i).evalGL (blockHom b i p)) • A (p * 1) f) g m = Φ (π p) := by
    simp [Φ, π, Ξ, a, h_A, h_ev, prod_univ_succ, mul_assoc, star_apply', h_det_ne,
      inv_apply_eq_inv', prod_ne_zero_iff, ← evalGL_labelChar_mul_det hc]
  have h_par_sum : ∑ᶠ p, Φ (π p) = 0 := by
    simpa [finsum_eq_sum_of_fintype, ← h_term, Finset.sum_apply] using congrFun₂ h_sum g m
  -- The projection `π` to the block `0` is onto, so the two averages agree.
  have h_mean : finMean Φ = finMean fun p : parabolic b ↦ Φ (π p) :=
    (finMean_comp_surjective π.toAdditive (surjective_reindexGL_comp_blockHom_zero h_block) Φ).symm
  have h_sum_Φ : ∑ x : GL ρ (ResField w), Φ x = 0 := by
    rw [finMean, finMean, h_par_sum] at h_mean
    simpa [finsum_eq_sum_of_fintype] using h_mean
  -- `L` of the idempotent applied to `y` is, at `(g, m)`, a multiple of the sum of `Φ`, which
  -- vanishes.
  suffices h_or : (labelChar T c).evalGL 1 = 0 ∨
      ∑ x : GL ρ (ResField w), starRingEnd ℂ ((labelChar T c).evalGL x) * L (σ x y) g m = 0 by
    simpa [T, labelIdem, hc, asAlgebraHom_eq_sum, mul_assoc, ← mul_sum] using h_or
  exact .inr h_sum_Φ

end ParahoricTypeLabel

end New
